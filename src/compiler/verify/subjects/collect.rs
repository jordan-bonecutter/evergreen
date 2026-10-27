//! Capture proof reads without evaluating source expressions a second time.

use super::*;

impl Context<'_> {
    pub(in crate::compiler::verify) fn claim_subjects(
        &mut self,
        expression: &Expr,
    ) -> Result<Snapshot> {
        let mut snapshot = Snapshot::default();
        snapshot.key = self.collect_subjects(expression, &mut snapshot, 0)?;
        if let Some(key) = snapshot.key.take() {
            snapshot = Snapshot::from_key(key);
        }
        Ok(snapshot)
    }

    fn collect_subjects(
        &mut self,
        expression: &Expr,
        snapshot: &mut Snapshot,
        depth: usize,
    ) -> Result<Option<ClaimKey>> {
        self.charge_value_work(1)?;
        if depth >= 32 {
            return Ok(None);
        }
        let key = match &expression.kind {
            Kind::Bytes(bytes) => Some(ClaimKey::Array(
                bytes
                    .iter()
                    .map(|&byte| ClaimKey::Number(i128::from(byte)))
                    .collect(),
            )),
            Kind::Name(name) if !self.locals.values.contains_key(name) => {
                if let Some(fact) = self.proof.facts.get(name).cloned() {
                    return self.collect_subjects(&fact, snapshot, depth + 1);
                }
                self.type_literal(expression).map(ClaimKey::Type)
            }
            Kind::Name(_) | Kind::Field(..) | Kind::Index(..) => {
                return self.collect_place_subject(expression, snapshot, depth + 1);
            }
            Kind::Unary(op, place) if op == "&" => self
                .collect_place_subject(place, snapshot, depth + 1)?
                .map(|key| ClaimKey::Unary(op.clone(), Box::new(key))),
            Kind::Unary(op, _) if op == "*" => {
                return self.collect_place_subject(expression, snapshot, depth + 1);
            }
            Kind::Binary(op, a, b) => {
                let a = self.collect_subjects(a, snapshot, depth + 1)?;
                let b = self.collect_subjects(b, snapshot, depth + 1)?;
                a.zip(b)
                    .map(|(a, b)| ClaimKey::Binary(op.clone(), Box::new(a), Box::new(b)))
            }
            Kind::Unary(op, value) => self
                .collect_subjects(value, snapshot, depth + 1)?
                .map(|key| ClaimKey::Unary(op.clone(), Box::new(key))),
            Kind::Array(items) => {
                let mut keys = Vec::new();
                let mut complete = true;
                for item in items {
                    if let Some(key) = self.collect_subjects(item, snapshot, depth + 1)? {
                        keys.push(key);
                    } else {
                        complete = false;
                    }
                }
                complete.then_some(ClaimKey::Array(keys))
            }
            Kind::Record(name, fields) => {
                let mut keys = Vec::new();
                let mut complete = true;
                for (field, value) in fields {
                    if let Some(key) = self.collect_subjects(value, snapshot, depth + 1)? {
                        keys.push((field.clone(), key));
                    } else {
                        complete = false;
                    }
                }
                complete.then_some(ClaimKey::Record(name.clone(), keys))
            }
            Kind::Call(name, arguments) if name == "owners" && arguments.len() == 1 => {
                if let Some(reference) = self.owner_subject_reference(&arguments[0]) {
                    let stamp = self.proof.subjects.observe(
                        &self.storage.memory,
                        reference,
                        ownership::census_path(),
                    )?;
                    Some(ClaimKey::Unary(
                        name.clone(),
                        Box::new(ClaimKey::Read(stamp)),
                    ))
                } else {
                    None
                }
            }
            Kind::Call(name, arguments) if name == "old" && arguments.len() == 1 => {
                if let Kind::Unary(op, base) = &arguments[0].kind {
                    if op == "*" {
                        if let Some(name) = Self::old_key(base) {
                            let value = self.entry.values.get(&name).cloned();
                            let place = match value {
                                Some(Symbol::Ref(_, reference, path)) => Some((reference, path)),
                                Some(Symbol::Plane(_, reference)) => Some((reference, vec![])),
                                Some(Symbol::Owner(_, owner)) => Some((owner.reference(), vec![])),
                                _ => None,
                            };
                            if let Some((reference, path)) = place {
                                let stamp = self.proof.subjects.old_read(
                                    self.entry.world,
                                    reference,
                                    path,
                                )?;
                                return Ok(Some(ClaimKey::OldRead(self.entry.world, stamp)));
                            }
                        }
                    }
                }
                Self::old_key(&arguments[0])
                    .filter(|key| self.entry.values.contains_key(key))
                    .map(|key| ClaimKey::Entry(self.entry.world, key))
            }
            Kind::Call(name, arguments)
                if arguments.len() == 1
                    && (matches!(name.as_str(), "integer" | "nat" | "typeof")
                        || MachineInt::parse(name).is_some()) =>
            {
                self.collect_subjects(&arguments[0], snapshot, depth + 1)?
                    .map(|key| ClaimKey::Unary(name.clone(), Box::new(key)))
            }
            Kind::Call(name, _) if name == "shape" => {
                self.type_literal(expression).map(ClaimKey::Type)
            }
            Kind::Call(_, arguments) => {
                // Call-result subjects need value-flow provenance through
                // parameter renaming. Never re-evaluate a call to discover it.
                for argument in arguments {
                    self.collect_subjects(argument, snapshot, depth + 1)?;
                }
                None
            }
            Kind::If(condition, _, _) | Kind::FactAt(condition, _) => {
                self.collect_subjects(condition, snapshot, depth + 1)?;
                None
            }
            Kind::Unit => Some(ClaimKey::Unit),
            Kind::Number(n) | Kind::Constant(_, n) => Some(ClaimKey::Number(*n)),
            Kind::Bool(b) => Some(ClaimKey::Bool(*b)),
        };
        Ok(key)
    }

    fn collect_place_subject(
        &mut self,
        expression: &Expr,
        snapshot: &mut Snapshot,
        depth: usize,
    ) -> Result<Option<ClaimKey>> {
        if let Some((reference, path)) = self.subject_place(expression, depth)? {
            self.charge_value_work(1usize.saturating_add(path.len()))?;
            let stamp = self
                .proof
                .subjects
                .observe(&self.storage.memory, reference, path)?;
            snapshot.reads.insert(stamp);
            Ok(Some(ClaimKey::Read(stamp)))
        } else {
            Ok(None)
        }
    }

    /// Resolve only existing storage and simple index values. This deliberately
    /// does not call `eval`, user functions, or expression elaboration twice.
    fn subject_place(
        &mut self,
        expression: &Expr,
        depth: usize,
    ) -> Result<Option<(Reference, Vec<Projection<Linear>>)>> {
        self.charge_value_work(1)?;
        if depth >= 32 {
            return Ok(None);
        }
        match &expression.kind {
            Kind::Name(name) => {
                let plane = if let Some(&plane) = self.locals.places.get(name) {
                    plane
                } else if let Some(value) = self.locals.values.get(name).cloned() {
                    let plane = self.allocate_symbol(value)?;
                    self.locals.places.insert(name.clone(), plane);
                    plane
                } else {
                    return Ok(None);
                };
                Ok(self
                    .storage
                    .memory
                    .borrow(plane)
                    .ok()
                    .map(|reference| (reference, vec![])))
            }
            Kind::Field(base, field) => {
                let Some((reference, mut path)) = self.subject_place(base, depth + 1)? else {
                    return Ok(None);
                };
                path.push(Projection::Field(field.clone()));
                Ok(Some((reference, path)))
            }
            Kind::Index(base, index) => {
                let Some((reference, mut path)) = self.subject_place(base, depth + 1)? else {
                    return Ok(None);
                };
                let index = match &index.kind {
                    Kind::Number(n) | Kind::Constant(_, n) => Some(Linear::number(*n)),
                    Kind::Name(name) => {
                        let value = self
                            .locals
                            .places
                            .get(name)
                            .and_then(|&id| self.storage.memory.get(id).ok())
                            .or_else(|| self.locals.values.get(name));
                        match value {
                            Some(Symbol::Number(_, number)) => Some(number.clone()),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let Some(index) = index else {
                    return Ok(None);
                };
                path.push(Projection::Index(index));
                Ok(Some((reference, path)))
            }
            Kind::Unary(op, base) if op == "*" => {
                // *old(p) freezes the pointer identity, not the pointee. The
                // resulting place is observed against the LIVE plane state.
                if let Kind::Call(name, arguments) = &base.kind {
                    if name == "old" && arguments.len() == 1 {
                        let old = Self::old_key(&arguments[0])
                            .and_then(|key| self.entry.values.get(&key));
                        return Ok(match old {
                            Some(Symbol::Ref(_, reference, path)) => {
                                Some((*reference, path.clone()))
                            }
                            Some(Symbol::Plane(_, reference)) => Some((*reference, vec![])),
                            Some(Symbol::Owner(_, owner)) => Some((owner.reference(), vec![])),
                            _ => None,
                        });
                    }
                }
                let Some((reference, path)) = self.subject_place(base, depth + 1)? else {
                    return Ok(None);
                };
                let value = self
                    .storage
                    .memory
                    .read(reference)
                    .ok()
                    .and_then(|value| self.observed_projection(value, &path));
                // Resolve identity without elaborating a second read. The
                // operational dereference separately proves this member active.
                let pointer = match value {
                    Some(Symbol::Union {
                        members, payloads, ..
                    }) => {
                        let ty = Ty::Union(members.clone());
                        ty.pointer_member()
                            .and_then(|pointer| members.iter().position(|ty| ty == pointer))
                            .and_then(|index| payloads[index].as_ref())
                    }
                    other => other,
                };
                match pointer {
                    Some(Symbol::Owner(_, owner)) => {
                        Ok(Some((self.storage.memory.borrow_owned(*owner)?, vec![])))
                    }
                    Some(Symbol::Ref(_, reference, path)) => Ok(Some((*reference, path.clone()))),
                    Some(Symbol::Plane(_, reference)) => Ok(Some((*reference, vec![]))),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }
}
