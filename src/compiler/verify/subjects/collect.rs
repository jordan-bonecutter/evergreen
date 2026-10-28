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
            Kind::Field(base, field)
                if array_values::indexed_base(expression).is_some()
                    && self
                        .locals
                        .logical_bindings
                        .iter()
                        .any(|binding| binding.quantified) =>
            {
                // The bound index is a logical argument, not a concrete memory
                // projection. Retain the entire array revision and field path.
                self.collect_subjects(base, snapshot, depth + 1)?
                    .map(|base| ClaimKey::Unary(format!("field:{field}"), Box::new(base)))
            }
            Kind::Index(base, index)
                if self
                    .locals
                    .logical_bindings
                    .iter()
                    .any(|binding| binding.quantified) =>
            {
                let base = self.collect_subjects(base, snapshot, depth + 1)?;
                let index = self.collect_subjects(index, snapshot, depth + 1)?;
                base.zip(index).map(|(base, index)| {
                    ClaimKey::Binary("index".into(), Box::new(base), Box::new(index))
                })
            }
            Kind::Call(name, arguments)
                if name == "typeof"
                    && arguments.len() == 1
                    && self
                        .locals
                        .logical_bindings
                        .iter()
                        .any(|binding| binding.quantified)
                    && matches!(arguments[0].kind, Kind::Index(..)) =>
            {
                let Kind::Index(base, index) = &arguments[0].kind else {
                    return Ok(None);
                };
                let base = self.collect_subjects(base, snapshot, depth + 1)?;
                let index = self.collect_subjects(index, snapshot, depth + 1)?;
                base.zip(index).map(|(base, index)| {
                    ClaimKey::Unary(
                        name.clone(),
                        Box::new(ClaimKey::Binary(
                            "index".into(),
                            Box::new(base),
                            Box::new(index),
                        )),
                    )
                })
            }
            Kind::Forall {
                variable,
                domain,
                body,
            } => {
                let name = self.quantified_name();
                self.with_logical_binding(variable, &name, true, |ctx| {
                    let domain = ctx.collect_subjects(domain, snapshot, depth + 1)?;
                    let body = ctx.collect_subjects(body, snapshot, depth + 1)?;
                    Ok(domain
                        .zip(body)
                        .map(|(a, b)| ClaimKey::Forall(Box::new(a), Box::new(b))))
                })?
            }
            Kind::Name(name) if self.logical_key(name).is_some() => self.logical_key(name),
            Kind::Type(_) => self.type_literal(expression).map(ClaimKey::Type),
            Kind::Generic { .. } => {
                return Err("unlowered generic expression reached proof-state collection".into())
            }
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
            Kind::Call(name, arguments) if name == "owner_count" && arguments.len() == 1 => {
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
                                Some(Symbol::Unique(_, reference)) => Some((reference, vec![])),
                                Some(Symbol::Shared(_, owner)) => Some((owner.reference(), vec![])),
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
            Kind::Call(name, _) if matches!(name.as_str(), "shape" | "unique" | "shared") => {
                self.type_literal(expression).map(ClaimKey::Type)
            }
            Kind::Call(name, arguments)
                if self
                    .declarations
                    .functions
                    .get(name)
                    .is_some_and(|function| self.is_verified_scalar_definition(function)) =>
            {
                // A pure scalar definition observes only these values. Keep its
                // identity and every argument revision without evaluating it.
                let mut keys = Vec::new();
                let mut complete = true;
                for argument in arguments {
                    match self.collect_subjects(argument, snapshot, depth + 1)? {
                        Some(key) => keys.push(key),
                        None => complete = false,
                    }
                }
                complete.then_some(ClaimKey::Call(name.clone(), keys))
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
            Kind::Block(..) => None,
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
            let Some(cases) = self.subject_cases(expression, depth + 1)? else {
                return Ok(None);
            };
            let mut keys = Vec::new();
            for case in cases {
                if self.checked_entails(&case.guard.clone().not())? {
                    continue;
                }
                let stamp =
                    self.proof
                        .subjects
                        .observe(&self.storage.memory, case.reference, case.path)?;
                keys.push((case.guard, ClaimKey::Read(stamp)));
            }
            if let [(guard, key)] = keys.as_slice() {
                if self.checked_entails(guard)? {
                    return Ok(Some(key.clone()));
                }
            }
            Ok((!keys.is_empty()).then_some(ClaimKey::Guarded(keys)))
        }
    }
}
