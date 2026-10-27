//! Resolve existing guarded storage for proof subjects without executing expressions.

use super::*;

impl Context<'_> {
    pub(super) fn subject_cases(
        &mut self,
        expression: &Expr,
        depth: usize,
    ) -> Result<Option<Vec<guarded_references::Case>>> {
        self.charge_value_work(1)?;
        if depth >= 32 {
            return Ok(None);
        };
        if let Some((reference, path)) = self.subject_place(expression, depth + 1)? {
            return Ok(Some(vec![guarded_references::Case {
                guard: Formula::True,
                reference,
                path,
            }]));
        }
        match &expression.kind {
            Kind::Field(base, name) => {
                let Some(mut cases) = self.subject_cases(base, depth + 1)? else {
                    return Ok(None);
                };
                for case in &mut cases {
                    case.path.push(Projection::Field(name.clone()));
                }
                Ok(Some(cases))
            }
            Kind::Index(base, index) => {
                let index = match &index.kind {
                    Kind::Number(n) | Kind::Constant(_, n) => Linear::number(*n),
                    Kind::Name(name) => {
                        let value = self
                            .locals
                            .places
                            .get(name)
                            .and_then(|plane| self.storage.memory.get(*plane).ok())
                            .or_else(|| self.locals.values.get(name));
                        let Some(Symbol::Number(_, n)) = value else {
                            return Ok(None);
                        };
                        n.clone()
                    }
                    _ => return Ok(None),
                };
                let Some(mut cases) = self.subject_cases(base, depth + 1)? else {
                    return Ok(None);
                };
                for case in &mut cases {
                    case.path.push(Projection::Index(index.clone()));
                }
                Ok(Some(cases))
            }
            Kind::Unary(op, base) if op == "*" => {
                if let Kind::Call(name, args) = &base.kind {
                    if name == "old" && args.len() == 1 {
                        return Self::old_key(&args[0])
                            .and_then(|key| self.entry.values.get(&key))
                            .map(guarded_references::cases)
                            .transpose();
                    }
                }
                let Some(headers) = self.subject_cases(base, depth + 1)? else {
                    return Ok(None);
                };
                let mut targets = Vec::new();
                for header in headers {
                    let value = self
                        .storage
                        .memory
                        .read(header.reference)
                        .ok()
                        .and_then(|value| self.observed_projection(value, &header.path));
                    let Some(value) = value else { return Ok(None) };
                    let selected = match value {
                        Symbol::Ref(..) | Symbol::RefCases(..) => guarded_references::cases(value)?,
                        Symbol::Plane(_, reference) => vec![guarded_references::Case {
                            guard: Formula::True,
                            reference: *reference,
                            path: vec![],
                        }],
                        Symbol::Owner(_, owner) => vec![guarded_references::Case {
                            guard: Formula::True,
                            reference: self.storage.memory.borrow_owned(*owner)?,
                            path: vec![],
                        }],
                        _ => return Ok(None),
                    };
                    targets.extend(selected.into_iter().map(|mut case| {
                        case.guard = header.guard.clone().and(case.guard);
                        case
                    }));
                }
                Ok(Some(targets))
            }
            _ => Ok(None),
        }
    }

    /// Resolve only existing storage and simple index values. This deliberately
    /// does not call `eval`, user functions, or expression elaboration twice.
    pub(super) fn subject_place(
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
