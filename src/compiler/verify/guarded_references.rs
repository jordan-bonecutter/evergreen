//! A selected reference retains real plane identities and frozen mathematical
//! guards. Runtime representation is still one pointer; guards are proof data.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Case {
    pub(super) guard: Formula,
    pub(super) reference: Reference,
    pub(super) path: Vec<Projection<Linear>>,
}

pub(super) type ReadKey = (Ty, Vec<(Formula, subjects::Stamp)>);

pub(super) fn cases(value: &Symbol) -> Result<Vec<Case>> {
    match value {
        Symbol::Ref(_, reference, path) => Ok(vec![Case {
            guard: Formula::True,
            reference: *reference,
            path: path.clone(),
        }]),
        Symbol::RefCases(_, cases) => Ok(cases.clone()),
        _ => Err("expected a non-owning reference".into()),
    }
}

pub(super) fn identity_equal(a: &Symbol, b: &Symbol) -> Result<Formula> {
    if a == b {
        return Ok(Formula::True);
    };
    let a = cases(a)?;
    let b = cases(b)?;
    let mut targets: BTreeMap<Reference, Vec<&Case>> = BTreeMap::new();
    for case in &b {
        targets.entry(case.reference).or_default().push(case);
    }
    let mut relation = Formula::False;
    let mut work = 0usize;
    for a in &a {
        for b in targets.get(&a.reference).into_iter().flatten() {
            work = work.saturating_add(
                1 + a.path.len()
                    + b.path.len()
                    + a.guard.storage_weight()?
                    + b.guard.storage_weight()?,
            );
            if work > MAX_VALUE_WORK {
                return Err("conditional reference identity work limit reached".into());
            };
            if a.path.len() != b.path.len() {
                continue;
            }
            let same = paths_equal(&a.path, &b.path)?;
            relation = relation.or(a.guard.clone().and(b.guard.clone()).and(same));
        }
    }
    Ok(relation)
}

pub(super) fn paths_equal(a: &[Projection<Linear>], b: &[Projection<Linear>]) -> Result<Formula> {
    if a.len() != b.len() {
        return Ok(Formula::False);
    };
    let mut same = Formula::True;
    for (a, b) in a.iter().zip(b) {
        same = same.and(match (a, b) {
            (Projection::Field(a), Projection::Field(b)) if a == b => Formula::True,
            (Projection::Index(a), Projection::Index(b)) => equal(a, b)?,
            (
                Projection::Member {
                    index: a,
                    expected: at,
                },
                Projection::Member {
                    index: b,
                    expected: bt,
                },
            ) if a == b && at == bt => Formula::True,
            _ => Formula::False,
        });
    }
    Ok(same)
}

impl Context<'_> {
    pub(super) fn incoming_borrow(
        &mut self,
        expression: &Expr,
        inputs: &[InputReference],
    ) -> Result<Symbol> {
        if let Kind::If(condition, yes, no) = &expression.kind {
            let guard = self.eval(condition, Some(&Ty::Bool))?.proposition()?;
            return self.eval_guarded(
                guard,
                None,
                expression.line,
                |context, _| context.incoming_borrow(yes, inputs),
                |context, _| context.incoming_borrow(no, inputs),
            );
        }
        let origin = input_reference_origin(expression)
            .ok_or("borrow must project an incoming reference")?;
        let value = self.eval(expression, None)?;
        for case in cases(&value)? {
            self.charge_value_work(inputs.len() + case.path.len() + case.guard.storage_weight()?)?;
            let mut available = Formula::False;
            for input in inputs.iter().filter(|input| {
                input.origin.as_ref() == Some(&origin)
                    && input.reference == case.reference
                    && input.path.len() <= case.path.len()
            }) {
                available = available.or(input
                    .guard
                    .clone()
                    .and(paths_equal(&input.path, &case.path[..input.path.len()])?));
            }
            if !self.checked_entails(&case.guard.not().or(available))? {
                return Err("borrow must refer to incoming caller storage, not a local parameter slot or another port".into());
            }
        }
        Ok(value)
    }

    pub(super) fn direct_reference(
        &mut self,
        value: &Symbol,
    ) -> Result<(Reference, Vec<Projection<Linear>>)> {
        for case in cases(value)? {
            if self.checked_entails(&case.guard)? {
                self.storage.memory.read(case.reference)?;
                return Ok((case.reference, case.path));
            }
        }
        Err("this reference selects between planes; the operation needs a guarded place".into())
    }

    pub(super) fn dereference(&mut self, pointer: &Expr, line: usize) -> Result<Symbol> {
        let value = self.pointer_operand(pointer)?;
        match &value {
            Symbol::Ref(..) | Symbol::RefCases(..) => self.read_reference(&value, line),
            Symbol::Unique(_, reference) => self.read_projection_value(*reference, &[], line),
            Symbol::Shared(_, owner) => {
                let reference = self.storage.memory.borrow_owned(*owner)?;
                self.read_projection_value(reference, &[], line)
            }
            _ => Err("dereference requires a reference or owning pointer".into()),
        }
    }
    pub(super) fn reference_view(&mut self, ty: Box<Ty>, cases: Vec<Case>) -> Result<Symbol> {
        let mut targets: BTreeMap<(Reference, Vec<Projection<Linear>>), Formula> = BTreeMap::new();
        for case in cases {
            self.charge_value_work(
                case.guard
                    .storage_weight()?
                    .saturating_add(case.path.len() + 1),
            )?;
            if case.guard == Formula::False {
                continue;
            }
            let guard = targets
                .entry((case.reference, case.path))
                .or_insert(Formula::False);
            *guard = guard.clone().or(case.guard);
        }
        let mut coverage = Formula::False;
        let cases = targets
            .into_iter()
            .map(|((reference, path), guard)| {
                coverage = coverage.clone().or(guard.clone());
                Case {
                    guard,
                    reference,
                    path,
                }
            })
            .collect::<Vec<_>>();
        if !self.checked_entails(&coverage)? {
            return Err(
                "conditional reference alternatives do not cover the current execution".into(),
            );
        }
        if let [case] = cases.as_slice() {
            Ok(Symbol::Ref(ty, case.reference, case.path.clone()))
        } else {
            Ok(Symbol::RefCases(ty, cases))
        }
    }

    pub(super) fn join_references(
        &mut self,
        a: &Symbol,
        b: &Symbol,
        line: usize,
    ) -> Result<(Symbol, Formula, Formula)> {
        let Ty::Ref(ty) = a.ty() else {
            return Err("conditional reference requires a reference type".into());
        };
        self.compatible(&b.ty(), &Ty::Ref(ty.clone()), line)?;
        let guard = self.arbitrary(&Ty::Bool)?.proposition()?;
        let mut selected = cases(a)?;
        for case in &mut selected {
            case.guard = guard.clone().and(case.guard.clone());
        }
        for mut case in cases(b)? {
            case.guard = guard.clone().not().and(case.guard);
            selected.push(case);
        }
        Ok((
            self.reference_view(ty, selected)?,
            guard.clone(),
            guard.not(),
        ))
    }

    pub(super) fn read_reference(&mut self, value: &Symbol, line: usize) -> Result<Symbol> {
        let Ty::Ref(ty) = value.ty() else {
            return Err("read requires a reference".into());
        };
        if let Symbol::Ref(_, reference, path) = value {
            return self.read_projection_value(*reference, path, line);
        }
        let mut reachable = Vec::new();
        for case in cases(value)? {
            if self.checked_entails(&case.guard)? {
                return self.read_projection_value(case.reference, &case.path, line);
            }
            if !self.checked_entails(&case.guard.clone().not())? {
                reachable.push(case);
            }
        }
        if self.history_element(&ty) || matches!(*ty, Ty::Ref(_)) {
            return self.read_reference_values(&reachable, &ty, line);
        }
        self.read_reference_cases(&reachable, &ty, line)
    }

    fn read_reference_values(&mut self, cases: &[Case], ty: &Ty, line: usize) -> Result<Symbol> {
        let mut stamps = Vec::new();
        for case in cases {
            stamps.push((
                case.guard.clone(),
                self.proof.subjects.observe(
                    &self.storage.memory,
                    case.reference,
                    case.path.clone(),
                )?,
            ));
        }
        let key = (ty.clone(), stamps);
        let base = self.proof.paths.clone();
        let mut paths = paths::Paths::from(Vec::new());
        paths.closed = base.closed.clone();
        let mut observed = Vec::new();
        for case in cases {
            self.proof.paths = extend(
                &base,
                &case.guard,
                false,
                self.session,
                &mut self.work.value_work,
            )?;
            let value = self.read_projection_value(case.reference, &case.path, line);
            paths.extend(self.proof.paths.clone());
            self.proof.paths = base.clone();
            observed.push((case, value?));
        }
        self.proof.paths = paths::bounded(paths, self.session, &mut self.work.value_work)?;
        if let Ty::Ref(element) = ty {
            let mut selected = Vec::new();
            for (parent, value) in observed {
                for mut case in self::cases(&value)? {
                    case.guard = parent.guard.clone().and(case.guard);
                    selected.push(case);
                }
            }
            return self.reference_view(element.clone(), selected);
        }
        let value = if let Some(value) = self.storage.reference_reads.get(&key).cloned() {
            self.assume_history_type(&value, false)?;
            value
        } else {
            let value = self.history_value(ty)?;
            self.storage.reference_reads.insert(key, value.clone());
            value
        };
        let mut relation = Formula::False;
        for (case, observed) in observed {
            relation = relation.or(case
                .guard
                .clone()
                .and(self.symbol_equal(&value, &observed)?));
        }
        self.assume(&relation)?;
        Ok(value)
    }

    fn read_reference_cases(&mut self, cases: &[Case], ty: &Ty, line: usize) -> Result<Symbol> {
        let Some((first, remaining)) = cases.split_first() else {
            return Err("conditional reference has no reachable target".into());
        };
        if self.checked_entails(&first.guard)? {
            return self.read_projection_value(first.reference, &first.path, line);
        }
        if self.checked_entails(&first.guard.clone().not())? {
            return self.read_reference_cases(remaining, ty, line);
        }
        if remaining.is_empty() {
            return Err("conditional reference target is not established".into());
        }
        self.eval_guarded(
            first.guard.clone(),
            Some(ty),
            line,
            |context, _| context.read_projection_value(first.reference, &first.path, line),
            |context, _| context.read_reference_cases(remaining, ty, line),
        )
    }
}
