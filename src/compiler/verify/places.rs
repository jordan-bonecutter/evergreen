//! Guarded places retain actual storage paths. Address components and assigned
//! values are evaluated once, before dispatching their conditional effects.

use super::*;
use guarded_references::Case;

pub(super) fn through_pointer(expression: &Expr) -> bool {
    match &expression.kind {
        Kind::Unary(op, _) if op == "*" => true,
        Kind::Field(base, _) | Kind::Index(base, _) => through_pointer(base),
        _ => false,
    }
}

impl Context<'_> {
    pub(super) fn on_reference_places(
        &mut self,
        cases: &[Case],
        expected: Option<&Ty>,
        line: usize,
        action: &impl Fn(&mut Self, &Case) -> Result<Symbol>,
    ) -> Result<Symbol> {
        let mut reachable = Vec::new();
        for case in cases {
            self.charge_value_work(1 + case.path.len() + case.guard.storage_weight()?)?;
            if self.checked_entails(&case.guard)? {
                return action(self, case);
            }
            if !self.checked_entails(&case.guard.clone().not())? {
                reachable.push(case.clone());
            }
        }
        if reachable.len() < 2 {
            return Err("conditional place target is not established".into());
        }
        // Balance alternatives rather than building a Rust call stack linear
        // in the number of possible targets. Unobserved array elements never
        // enter this list.
        let (left, right) = reachable.split_at(reachable.len() / 2);
        let guard = left
            .iter()
            .fold(Formula::False, |guard, case| guard.or(case.guard.clone()));
        self.eval_guarded(
            guard,
            expected,
            line,
            |ctx, hint| ctx.on_reference_places(left, hint, line, action),
            |ctx, hint| ctx.on_reference_places(right, hint, line, action),
        )
    }

    pub(super) fn place_reference(&mut self, expression: &Expr) -> Result<Symbol> {
        match &expression.kind {
            Kind::Unary(op, pointer) if op == "*" => {
                let value = match self.pointer_operand(pointer)? {
                    value @ (Symbol::Ref(..) | Symbol::RefCases(..)) => value,
                    Symbol::Unique(ty, reference) => Symbol::Ref(ty, reference, vec![]),
                    Symbol::Shared(ty, owner) => {
                        Symbol::Ref(ty, self.storage.memory.borrow_owned(owner)?, vec![])
                    }
                    _ => return Err("dereference requires a live pointer".into()),
                };
                self.validate_reference_addresses(&value)?;
                Ok(value)
            }
            Kind::Field(base, name) => {
                let base = self.place_reference(base)?;
                self.on_reference_places(
                    &guarded_references::cases(&base)?,
                    None,
                    expression.line,
                    &|ctx, case| {
                        ctx.validate_member_path(case.reference, &case.path, expression.line)?;
                        let root = ctx.storage.memory.read(case.reference)?;
                        let Symbol::Record(typename, _) = project(root, &case.path)? else {
                            return Err("field reference requires a record".into());
                        };
                        ctx.field_access(typename, name, expression.line)?;
                        let mut path = case.path.clone();
                        path.push(Projection::Field(name.clone()));
                        let ty = project(ctx.storage.memory.read(case.reference)?, &path)?.ty();
                        Ok(Symbol::Ref(Box::new(ty), case.reference, path))
                    },
                )
            }
            Kind::Index(base, index) => {
                let base = self.place_reference(base)?;
                let index = self.nonnegative(index, "nonnegative reference index")?;
                self.on_reference_places(
                    &guarded_references::cases(&base)?,
                    None,
                    expression.line,
                    &|ctx, case| ctx.index_reference(case, &index, expression.line),
                )
            }
            _ => {
                let (reference, path) = self.location(expression)?;
                let ty = project(self.storage.memory.read(reference)?, &path)?.ty();
                Ok(Symbol::Ref(Box::new(ty), reference, path))
            }
        }
    }

    pub(super) fn index_reference(
        &mut self,
        case: &Case,
        index: &Linear,
        line: usize,
    ) -> Result<Symbol> {
        self.validate_member_path(case.reference, &case.path, line)?;
        self.charge_value_work(symbol_weight(self.storage.memory.read(case.reference)?)?)?;
        let mut root = self.storage.memory.read(case.reference)?.clone();
        let Symbol::Array {
            element,
            len,
            items,
            cells,
            identity,
        } = project(&root, &case.path)?.clone()
        else {
            return Err("reference index requires array storage".into());
        };
        self.prove(
            &Formula::Ge(len.sub(index)?.add(&Linear::number(-1))?),
            "reference index < length",
            line,
        )?;
        if matches!(
            self.arrays.history.get(&identity),
            Some(ArrayHistory::Uninitialized(_))
        ) {
            return self
                .uninitialized_index_reference(case, index, &element, &identity, &cells, line);
        }
        let literal =
            constant_index(index).and_then(|i| items.as_ref().and_then(|items| items.get(i)));
        let input_union =
            self.arrays.inputs.contains(&identity) && matches!(element.as_ref(), Ty::Union(_));
        if input_union
            || !cells.contains_key(index) && (literal.is_none() || self.history_element(&element))
        {
            if !self.history_element(&element) && !self.ty_has_reference(&element) && !input_union {
                return Err("borrowing opaque array elements requires scalars or reference-free records without runtime cleanup".into());
            }
            let value = self.read_array(&element, &identity, index, items.as_deref(), &cells)?;
            let Symbol::Array { cells, .. } = project_mut(&mut root, &case.path)? else {
                return Err("invalid array storage".into());
            };
            cells.insert(index.clone(), value);
            let plane = self.storage.memory.plane(case.reference)?;
            self.storage.memory.write(plane, root, false)?;
        }
        let mut path = case.path.clone();
        path.push(Projection::Index(index.clone()));
        project(self.storage.memory.read(case.reference)?, &path)?;
        Ok(Symbol::Ref(element, case.reference, path))
    }

    pub(super) fn assign_indirect(&mut self, place: &Expr, expression: &Expr) -> Result<()> {
        let target = self.place_reference(place)?;
        let Ty::Ref(ty) = target.ty() else {
            return Err("assignment requires a stored place".into());
        };
        let value = self.eval(expression, Some(&ty))?;
        self.on_reference_places(
            &guarded_references::cases(&target)?,
            Some(&Ty::Unit),
            place.line,
            &|ctx, case| {
                ctx.write_reference(case.reference, &case.path, value.clone(), place.line)?;
                Ok(Symbol::Unit)
            },
        )?;
        Ok(())
    }

    fn write_reference(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        value: Symbol,
        line: usize,
    ) -> Result<()> {
        self.validate_member_path(reference, path, line)?;
        let old = project(self.storage.memory.read(reference)?, path)?.clone();
        if self.has_runtime_cleanup(&old.ty())
            && !(self.execution.phase == Phase::Ideal && self.erased_value(&old))
            && !self.uninitialized_union(&old, line)?
        {
            return Err("overwriting owned fields through references requires ownership effect proofs; unsupported".into());
        }
        self.replace_reference_contents(reference, path, value, line)
    }

    // Callers must first discharge old cleanup or transfer its live payload.
    // This common store still enforces write authority, revisions, and types.
    pub(super) fn replace_reference_contents(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        mut value: Symbol,
        line: usize,
    ) -> Result<()> {
        self.validate_member_path(reference, path, line)?;
        let id = self.storage.memory.plane(reference)?;
        let owned = self.owns_plane(id)?;
        if !self.write_permitted(reference, path, owned)? {
            return Err(format!("line {line}: writes through reference parameters need an effect contract; unsupported"));
        }
        let old = project(self.storage.memory.read(reference)?, path)?.clone();
        self.compatible(&value.ty(), &old.ty(), line)?;
        let replace_plane = !self.same_layout(&old, &value)?;
        if !replace_plane {
            self.preserve_views(&old, &mut value)?;
        }
        let mut root = self.storage.memory.read(reference)?.clone();
        self.replace_projection(&mut root, path, value)?;
        let lifted = self
            .storage
            .opened_planes
            .get(&id)
            .cloned()
            .unwrap_or_default();
        self.note_state_write(id, path)?;
        self.storage.memory.write(id, root.clone(), replace_plane)?;
        self.retained_valid_with(&root, line, &lifted)?;
        for (name, plane) in &self.locals.places {
            if *plane == id {
                self.locals.values.insert(name.clone(), root.clone());
            }
        }
        self.validate_opened_planes(line)
    }
}
