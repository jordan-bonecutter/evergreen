//! Unique ownership of stable, separately allocated planes. No shared-owner
//! capability or allocation authority can be fabricated by ideal computation.

use super::*;

pub(super) fn payload_type(ty: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match ty {
        Type::Ref(_) => false,
        Type::Plane(inner) | Type::Array(inner, _) => payload_type(inner, structs),
        Type::Named(name) => structs.get(name).is_some_and(|definition| {
            definition
                .fields
                .iter()
                .all(|(_, ty)| payload_type(ty, structs))
        }),
        _ => true,
    }
}

pub(super) fn owns_planes_type(ty: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match ty {
        Type::Plane(_) => true,
        Type::Array(inner, _) => owns_planes_type(inner, structs),
        Type::Named(name) => structs.get(name).is_some_and(|definition| {
            definition
                .fields
                .iter()
                .any(|(_, ty)| owns_planes_type(ty, structs))
        }),
        _ => false, // Borrowing an owner does not transfer its authority.
    }
}

pub(super) fn function_uses_planes(
    function: &Function,
    structs: &BTreeMap<String, Struct>,
) -> bool {
    fn ty(value: &Type, structs: &BTreeMap<String, Struct>) -> bool {
        match value {
            Type::Plane(_) => true,
            Type::Ref(inner) | Type::Array(inner, _) => ty(inner, structs),
            Type::Named(name) => structs.get(name).is_some_and(|definition| {
                definition
                    .fields
                    .iter()
                    .any(|(_, field)| ty(field, structs))
            }),
            _ => false,
        }
    }

    fn expression(value: &Expr) -> bool {
        match &value.kind {
            Kind::Call(name, _) if name == "alloc" => true,
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => expression(e),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => expression(a) || expression(b),
            Kind::If(c, a, b) => expression(c) || expression(a) || expression(b),
            Kind::Call(_, args) | Kind::Array(args) => args.iter().any(expression),
            Kind::Record(_, fields) => fields.iter().any(|(_, value)| expression(value)),
            _ => false,
        }
    }

    fn statement(value: &Statement, structs: &BTreeMap<String, Struct>) -> bool {
        match value {
            Statement::Ideal(inner) => statement(inner, structs),
            Statement::Let {
                ty: annotation,
                value,
                ..
            } => annotation.as_ref().is_some_and(|t| ty(t, structs)) || expression(value),
            Statement::Destructure { value, .. }
            | Statement::Effect(value)
            | Statement::Fact { value, .. } => expression(value),
            Statement::Proof { proposition, .. } => expression(proposition),
            Statement::Assign { target, value } => expression(target) || expression(value),
            Statement::Update { body, .. } => body.iter().any(|s| statement(s, structs)),
        }
    }
    function.params.iter().any(|(_, t)| ty(t, structs))
        || ty(&function.ret, structs)
        || function.body.iter().any(|s| statement(s, structs))
        || expression(&function.result)
}

pub(super) fn syntax_type(ty: &Ty, line: usize) -> Result<Type> {
    Ok(match ty {
        Ty::Int => Type::Int,
        Ty::Nat => Type::Nat,
        Ty::Bool => Type::Bool,
        Ty::Unit => Type::Unit,
        Ty::Machine(t) => Type::Machine(*t),
        Ty::Record(name) => Type::Named(name.clone()),
        Ty::Plane(inner) => Type::Plane(Box::new(syntax_type(inner, line)?)),
        Ty::Ref(inner) => Type::Ref(Box::new(syntax_type(inner, line)?)),
        Ty::Array(inner, len) if len.terms.is_empty() => Type::Array(
            Box::new(syntax_type(inner, line)?),
            Box::new(Expr {
                kind: Kind::Number(len.constant),
                line,
            }),
        ),
        Ty::Array(..) => return Err("allocated planes require fixed array extents".into()),
    })
}

pub(super) fn payload_layout(ty: &Type, structs: &BTreeMap<String, Struct>) -> Result<()> {
    if let Type::Array(element, count) = ty {
        if crate::compiler::layout::array_length(count).is_err() {
            crate::compiler::layout::of(element, structs)?;
            return Ok(());
        }
    }
    crate::compiler::layout::of(ty, structs).map(|_| ())
}

impl Context<'_> {
    pub(super) fn allocate_owned(
        &mut self,
        args: &[Expr],
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        if self.phase != Phase::Runtime || self.dropping || !self.opened_planes.is_empty() {
            return Err("allocation requires runtime execution with closed invariants".into());
        }
        if args.len() == 2 {
            return self.allocate_filled(args, expected, line);
        }
        if args.len() != 1 {
            return Err("alloc expects a payload, or a count and initial element".into());
        }
        let hint = match expected {
            Some(Ty::Plane(inner)) => Some(inner.as_ref()),
            _ => None,
        };
        let value = self.eval(&args[0], hint)?;
        let ty = value.ty();
        let syntax = syntax_type(&ty, line)?;
        if !runtime_type(&syntax, self.structs) || !payload_type(&syntax, self.structs) {
            return Err("owned planes require runtime payloads without borrowed references".into());
        }
        crate::compiler::layout::of(&syntax, self.structs)?;
        self.validate_argument(&value, line)?;
        let plane = self.memory.allocate(value)?;
        Ok(Symbol::Plane(Box::new(ty), self.memory.borrow(plane)?))
    }

    fn allocate_filled(
        &mut self,
        args: &[Expr],
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        let count_type = Ty::Machine(MachineInt::parse("usize").unwrap());
        let count = self.eval(&args[0], Some(&count_type))?.number()?;
        let hint = match expected {
            Some(Ty::Plane(inner)) => match inner.as_ref() {
                Ty::Array(element, _) => Some(element.as_ref()),
                _ => None,
            },
            _ => None,
        };
        let initial = self.eval(&args[1], hint)?;
        let element = initial.ty();
        let syntax = syntax_type(&element, line)?;
        if self.symbol_is_affine(&initial)
            || !payload_type(&syntax, self.structs)
            || !self.history_element(&element)
            || !runtime_type(&syntax, self.structs)
        {
            return Err("filled allocation requires copyable scalar or flat scalar-record elements without references".into());
        }
        let stride = crate::compiler::layout::of(&syntax, self.structs)?.size;
        let maximum = crate::compiler::layout::MAX_LAYOUT_BYTES / stride;
        self.prove(
            &Formula::Ge(count.clone()),
            "nonnegative allocation count",
            line,
        )?;
        self.prove(
            &Formula::Ge(Linear::number(maximum as i128).sub(&count)?),
            "allocation fits the 64 KiB object budget",
            line,
        )?;
        self.validate_argument(&initial, line)?;
        let identity = self.fresh_name();
        self.charge_value_work(symbol_weight(&initial)?)?;
        self.array_history
            .insert(identity.clone(), ArrayHistory::Fill(initial));
        let value = Symbol::Array {
            element: Box::new(element.clone()),
            len: count.clone(),
            items: None,
            cells: BTreeMap::new(),
            identity,
        };
        let plane = self.memory.allocate(value)?;
        Ok(Symbol::Plane(
            Box::new(Ty::Array(Box::new(element), count)),
            self.memory.borrow(plane)?,
        ))
    }

    pub(super) fn owns_plane(&mut self, plane: PlaneId) -> Result<bool> {
        if self.roots.values().any(|root| *root == plane) {
            return Ok(true);
        }
        let env = self.clone_env()?;
        let roots = self.roots.clone();
        self.owns_plane_in(&env, &roots, plane)
    }

    pub(super) fn owns_plane_in(
        &mut self,
        env: &BTreeMap<String, Symbol>,
        roots: &BTreeMap<String, PlaneId>,
        plane: PlaneId,
    ) -> Result<bool> {
        if roots.values().any(|root| *root == plane) {
            return Ok(true);
        }
        let mut pending = Vec::new();
        for (name, value) in env {
            let observed = if let Some(root) = roots.get(name) {
                let Ok(value) = self.memory.get(*root) else {
                    continue;
                };
                value
            } else {
                value
            };
            let cost = symbol_weight(observed)?;
            self.charge_value_work(cost)?;
            let value = if let Some(root) = roots.get(name) {
                self.memory.get(*root)?
            } else {
                value
            };
            pending.push(value.clone());
        }
        while let Some(value) = pending.pop() {
            self.charge_value_work(1)?;
            match value {
                Symbol::Plane(_, reference) => {
                    let owned = self.memory.plane(reference)?;
                    if owned == plane {
                        return Ok(true);
                    }
                    self.charge_value_work(symbol_weight(self.memory.read(reference)?)?)?;
                    pending.push(self.memory.read(reference)?.clone());
                }
                Symbol::Record(_, fields) => pending.extend(fields.into_values()),
                Symbol::Array { items, cells, .. } => {
                    pending.extend(items.into_iter().flatten());
                    pending.extend(cells.into_values());
                }
                _ => {} // A borrowed pointer does not own its target.
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
mod filled_tests {
    use super::*;

    #[test]
    fn runtime_planes_initialize_every_cell_and_replay() {
        let source = include_str!("../../../examples/runtime_planes.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(source, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        let empty = "fn main() -> usize {let a: plane(usize, 0) = alloc(0, 7); let b: plane(usize, 0) = alloc(0, 9); if &*a != &*b {42} else {1}}";
        assert_eq!(verify(empty).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn runtime_allocation_checks_bounds_ownership_and_liveness() {
        for source in [
            "fn make(n: usize) -> plane(usize, n) {alloc(n, 0)} fn main() -> usize {42}",
            "fn main() -> usize {let a: plane(usize, 8193) = alloc(8193, 0); 42}",
            "fn main() -> usize {let a: plane(usize, 2) = alloc(2, 0); (*a)[2]}",
            "fn main() -> usize {let x: usize = 42; let a = alloc(2, &x); 42}",
            "fn main() -> usize {let a = alloc(2, alloc(42)); 42}",
            "type Resource struct {tag: usize} impl Drop for Resource {fn drop(self) {}} fn main() -> usize {let a = alloc(2, Resource {tag: 7}); 42}",
            "fn main() -> usize {let a: plane(usize, 2) = alloc(2, 0); let view = &*a; drop(a); (*view)[0]}",
            "fn main() -> usize {let n: usize = 2; let a: plane(usize, n) = alloc(n, 0); let view = &*a; n = 3; (*view)[n - 1]}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
    }
}
