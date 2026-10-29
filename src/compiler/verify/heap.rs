//! Unique ownership of stable, separately allocated planes. No shared-owner
//! capability or allocation authority can be fabricated by ideal computation.

use super::*;

pub(super) fn payload_type(ty: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match ty {
        Type::Ref(_) => false,
        Type::Union(members) => members.iter().all(|ty| payload_type(ty, structs)),
        Type::Shape(_) => true,
        Type::Unique(inner) | Type::Shared(inner) | Type::Array(inner, _) => {
            payload_type(inner, structs)
        }
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
        Type::Unique(_) | Type::Shared(_) => true,
        Type::Union(members) => members.iter().any(|ty| owns_planes_type(ty, structs)),
        Type::Shape(_) => false,
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
            Type::Unique(_) | Type::Shared(_) => true,
            Type::Union(members) => members.iter().any(|member| ty(member, structs)),
            Type::Shape(_) => false,
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

    fn expression(value: &Expr, structs: &BTreeMap<String, Struct>) -> bool {
        match &value.kind {
            Kind::Call(name, _) if name == "alloc" => true,
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => expression(e, structs),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                expression(a, structs) || expression(b, structs)
            }
            Kind::If(c, a, b) => {
                expression(c, structs) || expression(a, structs) || expression(b, structs)
            }
            Kind::Block(body, tail) => {
                body.iter().any(|s| statement(s, structs)) || expression(tail, structs)
            }
            Kind::Call(_, args) | Kind::Array(args) => args.iter().any(|e| expression(e, structs)),
            Kind::Record(_, fields) => fields.iter().any(|(_, value)| expression(value, structs)),
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
            } => annotation.as_ref().is_some_and(|t| ty(t, structs)) || expression(value, structs),
            Statement::Destructure { value, .. }
            | Statement::Effect(value)
            | Statement::Fact { value, .. } => expression(value, structs),
            Statement::Proof { proposition, .. } => expression(proposition, structs),
            Statement::Assign {
                target,
                value,
                starts,
            } => !starts.is_empty() || expression(target, structs) || expression(value, structs),
            Statement::Update { body, .. } => body.iter().any(|s| statement(s, structs)),
            Statement::While {
                condition, body, ..
            } => expression(condition, structs) || body.iter().any(|s| statement(s, structs)),
        }
    }
    function.params.iter().any(|(_, t)| ty(t, structs))
        || ty(&function.ret, structs)
        || function.body.iter().any(|s| statement(s, structs))
        || expression(&function.result, structs)
}

pub(super) fn syntax_type(ty: &Ty, line: usize) -> Result<Type> {
    Ok(match ty {
        Ty::Union(members) => Type::Union(
            members
                .iter()
                .map(|ty| syntax_type(ty, line))
                .collect::<Result<_>>()?,
        ),
        Ty::Shape(inner) => Type::Shape(Box::new(syntax_type(inner, line)?)),
        Ty::Type => return Err("ideal type observations have no runtime storage".into()),
        Ty::Int => Type::Int,
        Ty::Nat => Type::Nat,
        Ty::Bool => Type::Bool,
        Ty::Unit => Type::Unit,
        Ty::Machine(t) => Type::Machine(*t),
        Ty::Record(name) => Type::Named(name.clone()),
        Ty::Unique(inner) => Type::Unique(Box::new(syntax_type(inner, line)?)),
        Ty::Shared(inner) => Type::Shared(Box::new(syntax_type(inner, line)?)),
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
    if let Type::Array(element, _) = ty {
        // Only the repeated element needs an inline layout. The total heap
        // extent is checked symbolically by the owning allocation constructor.
        crate::compiler::layout::of(element, structs)?;
        return Ok(());
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
        if self.execution.phase != Phase::Runtime
            || self.execution.dropping
            || !self.storage.opened_planes.is_empty()
        {
            return Err("allocation requires runtime execution with closed invariants".into());
        }
        if args.len() == 2 {
            return self.allocate_filled(args, expected, line);
        }
        if args.len() != 1 {
            return Err("alloc expects a payload, or a count and initial element".into());
        }
        let hint = match expected.and_then(Ty::pointer_member) {
            Some(Ty::Unique(inner) | Ty::Shared(inner)) => Some(inner.as_ref()),
            _ => None,
        };
        let value = self.eval(&args[0], hint)?;
        let ty = value.ty();
        let syntax = syntax_type(&ty, line)?;
        if !runtime_type(&syntax, self.declarations.structs)
            || !payload_type(&syntax, self.declarations.structs)
        {
            return Err("owned planes require runtime payloads without borrowed references".into());
        }
        crate::compiler::layout::of(&syntax, self.declarations.structs)?;
        self.validate_argument(&value, line)?;
        let plane = self.allocate_symbol(value)?;
        Ok(Symbol::Unique(
            Box::new(ty),
            self.storage.memory.borrow(plane)?,
        ))
    }

    fn allocate_filled(
        &mut self,
        args: &[Expr],
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        let count_type = Ty::Machine(MachineInt::parse("usize").unwrap());
        let count = self.eval(&args[0], Some(&count_type))?.number()?;
        let hint = match expected.and_then(Ty::pointer_member) {
            Some(Ty::Unique(inner) | Ty::Shared(inner)) => match inner.as_ref() {
                Ty::Array(element, _) => Some(element.as_ref()),
                _ => None,
            },
            _ => None,
        };
        let initial = self.eval(&args[1], hint)?;
        let element = initial.ty();
        let syntax = syntax_type(&element, line)?;
        let uninitialized = self.shape_initializer(&initial);
        if !payload_type(&syntax, self.declarations.structs) {
            return Err(
                "filled allocation cannot currently store elements containing borrowed references"
                    .into(),
            );
        }
        if !runtime_type(&syntax, self.declarations.structs) {
            return Err("filled allocation requires an element type with a runtime layout".into());
        }
        if !uninitialized && self.symbol_is_move_only(&initial) {
            let name = syntax::display::expression(&Expr {
                kind: Kind::Type(syntax.clone()),
                line,
            });
            return Err(format!("filled allocation repeats its initializer, but {name} does not implement Copy; initialize vacant slots individually for move-only elements"));
        }
        if !uninitialized && !self.history_element(&element) {
            return Err("filled allocation currently supports scalar-only records; nested arrays, owning pointers, and runtime cleanup need individual slot initialization".into());
        }
        let stride = crate::compiler::layout::of(&syntax, self.declarations.structs)?.size;
        let maximum = (crate::compiler::layout::MAX_ALLOCATION_BYTES / stride as u64) as i128;
        self.prove(
            &Formula::Ge(count.clone()),
            "nonnegative allocation count",
            line,
        )?;
        self.prove(
            &Formula::Ge(Linear::number(maximum).sub(&count)?),
            "allocation byte size fits target addressable object range",
            line,
        )?;
        self.validate_argument(&initial, line)?;
        let identity = self.fresh_name();
        self.charge_value_work(symbol_weight(&initial)?)?;
        self.arrays.history.insert(
            identity.clone(),
            if uninitialized {
                ArrayHistory::Uninitialized(initial)
            } else {
                ArrayHistory::Fill(initial)
            },
        );
        let value = Symbol::Array {
            element: Box::new(element.clone()),
            len: count.clone(),
            items: None,
            cells: BTreeMap::new(),
            identity,
        };
        let plane = self.allocate_symbol(value)?;
        Ok(Symbol::Unique(
            Box::new(Ty::Array(Box::new(element), count)),
            self.storage.memory.borrow(plane)?,
        ))
    }

    pub(super) fn owns_plane(&mut self, plane: PlaneId) -> Result<bool> {
        if self.locals.places.values().any(|root| *root == plane) {
            return Ok(true);
        }
        let env = self.clone_env()?;
        let roots = self.locals.places.clone();
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
                let Ok(value) = self.storage.memory.get(*root) else {
                    continue;
                };
                value
            } else {
                value
            };
            let cost = symbol_weight(observed)?;
            self.charge_value_work(cost)?;
            let value = if let Some(root) = roots.get(name) {
                self.storage.memory.get(*root)?
            } else {
                value
            };
            pending.push((value.clone(), Formula::True));
        }
        let mut authority = Formula::False;
        while let Some((value, guard)) = pending.pop() {
            self.charge_value_work(1usize.saturating_add(guard.storage_weight()?))?;
            match value {
                Symbol::Shared(_, owner) => {
                    let reference = self.storage.memory.borrow_owned(owner)?;
                    let owned = self.storage.memory.plane(reference)?;
                    if owned == plane {
                        authority = authority.or(guard.clone());
                    }
                    self.charge_value_work(symbol_weight(self.storage.memory.read(reference)?)?)?;
                    pending.push((self.storage.memory.read(reference)?.clone(), guard));
                }
                Symbol::Unique(_, reference) => {
                    let paths = self.proof.paths.clone();
                    if self.checked_impossible(&paths, &guard)? {
                        continue;
                    }
                    let owned = self.storage.memory.plane(reference)?;
                    if owned == plane {
                        authority = authority.or(guard.clone());
                    }
                    self.charge_value_work(symbol_weight(self.storage.memory.read(reference)?)?)?;
                    pending.push((self.storage.memory.read(reference)?.clone(), guard));
                }
                Symbol::Union {
                    active, payloads, ..
                } => {
                    for (index, payload) in payloads.into_iter().enumerate() {
                        if let Some(payload) = payload {
                            let active = equal(&active, &Linear::number(index as i128))?;
                            pending.push((payload, guard.clone().and(active)));
                        }
                    }
                }
                Symbol::Record(_, fields) => {
                    pending.extend(fields.into_values().map(|value| (value, guard.clone())));
                }
                Symbol::Array { items, cells, .. } => {
                    pending.extend(
                        items
                            .into_iter()
                            .flatten()
                            .map(|value| (value, guard.clone())),
                    );
                    pending.extend(cells.into_values().map(|value| (value, guard.clone())));
                }
                _ => {} // A borrowed pointer does not own its target.
            }
        }
        self.checked_entails(&authority)
    }
}

#[cfg(test)]
mod filled_tests {
    use super::*;

    #[test]
    fn filled_allocation_errors_identify_the_failed_requirement() {
        for (source, expected) in [
            ("type Item struct {n: usize} fn main() {let p = alloc(2, Item{n: 1});}", "Item does not implement Copy"),
            ("fn main() {let n: usize = 1; let p = alloc(2, &n);}", "containing borrowed references"),
            ("type Item struct {data: [usize; 2]} impl Copy for Item {} fn main() {let p = alloc(2, Item{data: [1, 2]});}", "nested arrays"),
        ] {
            let error = verify(source).unwrap_err();
            assert!(error.contains(expected), "{error}");
        }
    }

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
        let large = "fn main() -> usize {let a: unique(usize, 9000) = alloc(9000, 42); (*a)[8999]}";
        assert_eq!(verify(large).unwrap().run().unwrap().to_string(), "42");
        // Verification and replay must depend on observations and stores, not
        // the buffer extent. Never execute this allocation in the test runner.
        let enormous = "fn main() -> usize {let a: unique(u8, 1000000000) = alloc(1000000000, 0); proof last_initialized: (*a)[999999999] == 0; (*a)[17] = 42; proof stored: (*a)[17] == 42; proof untouched: (*a)[0] == 0 && (*a)[999999999] == 0; 42}";
        let (program, bundle) = prove(enormous).unwrap();
        assert_eq!(
            verify_with_certificate(enormous, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        assert!(program.run().unwrap_err().contains("before allocation"));
        let empty = "fn main() -> usize {let a: unique(usize, 0) = alloc(0, 7); let b: unique(usize, 0) = alloc(0, 9); if &*a != &*b {42} else {1}}";
        assert_eq!(verify(empty).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn runtime_allocation_checks_bounds_ownership_and_liveness() {
        for source in [
            "fn make(n: usize) -> unique(usize, n) {alloc(n, 0)} fn main() -> usize {42}",
            "fn main() -> usize {let a: unique(usize, usize::MAX) = alloc(usize::MAX, 0); 42}",
            "fn main() -> usize {let a: unique(usize, 2) = alloc(2, 0); (*a)[2]}",
            "fn main() -> usize {let x: usize = 42; let a = alloc(2, &x); 42}",
            "fn main() -> usize {let a = alloc(2, alloc(42)); 42}",
            "type Resource struct {tag: usize} impl Drop for Resource {fn drop(self) {}} fn main() -> usize {let a = alloc(2, Resource {tag: 7}); 42}",
            "fn main() -> usize {let a: unique(usize, 2) = alloc(2, 0); let view = &*a; drop(a); (*view)[0]}",
            "fn main() -> usize {let n: usize = 2; let a: unique(usize, n) = alloc(n, 0); let view = &*a; n = 3; (*view)[n - 1]}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
    }
}
