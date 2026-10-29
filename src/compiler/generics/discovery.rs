//! Resolve method uses to a fixed point before verification. Signature-only
//! prototypes are removed unless their checked body is instantiated.

use super::*;

impl Engine {
    pub(super) fn finish(&mut self, program: &mut Program) -> Result<()> {
        loop {
            while let Some(item) = self.pending.pop_front() {
                match item {
                    Concrete::Record(mut record) => {
                        self.record(&mut record)?;
                        program.structs.push(*record);
                    }
                    Concrete::Function(mut function) => {
                        self.function(&mut function)?;
                        program.functions.push(*function);
                    }
                    Concrete::Destructor(target, mut function) => {
                        self.function(&mut function)?;
                        program.destructors.push((target, *function));
                    }
                }
            }
            program.functions.append(&mut self.implementations.headers);
            templates::charge_program(program, &mut self.work)?;
            crate::compiler::field_sugar::expand_for(program, self.target);
            let mut calls = Calls {
                pending: &self.implementations.bodies,
                requested: BTreeSet::new(),
            };
            for record in &mut program.structs {
                calls.record(record)?;
            }
            for function in &mut program.functions {
                if !calls.pending.contains_key(&function.name) {
                    calls.function(function)?;
                }
            }
            for (_, function) in &mut program.destructors {
                calls.function(function)?;
            }
            if calls.requested.is_empty() {
                break;
            }
            let requested = calls.requested;
            program
                .functions
                .retain(|function| !requested.contains(&function.name));
            for name in requested {
                let body = self
                    .implementations
                    .bodies
                    .remove(&name)
                    .ok_or("missing generic method body")?;
                let function = body.instantiate(&mut self.work)?;
                self.pending.push_back(Concrete::Function(function));
            }
        }
        program
            .functions
            .retain(|function| !self.implementations.bodies.contains_key(&function.name));
        Ok(())
    }
}

struct Calls<'a> {
    pending: &'a BTreeMap<String, implementations::MethodBody>,
    requested: BTreeSet<String>,
}
impl Visitor for Calls<'_> {
    fn expr(&mut self, expression: &mut Expr) -> Result<()> {
        if let Kind::Call(name, _) = &expression.kind {
            if self.pending.contains_key(name) {
                self.requested.insert(name.clone());
            }
        }
        visit::walk_expr(self, expression)
    }
}
