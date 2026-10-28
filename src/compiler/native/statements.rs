//! Statement lowering, lexical bindings, and runtime loop control flow.

use super::*;

impl Emitter<'_> {
    pub(super) fn statement(&mut self, statement: &Statement) -> Result<()> {
        let start = self.temporaries.len();
        self.statement_inner(statement)?;
        self.finish_temporaries(start)
    }

    pub(super) fn statement_inner(&mut self, statement: &Statement) -> Result<()> {
        match statement {
            Statement::While {
                condition, body, ..
            } => self.while_loop(condition, body),
            Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => Ok(()),
            Statement::Let { name, ty, value } => {
                let ty = self.expr(value, ty.as_ref())?;
                self.slot(name, ty)
            }
            Statement::Assign { target, value, .. } => self.assign(target, value),
            Statement::Destructure {
                record,
                arguments,
                fields,
                value,
            } => {
                if !arguments.is_empty() {
                    return Err("generic record pattern requires specialization".into());
                }
                let ty = Type::Named(record.clone());
                self.expr(value, Some(&ty))?;
                self.code.extend([0x48, 0x89, 0xc6]);
                for (field, name) in fields {
                    if self.structs[record].ideal_fields.contains(field) {
                        continue;
                    }
                    let field = self.field(&ty, field)?;
                    self.code.extend([0x48, 0x8d, 0x86]);
                    self.code.extend((field.offset as i32).to_le_bytes());
                    if !layout::aggregate(&field.ty) {
                        self.load_scalar(&field.ty)?;
                    }
                    self.slot(name, field.ty)?;
                }
                Ok(())
            }
            Statement::Update { body, .. } => {
                let saved = self.slots.clone();
                let saved_alive = self.alive.clone();
                for statement in body {
                    self.statement(statement)?;
                }
                self.slots = saved;
                self.alive = saved_alive;
                Ok(())
            }
            Statement::Effect(e) => {
                let ty = self.expr(e, None)?;
                self.drop_value(&ty)
            }
        }
    }

    pub(super) fn while_loop(&mut self, condition: &Expr, body: &[Statement]) -> Result<()> {
        let slots = self.slots.clone();
        let alive = self.alive.clone();
        let head = self.code.len();
        self.scoped_expr(condition, Some(&Type::Bool))?;
        self.code.extend([0x48, 0x85, 0xc0, 0x0f, 0x84]); // test rax; jz exit
        let exit = self.code.len();
        self.code.extend([0; 4]);
        for item in body {
            self.statement(item)?;
        }
        let names = body
            .iter()
            .flat_map(|s| s.runtime_bindings(self.structs))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        for name in names.into_iter().rev() {
            self.cleanup_binding(&name, false)?;
        }
        if self.alive != alive {
            return Err("loop body changes surrounding native ownership".into());
        }
        self.slots = slots;
        self.alive = alive;
        self.code.push(0xe9);
        let back = self.code.len();
        self.code.extend([0; 4]);
        patch(self.code, back, head)?;
        let end = self.code.len();
        patch(self.code, exit, end)
    }
}
