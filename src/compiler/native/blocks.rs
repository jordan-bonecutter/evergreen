//! Lexical expression scopes and conditional ownership joins.
//! Results survive local cleanup; changes to surrounding bindings remain visible.

use super::*;

impl Emitter<'_> {
    pub(super) fn block_value(
        &mut self,
        body: &[Statement],
        tail: &Expr,
        expected: Option<&Type>,
    ) -> Result<Type> {
        let slots = self.slots.clone();
        for statement in body {
            self.statement(statement)?;
        }
        let ty = self.scoped_expr(tail, expected)?;
        let result = self.allocate(&ty)?;
        self.copy_frame(result, &ty)?;
        let names = body
            .iter()
            .flat_map(|s| s.runtime_bindings(self.structs))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        for name in names.into_iter().rev() {
            self.cleanup_binding(&name, false)?;
        }
        self.slots = slots;
        self.frame_address(result);
        if !layout::aggregate(&ty) {
            self.load_scalar(&ty)?;
        }
        Ok(ty)
    }
    pub(super) fn conditional_value(
        &mut self,
        condition: &Expr,
        yes: &Expr,
        no: &Expr,
        expected: Option<&Type>,
    ) -> Result<Type> {
        self.scoped_expr(condition, Some(&Type::Bool))?;
        let base_alive = self.alive.clone();
        self.code.extend([0x48, 0x85, 0xc0]);
        let alternative = self.jump(true);
        let ty = self.scoped_expr(yes, expected)?;
        let yes_alive = self.alive.clone();
        let end = self.jump(false);
        let target = self.code.len();
        patch(self.code, alternative, target)?;
        self.alive = base_alive;
        self.scoped_expr(no, Some(&ty))?;
        self.alive.extend(yes_alive);
        let target = self.code.len();
        patch(self.code, end, target)?;
        Ok(ty)
    }
}
