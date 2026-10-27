//! Spill the result across local destructors, then discard lexical slots.
//! The enclosing function keeps ownership changes to surrounding bindings.

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
}
