//! Capture the destination once, evaluate the replacement, clean up the old
//! value only if its binding still owns it, then install the replacement.

use super::*;

fn root(expression: &Expr) -> Option<&str> {
    match &expression.kind {
        Kind::Name(name) => Some(name),
        Kind::Field(base, _) | Kind::Index(base, _) => root(base),
        _ => None,
    }
}

impl Emitter<'_> {
    pub(super) fn assign(&mut self, target: &Expr, value: &Expr) -> Result<()> {
        let owner = root(target).map(str::to_owned);
        let ty = self.address(target)?;
        let pointer_ty = Type::Ref(Box::new(ty.clone()));
        let pointer = self.allocate(&pointer_ty)?;
        self.copy_frame(pointer, &pointer_ty)?;
        self.expr(value, Some(&ty))?;
        // Live union replacement is admitted only for a proved shape member. No
        // payload exists to drop, and the active selector is erased.
        if self.has_drop(&ty) && !matches!(ty, Type::Union(_)) {
            let new_value = self.allocate(&ty)?;
            self.copy_frame(new_value, &ty)?;
            if let Some(owner) = owner {
                self.cleanup_replaced_place(&owner, pointer, &ty)?;
            }
            self.frame_address(new_value);
            if !layout::aggregate(&ty) {
                self.load_scalar(&ty)?;
            }
        }
        self.code.extend([0x48, 0x8b, 0x8d]);
        self.code.extend(pointer.to_le_bytes());
        self.copy_address(&ty)?;
        if let Kind::Name(name) = &target.kind {
            self.mark_live(name);
        }
        Ok(())
    }
}
