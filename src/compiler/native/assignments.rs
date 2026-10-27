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
        let old =
            if self.has_drop(&ty) && owner.as_ref().is_some_and(|name| self.alive.contains(name)) {
                let home = self.allocate(&ty)?;
                if !layout::aggregate(&ty) {
                    self.load_scalar(&ty)?;
                }
                self.copy_frame(home, &ty)?;
                Some(home)
            } else {
                None
            };
        self.expr(value, Some(&ty))?;
        if self.has_drop(&ty) {
            let new_value = self.allocate(&ty)?;
            self.copy_frame(new_value, &ty)?;
            if let (Some(old), Some(owner)) = (old, owner) {
                self.cleanup_replaced_value(&owner, old, &ty)?;
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
