//! Owning-reference claims erase to ordinary pointers. Library counters remain
//! source operations; the backend emits no hidden reference-count updates.

use super::*;

impl Emitter<'_> {
    pub(super) fn owner_operation(&mut self, name: &str, args: &[Expr]) -> Result<Type> {
        let [argument] = args else {
            return Err("ownership operation requires one argument".into());
        };
        let ty = self.expr(argument, None)?;
        match (name, ty) {
            ("share_owner", Type::Plane(inner)) => Ok(Type::Owner(inner)),
            ("recover_owner", Type::Owner(inner)) => Ok(Type::Plane(inner)),
            ("release_owner", Type::Owner(_)) => {
                self.immediate(0);
                Ok(Type::Unit)
            }
            ("duplicate_owner", Type::Ref(inner)) => {
                if !matches!(inner.as_ref(), Type::Owner(_)) {
                    return Err("duplicate_owner needs a borrowed owning reference".into());
                }
                self.load_scalar(&inner)?;
                Ok(*inner)
            }
            _ => Err("invalid native ownership operation".into()),
        }
    }
}
