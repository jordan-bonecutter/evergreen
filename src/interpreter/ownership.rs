//! The reference execution model checks generic lifetime tokens independently
//! of source Rc counters. Native code erases this semantic bookkeeping.

use super::*;

impl Evaluator<'_> {
    pub(super) fn owner_operation(
        &mut self,
        name: &str,
        args: &[Expr],
        env: &BTreeMap<String, Value>,
    ) -> Result<Value> {
        let [argument] = args else {
            return Err("ownership operation requires one argument".into());
        };
        let value = self.expr(argument, env, None)?;
        match (name, value) {
            ("share_owner", Value::Plane(ty, reference)) => {
                let plane = self.memory.plane(reference)?;
                Ok(Value::Owner(ty, self.memory.share_owner(plane)?))
            }
            ("duplicate_owner", Value::Ref(_, reference, path)) => {
                let Value::Owner(ty, owner) = project(self.memory.read(reference)?, &path)?.clone()
                else {
                    return Err("duplicate_owner needs a borrowed owning reference".into());
                };
                Ok(Value::Owner(ty, self.memory.duplicate_owner(owner)?))
            }
            ("release_owner", Value::Owner(_, owner)) => {
                let reference = self.memory.borrow_owned(owner)?;
                if self.memory.owner_count(reference)? <= 1 {
                    return Err("releasing an owner must leave another live claim".into());
                }
                self.memory.release_owner(owner)?;
                Ok(Value::Unit)
            }
            ("recover_owner", Value::Owner(ty, owner)) => {
                let reference = self.memory.borrow_owned(owner)?;
                let census = self.memory.owner_census(reference)?;
                self.memory.recover_unique_owner_at(owner, census)?;
                Ok(Value::Plane(ty, reference))
            }
            _ => Err("invalid interpreter ownership operation".into()),
        }
    }
}
