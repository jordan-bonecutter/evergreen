//! Expression blocks consume local storage before returning their result.

use super::*;

impl Evaluator<'_> {
    pub(super) fn block_value(
        &mut self,
        body: &[Statement],
        tail: &Expr,
        env: &BTreeMap<String, Value>,
        expected: Option<&Type>,
    ) -> Result<Value> {
        let mut local = env
            .iter()
            .map(|(name, value)| Ok((name.clone(), copy_value(value, &mut self.fuel)?)))
            .collect::<Result<BTreeMap<_, _>>>()?;
        for statement in body {
            self.statement(statement, &mut local)?;
        }
        let result = self.scoped_expr(tail, &local, expected)?;
        let names = body
            .iter()
            .flat_map(|s| s.runtime_bindings(self.structs))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        for name in names.into_iter().rev() {
            let value = if let Some(plane) = self.roots.remove(&name) {
                self.memory.take(plane).ok()
            } else {
                local.remove(&name)
            };
            if let Some(value) = value {
                self.drop_value(value)?;
            }
        }
        Ok(result)
    }
}
