//! Sequential executable specification; this evaluator does not create threads.

use super::*;

impl Evaluator<'_> {
    pub(super) fn compare_exchange64(&mut self, values: Vec<Value>) -> Result<Value> {
        let [Value::Ref(_, reference, path), expected, desired] = values.as_slice() else {
            return Err("compare_exchange64 operand mismatch".into());
        };
        let old = copy_value(
            project(self.memory.read(*reference)?, path)?,
            &mut self.fuel,
        )?;
        if old == *expected {
            let id = self.memory.plane(*reference)?;
            let mut root = copy_value(self.memory.read(*reference)?, &mut self.fuel)?;
            replace_projection(&mut root, path, copy_value(desired, &mut self.fuel)?)?;
            self.memory.write(id, root, false)?;
        }
        Ok(old)
    }
}
