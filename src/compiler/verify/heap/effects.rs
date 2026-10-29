//! A checked boundary for replacing reference-free owned allocations. Returning
//! an input allocation, borrowing one, or containing nested pointers requires
//! the ordinary actual-body path instead.

use super::*;

impl Context<'_> {
    pub(in crate::compiler::verify) fn fresh_allocation_inputs(
        &self,
        function: &Function,
    ) -> Result<Option<Vec<PlaneId>>> {
        let Type::Unique(inner) = &function.ret else {
            return Ok(None);
        };
        if function.external.is_some()
            || function.ideal
            || !function.modifies.is_empty()
            || !function.borrows.is_empty()
            || type_has_reference(inner, self.declarations.structs)
        {
            return Ok(None);
        }
        let mut inputs = Vec::new();
        for (name, ty) in &function.params {
            match ty {
                Type::Unique(inner) if !type_has_reference(inner, self.declarations.structs) => {
                    let Some(Symbol::Unique(_, reference)) = self.locals.values.get(name) else {
                        return Err("fresh allocation input lost its unique owner".into());
                    };
                    inputs.push(self.storage.memory.plane(*reference)?);
                }
                ty if !type_has_reference(ty, self.declarations.structs) => {}
                _ => return Ok(None),
            }
        }
        Ok(Some(inputs))
    }

    pub(in crate::compiler::verify) fn apply_fresh_allocation_inputs(
        &mut self,
        function: &Function,
    ) -> Result<()> {
        let inputs = self
            .fresh_allocation_inputs(function)?
            .ok_or("fresh allocation summary does not match its signature")?;
        for plane in inputs {
            self.charge_value_work(symbol_weight(self.storage.memory.get(plane)?)?)?;
            let payload = self.storage.memory.get(plane)?.clone();
            self.remember_scalar_payloads(&payload)?;
            self.take_symbol(plane)?;
        }
        Ok(())
    }
}
