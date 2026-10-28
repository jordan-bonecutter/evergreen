//! A fresh frontend scalar can name one immutable term. This is a definition
//! of that scalar, not a hypothesis about an existing input. Its free inputs
//! remain fixed: universal introduction cannot generalize over them.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::compiler::verify) struct BindingId(usize);

#[derive(Debug)]
pub(super) struct Binding {
    terms: Arc<Terms>,
    value: Id,
    name: Id,
    variables: BTreeSet<String>,
}

impl Evidence {
    /// The frontend must allocate a fresh scalar name for the observed value.
    /// Definitions cannot overwrite one another or introduce a forward cycle.
    pub(in crate::compiler::verify) fn define_scalar_binding(
        &mut self,
        name: String,
        mut terms: Terms,
        value: Id,
    ) -> Result<BindingId> {
        if self.scalars.bound_names.contains(&name) || self.scalars.binding_inputs.contains(&name) {
            return Err("scalar binding requires a fresh name".into());
        }
        let mut work = Work::new(MAX_VALUE_WORK.saturating_sub(self.storage_weight));
        let mut variables = terms.free_variables(value, &mut work)?;
        if variables.contains(&name) {
            return Err("scalar binding cannot refer to itself".into());
        }
        let variable = terms.variable(&name, &mut work)?;
        work.charge(
            variables
                .iter()
                .fold(name.len(), |sum, name| sum.saturating_add(name.len() + 1)),
        )?;
        self.storage_weight += work.spent();
        self.scalars
            .binding_inputs
            .extend(variables.iter().cloned());
        self.scalars.bound_names.insert(name.clone());
        variables.insert(name);
        let id = BindingId(self.scalars.bindings.len());
        self.scalars.bindings.push(Binding {
            terms: Arc::new(terms),
            value,
            name: variable,
            variables,
        });
        Ok(id)
    }

    pub(in crate::compiler::verify::evidence) fn scalar_binding_mentions(
        &self,
        binding: BindingId,
        variable: &str,
    ) -> Result<bool> {
        Ok(self
            .scalar_binding_definition(binding)?
            .variables
            .contains(variable))
    }

    fn scalar_binding_definition(&self, binding: BindingId) -> Result<&Binding> {
        self.scalars
            .bindings
            .get(binding.0)
            .ok_or_else(|| "missing scalar binding".into())
    }

    pub(in crate::compiler::verify::evidence) fn scalar_binding(
        &self,
        goal: &Formula,
        binding: BindingId,
        work: &mut usize,
        limit: usize,
    ) -> Result<bool> {
        let mut budget = Work::new(limit.saturating_sub(*work));
        let result = (|| {
            let binding = self.scalar_binding_definition(binding)?;
            let mut scratch = Terms::new()?;
            let Some((left, right)) = self.scalar_sides(goal, &mut scratch, &mut budget)? else {
                return Ok(false);
            };
            let roots =
                scratch.import(&binding.terms, &[binding.value, binding.name], &mut budget)?;
            Ok((left, right) == (roots[0], roots[1]) || (right, left) == (roots[0], roots[1]))
        })();
        *work = work.saturating_add(budget.spent());
        result
    }
}
