//! Demand-driven computation of read-only verified definitions on concrete
//! inputs and total scalar symbolic expressions. Source contracts and trust
//! dependencies still pass through the ordinary call checker. Under a quantifier,
//! only safety-verified scalar definitions may reduce, with separately checked
//! preconditions and no imported postconditions. Neither path adds an axiom or
//! an FFI escape hatch.

use super::*;

mod aggregate;
mod applications;
mod evaluate;
mod quantified;
mod symbolic;
#[cfg(test)]
mod tests;
mod values;
#[cfg(test)]
mod view_tests;
pub(super) use applications::Applications;

use values::{Budget, Importer, Value};

impl Context<'_> {
    // Expression predicates describe propositions; evaluating one does not
    // establish its truth. Their declarations have already checked safety.
    pub(super) fn can_reduce_fact(&self, function: &Function) -> bool {
        function.ret == Type::Fact
            && function.ideal
            && function.body.is_empty()
            && function.pre.is_none()
            && function.post.is_none()
            && function.decreases.is_none()
            && eligible(self, function)
    }

    pub(super) fn reduce_fact(&mut self, function: &Function) -> Result<Symbol> {
        let safety = self.import_summary(&function.name, summaries::Aspect::Safety)?;
        self.proof.uses.extend(safety);
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let ideal = std::mem::replace(&mut self.execution.ideal_execution, true);
        let current = self.execution.current.replace(function.name.clone());
        let facts = std::mem::take(&mut self.proof.facts);
        let witnesses = std::mem::take(&mut self.proof.witnesses);
        let value = self.proposition(&function.result).map(Symbol::Fact);
        self.proof.facts = facts;
        self.proof.witnesses = witnesses;
        self.execution.current = current;
        self.execution.ideal_execution = ideal;
        self.execution.phase = phase;
        value
    }

    pub(super) fn reduce_ideal(&mut self, function: &Function) -> Result<Option<Symbol>> {
        if !function.ideal
            || !eligible(self, function)
            || !matches!(
                function.ret,
                Type::Int | Type::Nat | Type::Bool | Type::Unit | Type::Machine(_)
            )
        {
            return Ok(None);
        }
        let application = self.scalar_application(function)?;
        if let Some(value) = application
            .as_ref()
            .and_then(|key| self.applications.computed.get(key))
        {
            return Ok(Some(value.clone()));
        }
        let (value, spent) = {
            let mut budget = Budget::new(MAX_VALUE_WORK.saturating_sub(self.work.value_work));
            let mut importer = Importer::new(self, &mut budget);
            let mut arguments = BTreeMap::new();
            let mut supported = true;
            for (name, _) in &function.params {
                match importer.value(
                    self.locals
                        .values
                        .get(name)
                        .ok_or("missing ideal argument")?,
                    0,
                )? {
                    Some(value) => {
                        arguments.insert(name.clone(), value);
                    }
                    None => {
                        supported = false;
                        break;
                    }
                }
            }
            let value = if supported {
                evaluate::run(self, function, arguments, &mut budget)?
            } else {
                None
            };
            if let Some(value) = &value {
                budget.spend(symbolic::weight(value)?)?;
            }
            // Aggregate views borrow the immutable call state only during
            // reduction. Export an owned scalar before restoring mutable access.
            (value.and_then(Value::scalar), budget.spent)
        };
        self.charge_value_work(spent)?;
        if let (Some(key), Some(value)) = (application, value.as_ref()) {
            self.applications.computed.insert(key, value.clone());
        }
        Ok(value)
    }
}

fn eligible(context: &Context<'_>, function: &Function) -> bool {
    !function.partial && function.external.is_none() && function.modifies.is_empty()
        && (function.ideal || context.declarations.helpers.contains(&function.name))
        // A recursive prototype is not yet a verified definition.
        && context.declarations.summaries.contains_key(&function.name)
}
