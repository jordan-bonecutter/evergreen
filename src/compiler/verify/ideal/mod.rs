//! Demand-driven computation of read-only verified definitions on concrete
//! inputs. Source contracts and their trust dependencies still pass through the
//! ordinary call checker; reduction is not a new axiom or an FFI escape hatch.

use super::*;

mod applications;
mod evaluate;
#[cfg(test)]
mod tests;
mod values;
#[cfg(test)]
mod view_tests;
pub(super) use applications::Applications;

use values::{Budget, Importer, Value};

impl Context<'_> {
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
        let application = self.predicate_application(function)?;
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
            let mut concrete = true;
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
                        concrete = false;
                        break;
                    }
                }
            }
            let value = if concrete {
                evaluate::run(self, function, arguments, &mut budget)?
            } else {
                None
            };
            (value, budget.spent)
        };
        self.charge_value_work(spent)?;
        let value = value.and_then(Value::scalar);
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
