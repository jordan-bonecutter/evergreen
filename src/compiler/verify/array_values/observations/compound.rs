//! Interpret a complete specialized Boolean formula, retaining its connectives.
//! In particular, a disjunction never licenses either of its branches alone.

use super::*;

impl Context<'_> {
    pub(super) fn observe_compound_values(
        &mut self,
        theorem: evidence::NodeId,
        variable: &str,
        body: &Formula,
        identity: &str,
        index: &Linear,
        observed: &Symbol,
    ) -> Result<()> {
        if !matches!(
            body,
            Formula::And(..) | Formula::Or(..) | Formula::Implies(..) | Formula::Not(..)
        ) {
            return Ok(());
        }
        let mut pending = vec![body];
        let mut terms = BTreeSet::new();
        let mut alternatives = false;
        while let Some(part) = pending.pop() {
            self.charge_value_work(1)?;
            match part {
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    alternatives |= !matches!(part, Formula::And(..));
                    pending.extend([&**a, &**b])
                }
                Formula::Not(a) => {
                    alternatives |= !matches!(a.as_ref(), Formula::Predicate { .. });
                    pending.push(a);
                }
                Formula::Predicate { symbol, arguments } => {
                    let Some(key) = self.arrays.value_equality_origins.get(symbol) else {
                        continue;
                    };
                    for (side, contents) in [&key.0, &key.1].into_iter().enumerate() {
                        if contents.as_deref() == Some(identity) {
                            if let Some(term) = array_predicates::specialization_index(
                                &arguments[side],
                                index,
                                variable,
                            )? {
                                terms.insert(term);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        // Conjunctions of direct observations already have a projection path.
        if !alternatives {
            return Ok(());
        }
        for term in terms {
            self.charge_value_work(body.storage_weight()?)?;
            let instance = body.substitute(variable, &term)?;
            let Some(interpretation) =
                self.interpret_value_formula(&instance, identity, index, observed, 0)?
            else {
                continue;
            };
            if !interpretation.is_arithmetic() || self.checked_entails(&interpretation)? {
                continue;
            }
            let Some(premise) = self.checked_array_specialization(theorem, &term, &instance)?
            else {
                continue;
            };
            self.import_scalar_observation(instance, interpretation, premise, &[])?;
        }
        Ok(())
    }

    fn interpret_value_formula(
        &mut self,
        formula: &Formula,
        identity: &str,
        index: &Linear,
        observed: &Symbol,
        depth: usize,
    ) -> Result<Option<Formula>> {
        self.charge_value_work(1)?;
        if depth >= 64 {
            return Err("scalar observation formula depth limit reached".into());
        }
        if formula.is_arithmetic() {
            self.charge_value_work(formula.storage_weight()?)?;
            return Ok(Some(formula.clone()));
        }
        let result = match formula {
            Formula::Predicate { symbol, arguments } => {
                let Some(key) = self.arrays.value_equality_origins.get(symbol).cloned() else {
                    return Ok(None);
                };
                for (side, contents) in [&key.0, &key.1].into_iter().enumerate() {
                    if contents.as_deref() == Some(identity) && arguments.get(side) == Some(index) {
                        return self.observed_scalar_equality(formula, &key, side, index, observed);
                    }
                }
                return Ok(None);
            }
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                let Some(a) =
                    self.interpret_value_formula(a, identity, index, observed, depth + 1)?
                else {
                    return Ok(None);
                };
                let Some(b) =
                    self.interpret_value_formula(b, identity, index, observed, depth + 1)?
                else {
                    return Ok(None);
                };
                match formula {
                    Formula::And(..) => a.and(b),
                    Formula::Or(..) => a.or(b),
                    _ => Formula::Implies(Box::new(a), Box::new(b)),
                }
            }
            Formula::Not(a) => {
                let Some(a) =
                    self.interpret_value_formula(a, identity, index, observed, depth + 1)?
                else {
                    return Ok(None);
                };
                a.not()
            }
            _ => return Ok(None),
        };
        Ok(Some(result))
    }
}
