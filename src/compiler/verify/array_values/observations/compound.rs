//! Interpret a complete specialized Boolean formula, retaining its connectives.
//! In particular, a disjunction never licenses either of its branches alone.

use super::*;

impl Context<'_> {
    pub(super) fn observe_compound_values(
        &mut self,
        theorem: evidence::NodeId,
        variable: &str,
        body: &Formula,
        observed: &Observation<'_>,
        world: Option<state::WorldId>,
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
                        if contents.as_ref().is_some_and(|contents| {
                            contents.identity == observed.identity
                                && contents.fields.starts_with(observed.fields)
                        }) {
                            if let Some(term) = array_predicates::specialization_index(
                                &arguments[side],
                                observed.index,
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
            let Some(premise) =
                self.checked_array_specialization_in(theorem, &term, &instance, world)?
            else {
                continue;
            };
            let Some(interpretation) =
                self.interpret_value_formula(&instance, observed, theorem, world, 0)?
            else {
                continue;
            };
            if !interpretation.is_arithmetic() || self.checked_entails(&interpretation)? {
                continue;
            }
            self.import_scalar_observation(instance, interpretation, premise, &[])?;
        }
        Ok(())
    }

    fn interpret_value_formula(
        &mut self,
        formula: &Formula,
        observed: &Observation<'_>,
        theorem: evidence::NodeId,
        world: Option<state::WorldId>,
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
                // Whole payload interpretation is implication-only. It cannot
                // be substituted beneath negation or an implication antecedent.
                if key.0.as_ref().is_some_and(|contents| contents.whole)
                    || key.1.as_ref().is_some_and(|contents| contents.whole)
                {
                    return Ok(None);
                }
                for (side, contents) in [&key.0, &key.1].into_iter().enumerate() {
                    let Some(contents) = contents.as_ref().filter(|contents| {
                        contents.identity == observed.identity
                            && contents.fields.starts_with(observed.fields)
                    }) else {
                        continue;
                    };
                    if arguments.get(side) == Some(observed.index) {
                        self.charge_value_work(contents.fields.len() + 1)?;
                        let Some(value) = observed.project(contents)? else {
                            continue;
                        };
                        if !scalar(&value.ty()) {
                            continue;
                        }
                        return self.observed_scalar_equality(
                            formula,
                            &key,
                            side,
                            observed.index,
                            value,
                            Source { theorem, world },
                        );
                    }
                }
                return Ok(None);
            }
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                let Some(a) =
                    self.interpret_value_formula(a, observed, theorem, world, depth + 1)?
                else {
                    return Ok(None);
                };
                let Some(b) =
                    self.interpret_value_formula(b, observed, theorem, world, depth + 1)?
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
                    self.interpret_value_formula(a, observed, theorem, world, depth + 1)?
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
