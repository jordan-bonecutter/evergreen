//! Construct proofs of selector definitions from arithmetic guards and scoped
//! logical premises. Every connective and specialization uses kernel rules.

use super::*;

mod cases;
mod negative;

impl Context<'_> {
    pub(super) fn reduce_selector_formula(
        &mut self,
        goal: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        self.charge_value_work(goal.storage_weight()?)?;
        if depth >= 64 {
            return Err("selector proof reduction depth limit reached".into());
        }
        if goal.is_arithmetic() {
            let nodes = self.proof.witnesses.values().copied().collect::<Vec<_>>();
            self.charge_value_work(nodes.len())?;
            let mut local = paths::Paths::unit();
            let mut scoped = false;
            for node in nodes {
                if self.proof.evidence.check_closed(node).is_ok() {
                    continue;
                }
                self.charge_value_work(self.proof.evidence.claim(node)?.storage_weight()?)?;
                let claim = self.proof.evidence.claim(node)?.clone();
                if claim.is_arithmetic() {
                    scoped = true;
                    local = extend_from(
                        &local,
                        &claim,
                        false,
                        paths::Origin::Evidence(node),
                        self.session,
                        &mut self.work.value_work,
                    )?;
                }
            }
            let support = if scoped {
                self.probe_guard(&local, goal)?
            } else {
                None
            };
            let support = match support {
                Some(support) => Some(support),
                None => self.probe_guard(&self.proof.paths.clone(), goal)?,
            };
            return match support {
                Some(support) => {
                    self.work.obligations += 1;
                    self.proof
                        .evidence
                        .arithmetic(goal.clone(), support)
                        .map(Some)
                }
                None => Ok(None),
            };
        }
        if let Some(node) = self.logical_assumption(goal, None)? {
            return Ok(Some(node));
        }
        match goal {
            Formula::And(a, b) => {
                let Some(left) = self.reduce_selector_formula(a, depth + 1)? else {
                    return Ok(None);
                };
                let Some(right) = self.reduce_selector_formula(b, depth + 1)? else {
                    return Ok(None);
                };
                self.proof
                    .evidence
                    .derive(goal.clone(), evidence::Rule::AndIntro(left, right))
                    .map(Some)
            }
            Formula::Or(a, b) => {
                let rule = if let Some(left) = self.reduce_selector_formula(a, depth + 1)? {
                    evidence::Rule::OrLeft(left)
                } else if let Some(right) = self.reduce_selector_formula(b, depth + 1)? {
                    evidence::Rule::OrRight(right)
                } else {
                    return self.reduce_selector_choice(goal, a, b, depth + 1);
                };
                self.proof.evidence.derive(goal.clone(), rule).map(Some)
            }
            Formula::Not(body) => {
                if let Some(node) = self.scoped_selector_instance(goal, depth + 1)? {
                    return Ok(Some(node));
                }
                self.reduce_negative_selector(goal, body, depth + 1)
            }
            Formula::Predicate { symbol, .. } => {
                if let Some(node) = self.scoped_selector_instance(goal, depth + 1)? {
                    return Ok(Some(node));
                }
                let Some(&definition) = self.arrays.predicate_definitions.get(symbol) else {
                    return Ok(None);
                };
                let body = self.proof.evidence.predicate_definition(
                    definition,
                    goal,
                    &mut self.work.value_work,
                    MAX_VALUE_WORK,
                )?;
                let Some(premise) = self.reduce_selector_formula(&body, depth + 1)? else {
                    return Ok(None);
                };
                let implication = Formula::Implies(Box::new(body), Box::new(goal.clone()));
                let theorem = self.proof.evidence.derive(
                    implication,
                    evidence::Rule::UnfoldPredicate {
                        definition,
                        reverse: true,
                    },
                )?;
                self.proof
                    .evidence
                    .derive(
                        goal.clone(),
                        evidence::Rule::ImpElim {
                            theorem,
                            argument: premise,
                        },
                    )
                    .map(Some)
            }
            _ => Ok(None),
        }
    }

    pub(super) fn selector_contradiction(
        &mut self,
        first: evidence::NodeId,
        second: evidence::NodeId,
    ) -> Result<evidence::NodeId> {
        let a = self.proof.evidence.claim(first)?;
        let b = self.proof.evidence.claim(second)?;
        let same = |a: &Formula, b: &Formula| a.normalized().alpha_equal(&b.normalized());
        let rule = match (a, b) {
            (Formula::False, _) => evidence::Rule::Reuse(first),
            (_, Formula::False) => evidence::Rule::Reuse(second),
            (Formula::Not(inner), b) if same(inner, b) => evidence::Rule::ImpElim {
                theorem: first,
                argument: second,
            },
            (a, Formula::Not(inner)) if same(a, inner) => evidence::Rule::ImpElim {
                theorem: second,
                argument: first,
            },
            _ => {
                return Err(
                    "selector negation did not yield complementary checked propositions".into(),
                )
            }
        };
        self.proof.evidence.derive(Formula::False, rule)
    }

    fn scoped_selector_instance(
        &mut self,
        goal: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        let nodes = self.proof.witnesses.values().copied().collect::<Vec<_>>();
        self.charge_value_work(nodes.len())?;
        for theorem in nodes {
            // Generalize from explicit local premises, never automatically
            // carry an imported range across a write to its source plane.
            if self.proof.evidence.check_closed(theorem).is_ok() {
                continue;
            }
            self.charge_value_work(self.proof.evidence.claim(theorem)?.storage_weight()?)?;
            let Formula::Forall {
                variable,
                domain,
                body,
            } = self.proof.evidence.claim(theorem)?.clone()
            else {
                continue;
            };
            let Some(term) = observations::specialization_term(&body, goal, &variable)? else {
                continue;
            };
            let domain = domain.substitute(&variable, &term)?;
            let Some(domain) = self.reduce_selector_formula(&domain, depth + 1)? else {
                continue;
            };
            return self
                .proof
                .evidence
                .derive(
                    goal.clone(),
                    evidence::Rule::ForallElim {
                        theorem,
                        domain,
                        term,
                    },
                )
                .map(Some);
        }
        Ok(None)
    }
}
