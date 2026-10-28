//! Negated selector definitions use constructive contradiction rules. No
//! predicate is replaced by an unconstrained arithmetic Boolean.

use super::*;

impl Context<'_> {
    pub(super) fn reduce_negative_selector(
        &mut self,
        goal: &Formula,
        body: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        use evidence::Rule;
        let (hypothesis, contradiction) = match body {
            Formula::And(a, b) => {
                let selected = if let Some(node) =
                    self.reduce_selector_formula(&a.clone().not(), depth + 1)?
                {
                    Some((node, false))
                } else {
                    self.reduce_selector_formula(&b.clone().not(), depth + 1)?
                        .map(|node| (node, true))
                };
                let Some((negation, right)) = selected else {
                    let guard = if a.is_arithmetic() && !b.is_arithmetic() {
                        &**a
                    } else if b.is_arithmetic() && !a.is_arithmetic() {
                        &**b
                    } else {
                        return Ok(None);
                    };
                    return self.selector_arithmetic_cases(goal, guard, depth + 1);
                };
                let (hypothesis, conjunction) = self.proof.evidence.hypothesis(body.clone())?;
                let selected = self.proof.evidence.derive(
                    if right { *b.clone() } else { *a.clone() },
                    if right {
                        Rule::AndRight(conjunction)
                    } else {
                        Rule::AndLeft(conjunction)
                    },
                )?;
                let contradiction = self.selector_contradiction(negation, selected)?;
                (hypothesis, contradiction)
            }
            Formula::Or(a, b) => {
                let Some(left_not) = self.reduce_selector_formula(&a.clone().not(), depth + 1)?
                else {
                    return Ok(None);
                };
                let Some(right_not) = self.reduce_selector_formula(&b.clone().not(), depth + 1)?
                else {
                    return Ok(None);
                };
                let (hypothesis, source) = self.proof.evidence.hypothesis(body.clone())?;
                let (left_hypothesis, left) = self.proof.evidence.hypothesis(*a.clone())?;
                let (right_hypothesis, right) = self.proof.evidence.hypothesis(*b.clone())?;
                let left = self.selector_contradiction(left_not, left)?;
                let right = self.selector_contradiction(right_not, right)?;
                let contradiction = self.proof.evidence.derive(
                    Formula::False,
                    Rule::OrElim {
                        source,
                        left_hypothesis,
                        left,
                        right_hypothesis,
                        right,
                    },
                )?;
                (hypothesis, contradiction)
            }
            Formula::Predicate { symbol, .. } => {
                let Some(&definition) = self.arrays.predicate_definitions.get(symbol) else {
                    return Ok(None);
                };
                let expanded = self.proof.evidence.predicate_definition(
                    definition,
                    body,
                    &mut self.work.value_work,
                    MAX_VALUE_WORK,
                )?;
                let Some(negation) =
                    self.reduce_selector_formula(&expanded.clone().not(), depth + 1)?
                else {
                    return Ok(None);
                };
                let (hypothesis, premise) = self.proof.evidence.hypothesis(body.clone())?;
                let implication =
                    Formula::Implies(Box::new(body.clone()), Box::new(expanded.clone()));
                let theorem = self.proof.evidence.derive(
                    implication,
                    Rule::UnfoldPredicate {
                        definition,
                        reverse: false,
                    },
                )?;
                let argument = self.proof.evidence.derive(
                    expanded,
                    Rule::ImpElim {
                        theorem,
                        argument: premise,
                    },
                )?;
                let contradiction = self.selector_contradiction(negation, argument)?;
                (hypothesis, contradiction)
            }
            _ => return Ok(None),
        };
        self.proof
            .evidence
            .derive(
                goal.clone(),
                evidence::Rule::ImpIntro {
                    hypothesis,
                    body: contradiction,
                },
            )
            .map(Some)
    }
}
