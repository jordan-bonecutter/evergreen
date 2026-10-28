//! Propositional inference checking. Tactics choose rules; this module checks
//! their conclusions and tracks hypotheses until an introduction/cases rule
//! discharges them. Arithmetic and declaration imports remain separate leaves.

use super::*;

#[cfg(test)]
mod predicate_tests;
#[cfg(test)]
mod quantified_tests;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::compiler::verify) struct HypothesisId {
    pub(super) node: NodeId,
}

#[derive(Clone, Debug)]
pub(in crate::compiler::verify) enum Rule {
    Reuse(NodeId),
    AndIntro(NodeId, NodeId),
    AndLeft(NodeId),
    AndRight(NodeId),
    OrLeft(NodeId),
    OrRight(NodeId),
    ImpIntro {
        hypothesis: HypothesisId,
        body: NodeId,
    },
    ImpElim {
        theorem: NodeId,
        argument: NodeId,
    },
    OrElim {
        source: NodeId,
        left_hypothesis: HypothesisId,
        left: NodeId,
        right_hypothesis: HypothesisId,
        right: NodeId,
    },
    FalseElim(NodeId),
    ForallIntro {
        hypothesis: HypothesisId,
        body: NodeId,
        eigenvariable: String,
    },
    ForallElim {
        theorem: NodeId,
        domain: NodeId,
        term: Linear,
    },
    // Source indexed-memory elaboration will construct this congruence step.
    #[allow(dead_code)]
    PredicateCongruence {
        source: NodeId,
        equalities: Vec<NodeId>,
    },
    UnfoldPredicate {
        definition: DefinitionId,
        reverse: bool,
    },
}

impl Rule {
    pub(super) fn parents(&self) -> Vec<NodeId> {
        match *self {
            Self::UnfoldPredicate { .. } => vec![],
            Self::Reuse(p)
            | Self::AndLeft(p)
            | Self::AndRight(p)
            | Self::OrLeft(p)
            | Self::OrRight(p)
            | Self::FalseElim(p) => vec![p],
            Self::AndIntro(a, b) => vec![a, b],
            Self::ImpIntro { hypothesis, body } => vec![hypothesis.node, body],
            Self::ImpElim { theorem, argument } => vec![theorem, argument],
            Self::OrElim {
                source,
                left_hypothesis,
                left,
                right_hypothesis,
                right,
            } => vec![
                source,
                left_hypothesis.node,
                left,
                right_hypothesis.node,
                right,
            ],
            Self::ForallIntro {
                hypothesis, body, ..
            } => vec![hypothesis.node, body],
            Self::ForallElim {
                theorem, domain, ..
            } => vec![theorem, domain],
            Self::PredicateCongruence {
                source,
                ref equalities,
            } => std::iter::once(source)
                .chain(equalities.iter().copied())
                .collect(),
        }
    }

    pub(super) fn storage_weight(&self) -> usize {
        match self {
            Self::ForallIntro { eigenvariable, .. } => 1usize.saturating_add(eigenvariable.len()),
            Self::ForallElim { term, .. } => term
                .terms
                .keys()
                .fold(1usize, |cost, name| cost.saturating_add(1 + name.len())),
            Self::PredicateCongruence { equalities, .. } => equalities.len(),
            _ => 0,
        }
    }

    pub(super) fn check(
        &self,
        graph: &Evidence,
        goal: &Formula,
        work: &mut usize,
        limit: usize,
    ) -> Result<BTreeSet<HypothesisId>> {
        // Validate all references before any indexing, including binder IDs.
        let parents = self.parents();
        if parents.iter().any(|id| id.0 >= graph.nodes.len()) {
            return Err("logical rule refers to a missing premise".into());
        }
        let mut open: BTreeSet<HypothesisId> = BTreeSet::new();
        for parent in &parents {
            open.extend(&graph.nodes[parent.0].hypotheses);
        }
        let claim = |id| graph.claim(id);
        let same = |a: &Formula, b: &Formula| a.normalized().alpha_equal(&b.normalized());
        let hypothesis = |id: HypothesisId| -> Result<&Formula> {
            if !matches!(graph.nodes[id.node.0].rule, NodeRule::Hypothesis) {
                return Err("logical rule binder is not a hypothesis".into());
            }
            claim(id.node)
        };
        let valid = match *self {
            Self::UnfoldPredicate {
                definition,
                reverse,
            } => match goal {
                Formula::Implies(a, b) => {
                    let (atom, body) = if reverse { (b, a) } else { (a, b) };
                    same(
                        &graph.predicate_definition(definition, atom, work, limit)?,
                        body,
                    )
                }
                _ => false,
            },
            Self::Reuse(p) => same(claim(p)?, goal),
            Self::AndIntro(a, b) => {
                matches!(goal, Formula::And(x, y) if same(claim(a)?, x) && same(claim(b)?, y))
            }
            Self::AndLeft(p) => matches!(claim(p)?, Formula::And(a, _) if same(a, goal)),
            Self::AndRight(p) => matches!(claim(p)?, Formula::And(_, b) if same(b, goal)),
            Self::OrLeft(p) => matches!(goal, Formula::Or(a, _) if same(claim(p)?, a)),
            Self::OrRight(p) => matches!(goal, Formula::Or(_, b) if same(claim(p)?, b)),
            Self::FalseElim(p) => matches!(claim(p)?, Formula::False),
            Self::ImpElim { theorem, argument } => match claim(theorem)? {
                Formula::Implies(a, b) => same(a, claim(argument)?) && same(b, goal),
                Formula::Not(a) => same(a, claim(argument)?) && same(goal, &Formula::False),
                _ => false,
            },
            Self::ImpIntro {
                hypothesis: h,
                body,
            } => {
                let premise = hypothesis(h)?;
                open.remove(&h);
                match goal {
                    Formula::Implies(a, b) => same(a, premise) && same(b, claim(body)?),
                    Formula::Not(a) => same(a, premise) && same(claim(body)?, &Formula::False),
                    _ => false,
                }
            }
            Self::OrElim {
                source,
                left_hypothesis: lh,
                left,
                right_hypothesis: rh,
                right,
            } => {
                let lp = hypothesis(lh)?;
                let rp = hypothesis(rh)?;
                // Each branch may assume only its own case. Neither binder may
                // justify the source disjunction that licenses the split.
                let scoped = lh != rh
                    && !graph.nodes[source.0].hypotheses.contains(&lh)
                    && !graph.nodes[source.0].hypotheses.contains(&rh)
                    && !graph.nodes[left.0].hypotheses.contains(&rh)
                    && !graph.nodes[right.0].hypotheses.contains(&lh);
                open.remove(&lh);
                open.remove(&rh);
                scoped
                    && same(claim(left)?, goal)
                    && same(claim(right)?, goal)
                    && matches!(claim(source)?, Formula::Or(a, b) if same(a, lp) && same(b, rp))
            }
            Self::ForallIntro {
                hypothesis: h,
                body,
                ref eigenvariable,
            } => {
                let premise = hypothesis(h)?;
                open.remove(&h);
                match goal {
                    Formula::Forall {
                        variable,
                        domain,
                        body: consequence,
                    } => {
                        if eigenvariable.is_empty() || eigenvariable.len() > 256 {
                            return Err("invalid universal eigenvariable".into());
                        }
                        let value = Linear::variable(eigenvariable);
                        let expected_domain = domain.substitute(variable, &value)?;
                        let expected_body = consequence.substitute(variable, &value)?;
                        let mut fresh = !goal.free_variables()?.contains(eigenvariable);
                        for other in &open {
                            *work = work
                                .saturating_add(graph.nodes[other.node.0].weight.saturating_mul(2));
                            if *work > limit {
                                return Err("universal freshness work limit reached".into());
                            }
                            fresh &= !hypothesis(*other)?
                                .free_variables()?
                                .contains(eigenvariable);
                        }
                        fresh &= graph.eigenvariable_is_fresh(body, eigenvariable, work, limit)?;
                        fresh
                            && same(premise, &expected_domain)
                            && same(claim(body)?, &expected_body)
                    }
                    _ => false,
                }
            }
            Self::ForallElim {
                theorem,
                domain,
                ref term,
            } => match claim(theorem)? {
                Formula::Forall {
                    variable,
                    domain: bounds,
                    body,
                } => {
                    same(claim(domain)?, &bounds.substitute(variable, term)?)
                        && same(goal, &body.substitute(variable, term)?)
                }
                _ => false,
            },
            Self::PredicateCongruence {
                source,
                ref equalities,
            } => match (claim(source)?, goal) {
                (
                    Formula::Predicate {
                        symbol: a,
                        arguments: aa,
                    },
                    Formula::Predicate {
                        symbol: b,
                        arguments: ba,
                    },
                ) if a == b && aa.len() == ba.len() && aa.len() == equalities.len() => {
                    let mut valid = true;
                    for ((from, to), proof) in aa.iter().zip(ba).zip(equalities) {
                        valid &= same(claim(*proof)?, &equal(from, to)?);
                    }
                    valid
                }
                _ => false,
            },
        };
        if !valid {
            return Err("logical rule does not establish its claimed conclusion".into());
        }
        Ok(open)
    }
}

impl Evidence {
    // Conclusions may mention the eigenvariable; external assumptions may not.
    // Discharged hypotheses stay inside the DAG, so only the root's open
    // hypotheses are checked by ForallIntro above.
    fn eigenvariable_is_fresh(
        &self,
        root: NodeId,
        variable: &str,
        work: &mut usize,
        limit: usize,
    ) -> Result<bool> {
        let mut pending = vec![root];
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !seen.insert(id) {
                continue;
            }
            let node = self
                .nodes
                .get(id.0)
                .ok_or("missing universal proof dependency")?;
            *work = work.saturating_add(1 + node.parents.len() + node.rule.storage_weight());
            if *work > limit {
                return Err("universal freshness work limit reached".into());
            }
            match &node.rule {
                NodeRule::Arithmetic {
                    context_variables, ..
                } => {
                    if context_variables.contains(variable) {
                        return Ok(false);
                    }
                }
                NodeRule::ImportedTrust(_)
                | NodeRule::Contract(_)
                | NodeRule::Reference {
                    pending: Some(_), ..
                } => {
                    return Err(
                        "universal introduction requires fully traced context dependencies".into(),
                    );
                }
                NodeRule::Admission(_) => {
                    *work = work.saturating_add(node.weight.saturating_mul(2));
                    if *work > limit {
                        return Err("universal freshness work limit reached".into());
                    }
                    if self.claim(id)?.free_variables()?.contains(variable) {
                        return Ok(false);
                    }
                }
                _ => {}
            }
            pending.extend(&node.parents);
        }
        Ok(true)
    }
}
