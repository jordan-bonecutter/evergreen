//! Propositional inference checking. Tactics choose rules; this module checks
//! their conclusions and tracks hypotheses until an introduction/cases rule
//! discharges them. Arithmetic and declaration imports remain separate leaves.

use super::*;

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
}

impl Rule {
    pub(super) fn parents(&self) -> Vec<NodeId> {
        match *self {
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
        }
    }

    pub(super) fn check(&self, graph: &Evidence, goal: &Formula) -> Result<BTreeSet<HypothesisId>> {
        // Validate all references before any indexing, including binder IDs.
        let parents = self.parents();
        if parents.iter().any(|id| id.0 >= graph.nodes.len()) {
            return Err("logical rule refers to a missing premise".into());
        }
        let mut open = BTreeSet::new();
        for parent in &parents {
            open.extend(&graph.nodes[parent.0].hypotheses);
        }
        let claim = |id| graph.claim(id);
        let same = |a: &Formula, b: &Formula| a.normalized() == b.normalized();
        let hypothesis = |id: HypothesisId| -> Result<&Formula> {
            if !matches!(graph.nodes[id.node.0].rule, NodeRule::Hypothesis) {
                return Err("logical rule binder is not a hypothesis".into());
            }
            Ok(claim(id.node))
        };
        let valid = match *self {
            Self::Reuse(p) => same(claim(p), goal),
            Self::AndIntro(a, b) => {
                matches!(goal, Formula::And(x, y) if same(claim(a), x) && same(claim(b), y))
            }
            Self::AndLeft(p) => matches!(claim(p), Formula::And(a, _) if same(a, goal)),
            Self::AndRight(p) => matches!(claim(p), Formula::And(_, b) if same(b, goal)),
            Self::OrLeft(p) => matches!(goal, Formula::Or(a, _) if same(claim(p), a)),
            Self::OrRight(p) => matches!(goal, Formula::Or(_, b) if same(claim(p), b)),
            Self::FalseElim(p) => matches!(claim(p), Formula::False),
            Self::ImpElim { theorem, argument } => match claim(theorem) {
                Formula::Implies(a, b) => same(a, claim(argument)) && same(b, goal),
                Formula::Not(a) => same(a, claim(argument)) && same(goal, &Formula::False),
                _ => false,
            },
            Self::ImpIntro {
                hypothesis: h,
                body,
            } => {
                let premise = hypothesis(h)?;
                open.remove(&h);
                match goal {
                    Formula::Implies(a, b) => same(a, premise) && same(b, claim(body)),
                    Formula::Not(a) => same(a, premise) && same(claim(body), &Formula::False),
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
                    && same(claim(left), goal)
                    && same(claim(right), goal)
                    && matches!(claim(source), Formula::Or(a, b) if same(a, lp) && same(b, rp))
            }
        };
        if !valid {
            return Err("logical rule does not establish its claimed conclusion".into());
        }
        Ok(open)
    }
}
