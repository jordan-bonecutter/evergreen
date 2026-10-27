//! Append-only evidence for explicit propositional proof steps.
//!
//! Edges point to earlier nodes. Arithmetic certificates add edges for the
//! evidence rows they use, including evidence that closed discarded paths.
//! Known subject and row edges support scoped admission use. Unresolved
//! declaration summaries remain explicit; the full trust boundary is incomplete.

use super::*;

mod rules;
pub(super) use rules::{HypothesisId, Rule};

const MAX_NODES: usize = 20_000;
const MAX_EDGES: usize = 2_000_000;
const MAX_INFERENCE_WORK: usize = 2_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct NodeId(usize);

impl NodeId {
    pub(super) fn key(self) -> u128 {
        self.0 as u128
    }
}

#[derive(Debug)]
enum NodeRule {
    Admission,
    Hypothesis,
    Arithmetic(Vec<NodeId>),
    Contract(Vec<NodeId>),
    Logical(Rule),
    #[cfg(test)]
    Fixture(Vec<NodeId>),
}

impl NodeRule {
    fn parents(&self) -> Vec<NodeId> {
        match self {
            Self::Admission | Self::Hypothesis => vec![],
            Self::Arithmetic(parents) | Self::Contract(parents) => parents.clone(),
            Self::Logical(rule) => rule.parents(),
            #[cfg(test)]
            Self::Fixture(parents) => parents.clone(),
        }
    }
}

#[derive(Debug)]
struct Node {
    claim: Formula,
    rule: NodeRule,
    hypotheses: BTreeSet<HypothesisId>,
    weight: usize,
    parents: Vec<NodeId>,
    unresolved_context: bool,
    subjects: Option<subjects::Snapshot>,
}

#[derive(Default, Debug)]
pub(super) struct Evidence {
    nodes: Vec<Node>,
    edges: usize,
    claim_weight: usize,
    rule_work: usize,
}

impl Evidence {
    pub(super) fn claim(&self, id: NodeId) -> &Formula {
        &self.nodes[id.0].claim
    }

    /// Only explicit admissions and checked imports can create leaf evidence.
    pub(super) fn admit(&mut self, claim: Formula) -> Result<NodeId> {
        self.insert_node(claim, NodeRule::Admission, BTreeSet::new())
    }

    pub(super) fn hypothesis(&mut self, claim: Formula) -> Result<(HypothesisId, NodeId)> {
        let id = NodeId(self.nodes.len());
        let h = HypothesisId { node: id };
        self.insert_node(claim, NodeRule::Hypothesis, BTreeSet::from([h]))?;
        Ok((h, id))
    }

    pub(super) fn derive(&mut self, claim: Formula, rule: Rule) -> Result<NodeId> {
        let weight = Self::claim_weight(&claim)?;
        let mut work = weight;
        for parent in rule.parents() {
            let node = self
                .nodes
                .get(parent.0)
                .ok_or("logical rule refers to a missing premise")?;
            work = work
                .saturating_add(node.weight)
                .saturating_add(node.hypotheses.len());
        }
        if work > MAX_INFERENCE_WORK.saturating_sub(self.rule_work) {
            return Err("logical inference work limit reached".into());
        }
        let hypotheses = rule.check(self, &claim)?;
        let id = self.insert_node(claim, NodeRule::Logical(rule), hypotheses)?;
        self.rule_work += work;
        Ok(id)
    }

    pub(super) fn check_closed(&self, id: NodeId) -> Result<()> {
        let node = self
            .nodes
            .get(id.0)
            .ok_or("proof refers to a missing node")?;
        if !node.hypotheses.is_empty() {
            return Err("proof contains undischarged hypotheses".into());
        }
        Ok(())
    }

    // Synthetic origins for graph/provenance tests. Production code must use
    // a specific import boundary or a checked inference rule.
    #[cfg(test)]
    pub(super) fn insert(
        &mut self,
        claim: Formula,
        parents: Vec<NodeId>,
        admission: bool,
    ) -> Result<NodeId> {
        if admission {
            assert!(parents.is_empty());
            self.admit(claim)
        } else {
            let hypotheses = self.inherited_hypotheses(&parents)?;
            self.insert_node(claim, NodeRule::Fixture(parents), hypotheses)
        }
    }

    fn inherited_hypotheses(&self, parents: &[NodeId]) -> Result<BTreeSet<HypothesisId>> {
        let mut hypotheses = BTreeSet::new();
        for parent in parents {
            let node = self
                .nodes
                .get(parent.0)
                .ok_or("proof evidence refers to a missing premise")?;
            hypotheses.extend(&node.hypotheses);
        }
        Ok(hypotheses)
    }

    fn claim_weight(claim: &Formula) -> Result<usize> {
        let mut weight = 0usize;
        let mut pending = vec![(claim, 0usize)];
        while let Some((part, depth)) = pending.pop() {
            if depth >= 128 {
                return Err("proof evidence claim depth limit reached".into());
            }
            weight = weight.saturating_add(1);
            match part {
                Formula::Ge(row) => weight = weight.saturating_add(row.terms.len()),
                Formula::Not(p) => pending.push((p, depth + 1)),
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    pending.push((a, depth + 1));
                    pending.push((b, depth + 1));
                }
                _ => {}
            }
            if weight > MAX_VALUE_WORK {
                return Err("proof evidence claim storage limit reached".into());
            }
        }
        Ok(weight)
    }

    fn insert_node(
        &mut self,
        claim: Formula,
        rule: NodeRule,
        hypotheses: BTreeSet<HypothesisId>,
    ) -> Result<NodeId> {
        let mut parents = rule.parents();
        parents.sort_unstable_by_key(|id| id.0);
        parents.dedup();
        if parents.iter().any(|id| id.0 >= self.nodes.len()) {
            return Err("proof evidence refers to a missing premise".into());
        }
        if self.nodes.len() >= MAX_NODES || parents.len() > MAX_EDGES.saturating_sub(self.edges) {
            return Err("proof evidence graph limit reached".into());
        }
        let weight = Self::claim_weight(&claim)?;
        let storage = weight.saturating_add(hypotheses.len());
        if storage > MAX_VALUE_WORK.saturating_sub(self.claim_weight) {
            return Err("proof evidence claim storage limit reached".into());
        }
        if hypotheses.len() > 128 {
            return Err("proof evidence hypothesis limit reached".into());
        }
        let id = NodeId(self.nodes.len());
        self.edges += parents.len();
        self.claim_weight += storage;
        self.nodes.push(Node {
            claim,
            rule,
            hypotheses,
            weight,
            parents,
            unresolved_context: false,
            subjects: None,
        });
        Ok(id)
    }

    pub(super) fn record_subjects(
        &mut self,
        node: NodeId,
        snapshot: subjects::Snapshot,
    ) -> Result<()> {
        self.check_closed(node)?;
        if self.nodes[node.0].subjects.is_some() {
            return Err("proof node already has state subjects".into());
        }
        if snapshot.reads.len() > MAX_VALUE_WORK.saturating_sub(self.claim_weight) {
            return Err("proof evidence subject storage limit reached".into());
        }
        self.claim_weight += snapshot.reads.len();
        self.nodes[node.0].subjects = Some(snapshot);
        Ok(())
    }

    pub(super) fn subjects(&self, node: NodeId) -> Option<&subjects::Snapshot> {
        self.nodes[node.0].subjects.as_ref()
    }

    pub(super) fn contract(&mut self, claim: Formula, parents: Vec<NodeId>) -> Result<NodeId> {
        let hypotheses = self.inherited_hypotheses(&parents)?;
        let id = self.insert_node(claim, NodeRule::Contract(parents), hypotheses)?;
        // Complete declaration summaries (including their own admissions) are
        // still pending; never report this instantiation as fully traced.
        self.nodes[id.0].unresolved_context = true;
        Ok(id)
    }

    pub(super) fn arithmetic(&mut self, claim: Formula, support: paths::Support) -> Result<NodeId> {
        let parents = support.parents.into_iter().collect::<Vec<_>>();
        let hypotheses = self.inherited_hypotheses(&parents)?;
        let id = self.insert_node(claim, NodeRule::Arithmetic(parents), hypotheses)?;
        self.nodes[id.0].unresolved_context = support.unresolved;
        Ok(id)
    }

    /// Historical dependencies remain meaningful after lexical witnesses leave
    /// scope. Traverse iteratively and visit shared premises only once.
    pub(super) fn admissions(&self, root: NodeId) -> AdmissionDependencies {
        let mut pending = vec![root];
        let mut seen = BTreeSet::new();
        let mut admissions = BTreeSet::new();
        let mut complete = true;
        let mut work = 0usize;
        while let Some(id) = pending.pop() {
            work = work.saturating_add(1);
            if !seen.insert(id.0) {
                continue;
            }
            let node = &self.nodes[id.0];
            complete &= !node.unresolved_context;
            if let Some(subjects) = &node.subjects {
                complete &= subjects.complete;
            }
            if matches!(node.rule, NodeRule::Admission) {
                admissions.insert(id);
            }
            pending.extend(node.parents.iter().copied());
        }
        AdmissionDependencies {
            admissions,
            complete,
            work,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct AdmissionDependencies {
    pub(super) admissions: BTreeSet<NodeId>,
    pub(super) complete: bool,
    pub(super) work: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dependencies_follow_edges_instead_of_all_available_admissions() {
        let mut graph = Evidence::default();
        let unused = graph.insert(Formula::False, vec![], true).unwrap();
        let used = graph.insert(Formula::True, vec![], true).unwrap();
        let left = graph.insert(Formula::True, vec![used], false).unwrap();
        let right = graph.insert(Formula::True, vec![used], false).unwrap();
        let root = graph
            .insert(Formula::True, vec![left, right, left], false)
            .unwrap();
        assert_eq!(graph.admissions(root).admissions, BTreeSet::from([used]));
        assert!(!graph.admissions(root).admissions.contains(&unused));
        assert_eq!(graph.nodes[root.0].parents, vec![left, right]);
    }

    #[test]
    fn unresolved_arithmetic_context_cannot_appear_admission_free() {
        let mut graph = Evidence::default();
        let leaf = graph
            .arithmetic(
                Formula::True,
                paths::Support {
                    unresolved: true,
                    ..paths::Support::default()
                },
            )
            .unwrap();
        let root = graph.insert(Formula::True, vec![leaf], false).unwrap();
        let dependencies = graph.admissions(root);
        assert!(dependencies.admissions.is_empty());
        assert!(!dependencies.complete);
    }

    #[test]
    fn invalid_edges_do_not_partially_mutate_graph() {
        let mut graph = Evidence::default();
        assert!(graph.insert(Formula::True, vec![NodeId(0)], false).is_err());
        assert_eq!(graph.nodes.len(), 0);
        assert_eq!(graph.edges, 0);
    }

    #[test]
    fn oversized_claims_are_rejected_before_insertion() {
        let mut graph = Evidence {
            claim_weight: MAX_VALUE_WORK,
            ..Evidence::default()
        };
        assert!(graph.insert(Formula::True, vec![], false).is_err());
        assert!(graph.nodes.is_empty());
        assert_eq!(graph.edges, 0);
    }

    #[test]
    fn deep_proof_chains_do_not_recurse_or_copy_transitive_dependencies() {
        let mut graph = Evidence::default();
        let source = graph.insert(Formula::True, vec![], true).unwrap();
        let mut root = source;
        for _ in 1..MAX_NODES {
            root = graph.insert(Formula::True, vec![root], false).unwrap();
        }
        assert_eq!(graph.admissions(root).admissions, BTreeSet::from([source]));
        assert_eq!(graph.edges, MAX_NODES - 1);
        assert!(graph.insert(Formula::True, vec![], false).is_err());
    }
}
