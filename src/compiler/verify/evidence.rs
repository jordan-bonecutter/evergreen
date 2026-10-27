//! Append-only evidence for explicit propositional proof steps.
//!
//! Edges point to earlier nodes. Arithmetic certificates add edges for the
//! evidence rows they use, including evidence that closed discarded paths.
//! Known subject and row edges support scoped admission use. Unresolved
//! declaration summaries remain explicit; the full trust boundary is incomplete.

use super::*;

const MAX_NODES: usize = 20_000;
const MAX_EDGES: usize = 2_000_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct NodeId(usize);

impl NodeId {
    pub(super) fn key(self) -> u128 {
        self.0 as u128
    }
}

#[derive(Debug)]
struct Node {
    claim: Formula,
    parents: Vec<NodeId>,
    admission: bool,
    unresolved_context: bool,
    subjects: Option<subjects::Snapshot>,
}

#[derive(Default, Debug)]
pub(super) struct Evidence {
    nodes: Vec<Node>,
    edges: usize,
    claim_weight: usize,
}

impl Evidence {
    pub(super) fn claim(&self, id: NodeId) -> &Formula {
        &self.nodes[id.0].claim
    }

    pub(super) fn insert(
        &mut self,
        claim: Formula,
        mut parents: Vec<NodeId>,
        admission: bool,
    ) -> Result<NodeId> {
        parents.sort_unstable_by_key(|id| id.0);
        parents.dedup();
        if parents.iter().any(|id| id.0 >= self.nodes.len()) {
            return Err("proof evidence refers to a missing premise".into());
        }
        if self.nodes.len() >= MAX_NODES || parents.len() > MAX_EDGES.saturating_sub(self.edges) {
            return Err("proof evidence graph limit reached".into());
        }
        let mut weight = 0usize;
        let mut pending = vec![&claim];
        while let Some(part) = pending.pop() {
            weight = weight.saturating_add(1);
            match part {
                Formula::Ge(row) => weight = weight.saturating_add(row.terms.len()),
                Formula::Not(p) => pending.push(p),
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                _ => {}
            }
            if weight > MAX_VALUE_WORK.saturating_sub(self.claim_weight) {
                return Err("proof evidence claim storage limit reached".into());
            }
        }
        let id = NodeId(self.nodes.len());
        self.edges += parents.len();
        self.claim_weight += weight;
        self.nodes.push(Node {
            claim,
            parents,
            admission,
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
        let id = self.insert(claim, parents, false)?;
        // Complete declaration summaries (including their own admissions) are
        // still pending; never report this instantiation as fully traced.
        self.nodes[id.0].unresolved_context = true;
        Ok(id)
    }

    pub(super) fn arithmetic(&mut self, claim: Formula, support: paths::Support) -> Result<NodeId> {
        let id = self.insert(claim, support.parents.into_iter().collect(), false)?;
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
            if node.admission {
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
