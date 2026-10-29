//! Append-only evidence for explicit propositional proof steps.
//!
//! Edges point to earlier nodes. Arithmetic certificates add edges for the
//! evidence rows they use, including evidence that closed discarded paths.
//! Known subject and row edges support scoped admission use. Unresolved
//! declaration summaries remain explicit; the full trust boundary is incomplete.

use super::*;
use crate::compiler::certificate::TrustId;

mod definitions;
mod facts;
mod scalars;
pub(super) use definitions::DefinitionId;
use facts::{FactId, Facts};
pub(super) use scalars::BindingId;
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
    Admission(Option<TrustId>),
    ImportedTrust(TrustId),
    Reference {
        parents: Vec<NodeId>,
        pending: Option<summaries::Aspect>,
    },
    Hypothesis,
    Arithmetic {
        parents: Vec<NodeId>,
        context_variables: BTreeSet<String>,
    },
    Contract(Vec<NodeId>),
    AppliedContract {
        parents: Vec<NodeId>,
        context_variables: BTreeSet<String>,
    },
    Logical(Rule),
    #[cfg(test)]
    Fixture(Vec<NodeId>),
}

impl NodeRule {
    fn parents(&self) -> Vec<NodeId> {
        match self {
            Self::Admission(_) | Self::ImportedTrust(_) | Self::Hypothesis => vec![],
            Self::Reference { parents, .. } => parents.clone(),
            Self::Arithmetic { parents, .. }
            | Self::Contract(parents)
            | Self::AppliedContract { parents, .. } => parents.clone(),
            Self::Logical(rule) => rule.parents(),
            #[cfg(test)]
            Self::Fixture(parents) => parents.clone(),
        }
    }

    fn storage_weight(&self) -> usize {
        match self {
            Self::Arithmetic {
                context_variables, ..
            }
            | Self::AppliedContract {
                context_variables, ..
            } => context_variables
                .iter()
                .fold(0usize, |cost, name| cost.saturating_add(1 + name.len())),
            Self::Logical(rule) => rule.storage_weight(),
            _ => 0,
        }
    }
}

#[derive(Debug)]
struct Node {
    claim: Option<FactId>,
    rule: NodeRule,
    hypotheses: BTreeSet<HypothesisId>,
    weight: usize,
    parents: Vec<NodeId>,
    unresolved_context: bool,
    subjects: Option<subjects::Snapshot>,
    has_admissions: bool,
    has_pending_summaries: bool,
    has_opaque_context: bool,
}

#[derive(Default, Debug)]
pub(super) struct Evidence {
    definitions: definitions::Definitions,
    scalars: scalars::Definitions,
    nodes: Vec<Node>,
    facts: Facts,
    sources: BTreeMap<TrustId, NodeId>,
    edges: usize,
    storage_weight: usize,
    rule_work: usize,
    guards: BTreeMap<(NodeId, Formula), NodeId>,
}

impl Evidence {
    pub(super) fn claim(&self, id: NodeId) -> Result<&Formula> {
        self.nodes
            .get(id.0)
            .and_then(|node| node.claim)
            .map(|fact| self.facts.get(fact))
            .ok_or_else(|| "proof dependency source is not a proposition".into())
    }

    // This is a rejection filter, never evidence. Alpha-renaming and logical
    // normalization cannot introduce a predicate symbol absent from a fact.
    pub(super) fn claim_mentions_predicate(&self, id: NodeId, symbol: &str) -> bool {
        self.nodes
            .get(id.0)
            .and_then(|node| node.claim)
            .is_some_and(|fact| self.facts.mentions_predicate(fact, symbol))
    }

    // A negative result skips a lookup; a positive result proves nothing.
    pub(super) fn claim_may_project(&self, id: NodeId, normalized_goal: &Formula) -> bool {
        self.nodes
            .get(id.0)
            .and_then(|node| node.claim)
            .is_some_and(|fact| self.facts.may_project(fact, normalized_goal))
    }

    pub(super) fn admit_source(&mut self, claim: Formula, trust: TrustId) -> Result<NodeId> {
        let node = self.insert_node(
            Some(claim),
            NodeRule::Admission(Some(trust)),
            BTreeSet::new(),
        )?;
        self.sources.insert(trust, node);
        Ok(node)
    }

    #[cfg(test)]
    pub(super) fn admit(&mut self, claim: Formula) -> Result<NodeId> {
        self.insert_node(Some(claim), NodeRule::Admission(None), BTreeSet::new())
    }

    pub(super) fn import_trust(&mut self, trust: TrustId) -> Result<NodeId> {
        if let Some(&node) = self.sources.get(&trust) {
            return Ok(node);
        }
        let node = self.insert_node(None, NodeRule::ImportedTrust(trust), BTreeSet::new())?;
        self.sources.insert(trust, node);
        Ok(node)
    }

    pub(super) fn trust(&self, node: NodeId) -> Result<TrustId> {
        match self.nodes.get(node.0).map(|n| &n.rule) {
            Some(NodeRule::Admission(Some(trust)) | NodeRule::ImportedTrust(trust)) => Ok(*trust),
            _ => Err("admission has no source trust identity".into()),
        }
    }

    pub(super) fn reference(
        &mut self,
        parents: Vec<NodeId>,
        pending: Option<summaries::Aspect>,
    ) -> Result<NodeId> {
        let hypotheses = self.inherited_hypotheses(&parents)?;
        self.insert_node(None, NodeRule::Reference { parents, pending }, hypotheses)
    }

    pub(super) fn hypothesis(&mut self, claim: Formula) -> Result<(HypothesisId, NodeId)> {
        let id = NodeId(self.nodes.len());
        let h = HypothesisId { node: id };
        self.insert_node(Some(claim), NodeRule::Hypothesis, BTreeSet::from([h]))?;
        Ok((h, id))
    }

    pub(super) fn derive(&mut self, claim: Formula, rule: Rule) -> Result<NodeId> {
        // Projecting a freshly constructed pair needs only that component's
        // proof, preserving the dependencies actually used by elimination.
        let rule = match rule {
            Rule::AndLeft(parent) => match self.nodes.get(parent.0).map(|n| &n.rule) {
                Some(NodeRule::Logical(Rule::AndIntro(left, _))) => Rule::Reuse(*left),
                _ => Rule::AndLeft(parent),
            },
            Rule::AndRight(parent) => match self.nodes.get(parent.0).map(|n| &n.rule) {
                Some(NodeRule::Logical(Rule::AndIntro(_, right))) => Rule::Reuse(*right),
                _ => Rule::AndRight(parent),
            },
            rule => rule,
        };
        let weight = claim.storage_weight()?;
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
        work = work.saturating_add(rule.storage_weight());
        let limit = MAX_INFERENCE_WORK.saturating_sub(self.rule_work);
        let hypotheses = rule.check(self, &claim, &mut work, limit)?;
        if work > limit {
            return Err("logical inference work limit reached".into());
        }
        let id = self.insert_node(Some(claim), NodeRule::Logical(rule), hypotheses)?;
        self.rule_work += work;
        Ok(id)
    }

    pub(super) fn guard(&mut self, proof: NodeId, condition: &Formula) -> Result<NodeId> {
        if matches!(condition, Formula::True) {
            return Ok(proof);
        }
        if let Some(&node) = self.guards.get(&(proof, condition.clone())) {
            return Ok(node);
        }
        let body = self.claim(proof)?.clone();
        let (hypothesis, _) = self.hypothesis(condition.clone())?;
        let goal = Formula::Implies(Box::new(condition.clone()), Box::new(body));
        let node = self.derive(
            goal,
            Rule::ImpIntro {
                hypothesis,
                body: proof,
            },
        )?;
        self.guards.insert((proof, condition.clone()), node);
        Ok(node)
    }

    pub(super) fn guarded_condition(&self, node: NodeId) -> Option<Formula> {
        let NodeRule::Logical(Rule::ImpIntro { hypothesis, body }) = &self.nodes.get(node.0)?.rule
        else {
            return None;
        };
        let guard = self.claim(hypothesis.node).ok()?;
        (self.guards.get(&(*body, guard.clone())) == Some(&node)).then(|| guard.clone())
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
            self.insert_node(Some(claim), NodeRule::Fixture(parents), hypotheses)
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

    fn insert_node(
        &mut self,
        claim: Option<Formula>,
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
        let weight = claim
            .as_ref()
            .map(Formula::storage_weight)
            .transpose()?
            .unwrap_or(0);
        let fresh_formula = claim
            .as_ref()
            .is_some_and(|claim| self.facts.find(claim).is_none());
        let formula_storage = if fresh_formula { weight } else { 0 };
        let storage = formula_storage
            .saturating_add(hypotheses.len())
            .saturating_add(rule.storage_weight());
        if storage > MAX_VALUE_WORK.saturating_sub(self.storage_weight) {
            return Err("proof evidence claim storage limit reached".into());
        }
        if hypotheses.len() > 128 {
            return Err("proof evidence hypothesis limit reached".into());
        }
        let id = NodeId(self.nodes.len());
        self.edges += parents.len();
        self.storage_weight += storage;
        let claim = claim.map(|claim| self.facts.intern(claim));
        let has_admissions = matches!(rule, NodeRule::Admission(_) | NodeRule::ImportedTrust(_))
            || parents.iter().any(|id| self.nodes[id.0].has_admissions);
        let has_pending_summaries = matches!(
            rule,
            NodeRule::Reference {
                pending: Some(_),
                ..
            }
        ) || parents
            .iter()
            .any(|id| self.nodes[id.0].has_pending_summaries);
        let has_opaque_context = matches!(
            rule,
            NodeRule::Contract(_)
                | NodeRule::ImportedTrust(_)
                | NodeRule::Reference {
                    pending: Some(_),
                    ..
                }
        ) || parents.iter().any(|id| self.nodes[id.0].has_opaque_context);
        self.nodes.push(Node {
            claim,
            rule,
            hypotheses,
            weight,
            parents,
            unresolved_context: false,
            subjects: None,
            has_admissions,
            has_pending_summaries,
            has_opaque_context,
        });
        Ok(id)
    }

    pub(super) fn record_subjects(
        &mut self,
        node: NodeId,
        snapshot: subjects::Snapshot,
    ) -> Result<()> {
        self.check_closed(node)?;
        self.claim(node)?;
        if self.nodes[node.0].subjects.is_some() {
            return Err("proof node already has state subjects".into());
        }
        let weight = snapshot.storage_weight()?;
        if weight > MAX_VALUE_WORK.saturating_sub(self.storage_weight) {
            return Err("proof evidence subject storage limit reached".into());
        }
        self.storage_weight += weight;
        self.nodes[node.0].subjects = Some(snapshot);
        Ok(())
    }

    pub(super) fn subjects(&self, node: NodeId) -> Option<&subjects::Snapshot> {
        self.nodes[node.0].subjects.as_ref()
    }

    /// These flags depend only on immutable parent edges and rule kinds.
    /// Subject attachment can change completeness, but never these flags.
    pub(super) fn has_admissions(&self, node: NodeId) -> bool {
        self.nodes[node.0].has_admissions
    }

    pub(super) fn has_pending_summaries(&self, node: NodeId) -> bool {
        self.nodes[node.0].has_pending_summaries
    }

    // Rejection-only hint: universal introduction still checks freshness.
    pub(super) fn has_opaque_context(&self, node: NodeId) -> bool {
        self.nodes[node.0].has_opaque_context
    }

    pub(super) fn contract(&mut self, claim: Formula, parents: Vec<NodeId>) -> Result<NodeId> {
        let hypotheses = self.inherited_hypotheses(&parents)?;
        let id = self.insert_node(Some(claim), NodeRule::Contract(parents), hypotheses)?;
        // Complete declaration summaries (including their own admissions) are
        // still pending; never report this instantiation as fully traced.
        self.nodes[id.0].unresolved_context = true;
        Ok(id)
    }

    /// A verified, non-recursive call has fixed actual inputs. Its precondition
    /// proof and declaration trust summary are parents; the claim and control
    /// variables remain visible to universal freshness checking.
    pub(super) fn applied_contract(
        &mut self,
        claim: Formula,
        parents: Vec<NodeId>,
        control: &Formula,
    ) -> Result<NodeId> {
        let mut context_variables = claim.free_variables()?;
        context_variables.extend(control.free_variables()?);
        let hypotheses = self.inherited_hypotheses(&parents)?;
        self.insert_node(
            Some(claim),
            NodeRule::AppliedContract {
                parents,
                context_variables,
            },
            hypotheses,
        )
    }

    pub(super) fn arithmetic(&mut self, claim: Formula, support: paths::Support) -> Result<NodeId> {
        let parents = support.parents.into_iter().collect::<Vec<_>>();
        let hypotheses = self.inherited_hypotheses(&parents)?;
        let rule = NodeRule::Arithmetic {
            parents,
            context_variables: support.context_variables,
        };
        let id = self.insert_node(Some(claim), rule, hypotheses)?;
        self.nodes[id.0].unresolved_context = support.unresolved;
        Ok(id)
    }

    /// Historical dependencies remain meaningful after lexical witnesses leave
    /// scope. Traverse iteratively and visit shared premises only once.
    pub(super) fn admissions(&self, root: NodeId) -> AdmissionDependencies {
        self.admissions_many(&[root])
    }

    /// A declaration exports the union of its used roots. Shared subproofs
    /// need only one visit, regardless of how many obligations reuse them.
    pub(super) fn admissions_many(&self, roots: &[NodeId]) -> AdmissionDependencies {
        let mut pending = roots.to_vec();
        let mut seen = BTreeSet::new();
        let mut admissions = BTreeSet::new();
        let mut complete = true;
        let mut pending_summaries = BTreeSet::new();
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
            if let NodeRule::Reference {
                pending: Some(aspect),
                ..
            } = node.rule
            {
                pending_summaries.insert(aspect);
                complete = false;
            }
            if matches!(
                node.rule,
                NodeRule::Admission(_) | NodeRule::ImportedTrust(_)
            ) {
                admissions.insert(id);
            }
            pending.extend(node.parents.iter().copied());
        }
        AdmissionDependencies {
            admissions,
            pending_summaries,
            complete,
            work,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(super) struct AdmissionDependencies {
    pub(super) admissions: BTreeSet<NodeId>,
    pub(super) pending_summaries: BTreeSet<summaries::Aspect>,
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
    fn declaration_roots_share_dependency_traversal_without_losing_trust() {
        let mut graph = Evidence::default();
        let used = graph.insert(Formula::True, vec![], true).unwrap();
        let unused = graph.insert(Formula::False, vec![], true).unwrap();
        let mut shared = used;
        for _ in 0..100 {
            shared = graph.insert(Formula::True, vec![shared], false).unwrap();
        }
        let roots = (0..100)
            .map(|_| graph.insert(Formula::True, vec![shared], false).unwrap())
            .collect::<Vec<_>>();
        let separately = roots
            .iter()
            .map(|&root| graph.admissions(root).work)
            .sum::<usize>();
        let combined = graph.admissions_many(&roots);
        assert_eq!(combined.admissions, BTreeSet::from([used]));
        assert!(!combined.admissions.contains(&unused));
        assert!(combined.work < separately / 10);
        let pending = graph
            .reference(vec![shared], Some(summaries::Aspect::Contract))
            .unwrap();
        let mixed = graph.admissions_many(&[roots[0], pending]);
        assert_eq!(mixed.admissions, BTreeSet::from([used]));
        assert_eq!(
            mixed.pending_summaries,
            BTreeSet::from([summaries::Aspect::Contract])
        );
        assert!(!mixed.complete);
        for index in 0..graph.nodes.len() {
            let node = NodeId(index);
            let dependencies = graph.admissions(node);
            assert_eq!(
                graph.has_admissions(node),
                !dependencies.admissions.is_empty()
            );
            assert_eq!(
                graph.has_pending_summaries(node),
                !dependencies.pending_summaries.is_empty()
            );
        }
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
            storage_weight: MAX_VALUE_WORK,
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
        assert_eq!(graph.storage_weight, 1);
        assert!(graph.insert(Formula::True, vec![], false).is_err());
    }

    #[test]
    fn a_stored_proposition_is_not_evidence_for_itself() {
        let mut graph = Evidence::default();
        let false_fact = graph.facts.intern(Formula::False);
        assert_eq!(graph.facts.get(false_fact), &Formula::False);
        assert!(graph.nodes.is_empty());
        assert!(graph
            .derive(Formula::False, Rule::Reuse(NodeId(0)))
            .is_err());
        assert!(graph.nodes.is_empty());
    }

    #[test]
    fn shared_conclusions_preserve_distinct_proof_and_admission_identities() {
        let mut graph = Evidence::default();
        let first = graph.admit(Formula::False).unwrap();
        let reused = graph.derive(Formula::False, Rule::Reuse(first)).unwrap();
        let second = graph.admit(Formula::False).unwrap();
        assert_ne!(first, reused);
        assert_ne!(first, second);
        assert_eq!(graph.nodes[first.0].claim, graph.nodes[reused.0].claim);
        assert_eq!(graph.nodes[first.0].claim, graph.nodes[second.0].claim);
        assert_eq!(graph.storage_weight, 1);
        assert_eq!(graph.admissions(reused).admissions, BTreeSet::from([first]));
        assert_eq!(
            graph.admissions(second).admissions,
            BTreeSet::from([second])
        );
    }

    #[test]
    fn shared_formula_storage_does_not_bypass_hypothesis_or_fresh_formula_limits() {
        let mut graph = Evidence {
            storage_weight: MAX_VALUE_WORK - 1,
            ..Evidence::default()
        };
        let proof = graph.admit(Formula::False).unwrap();
        assert_eq!(graph.storage_weight, MAX_VALUE_WORK);
        graph.derive(Formula::False, Rule::Reuse(proof)).unwrap();
        let nodes = graph.nodes.len();
        assert!(graph.hypothesis(Formula::False).is_err());
        assert!(graph.admit(Formula::True).is_err());
        assert_eq!(graph.nodes.len(), nodes);
        assert!(graph.facts.find(&Formula::True).is_none());
    }
}
