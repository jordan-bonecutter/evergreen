//! Immutable proposition storage. Interning a formula establishes no truth;
//! only the evidence arena can create a proof concluding one of these facts.

use super::Formula;
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct FactId(usize);

#[derive(Default, Debug)]
pub(super) struct Facts {
    entries: Vec<Arc<Formula>>,
    by_formula: BTreeMap<Arc<Formula>, FactId>,
    predicates: Vec<BTreeSet<String>>,
    projectable_shapes: Vec<u16>,
}

fn shape(formula: &Formula) -> u16 {
    match formula {
        Formula::True => 1,
        Formula::False => 2,
        Formula::Ge(_) => 4,
        Formula::And(..) => 8,
        Formula::Or(..) => 16,
        Formula::Not(_) => 32,
        Formula::Forall { .. } => 64,
        Formula::Predicate { .. } => 128,
        Formula::Implies(..) => 256,
    }
}

// Projection follows only conjunctions/disjunctions. Normalizing these may
// select a child, so include all child shapes. Negation and implication can
// change shape more broadly; keep them conservatively unfiltered.
fn projectable_shapes(formula: &Formula) -> u16 {
    match formula {
        Formula::And(a, b) | Formula::Or(a, b) => {
            shape(formula) | projectable_shapes(a) | projectable_shapes(b)
        }
        Formula::Not(_) | Formula::Implies(..) => u16::MAX,
        _ => shape(formula),
    }
}

impl Facts {
    pub(super) fn find(&self, formula: &Formula) -> Option<FactId> {
        self.by_formula.get(formula).copied()
    }

    pub(super) fn get(&self, id: FactId) -> &Formula {
        &self.entries[id.0]
    }

    pub(super) fn mentions_predicate(&self, id: FactId, symbol: &str) -> bool {
        self.predicates[id.0].contains(symbol)
    }

    pub(super) fn may_project(&self, id: FactId, normalized_goal: &Formula) -> bool {
        self.projectable_shapes[id.0] & shape(normalized_goal) != 0
    }

    /// Called after graph/storage limits and formula depth have been checked.
    pub(super) fn intern(&mut self, formula: Formula) -> FactId {
        if let Some(id) = self.find(&formula) {
            return id;
        }
        let id = FactId(self.entries.len());
        let mut predicates = BTreeSet::new();
        let mut pending = vec![&formula];
        while let Some(part) = pending.pop() {
            match part {
                Formula::Predicate { symbol, .. } => {
                    predicates.insert(symbol.clone());
                }
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    pending.extend([&**a, &**b])
                }
                Formula::Not(inner) => pending.push(inner),
                Formula::Forall { domain, body, .. } => pending.extend([&**domain, &**body]),
                _ => {}
            }
        }
        self.predicates.push(predicates);
        self.projectable_shapes.push(projectable_shapes(&formula));
        let formula = Arc::new(formula);
        self.entries.push(Arc::clone(&formula));
        self.by_formula.insert(formula, id);
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::kernel::Linear;

    #[test]
    fn interning_preserves_connectives_and_does_not_confuse_distinct_atoms() {
        let mut facts = Facts::default();
        let p = Formula::Ge(Linear::variable("p"));
        let q = Formula::Ge(Linear::variable("q"));
        let first = facts.intern(p.clone());
        assert_eq!(facts.intern(p.clone()), first);
        assert_ne!(facts.intern(q), first);
        let implication = Formula::Implies(Box::new(p.clone()), Box::new(p));
        let id = facts.intern(implication.clone());
        assert_eq!(facts.get(id), &implication);
        assert!(matches!(facts.get(id), Formula::Implies(..)));
        assert_eq!(facts.entries.len(), 3);
        let indexed = facts.by_formula.get_key_value(&implication).unwrap().0;
        assert!(Arc::ptr_eq(indexed, &facts.entries[id.0]));
    }

    #[test]
    fn predicate_index_covers_nested_guards_and_preserves_distinct_versions() {
        let atom = |symbol: &str| Formula::Predicate {
            symbol: symbol.into(),
            arguments: vec![Linear::variable("i")],
        };
        let nested = Formula::Forall {
            variable: "i".into(),
            domain: Box::new(atom("guard")),
            body: Box::new(Formula::Implies(
                Box::new(Formula::Not(Box::new(atom("before")))),
                Box::new(Formula::And(
                    Box::new(atom("after")),
                    Box::new(Formula::Or(Box::new(atom("left")), Box::new(atom("right")))),
                )),
            )),
        };
        let mut facts = Facts::default();
        let id = facts.intern(nested.clone());
        for symbol in ["guard", "before", "after", "left", "right"] {
            assert!(facts.mentions_predicate(id, symbol));
        }
        assert!(!facts.mentions_predicate(id, "later"));
        assert_eq!(id, facts.intern(nested));
        assert_eq!(facts.predicates.len(), 1);
        let other = facts.intern(atom("later"));
        assert!(!facts.mentions_predicate(other, "before"));
        assert!(!facts.may_project(id, &atom("before")));
        assert!(facts.may_project(id, facts.get(id)));
        let conjunction = Formula::And(Box::new(Formula::True), Box::new(facts.get(id).clone()));
        let normalized = conjunction.normalized();
        let conjunction = facts.intern(conjunction);
        assert!(facts.may_project(conjunction, &normalized));
        let implication = Formula::Implies(Box::new(Formula::True), Box::new(atom("after")));
        let normalized = implication.normalized();
        let implication = facts.intern(implication);
        assert!(facts.may_project(implication, &normalized));
    }
}
