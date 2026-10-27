//! Immutable proposition storage. Interning a formula establishes no truth;
//! only the evidence arena can create a proof concluding one of these facts.

use super::Formula;
use std::{collections::BTreeMap, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct FactId(usize);

#[derive(Default, Debug)]
pub(super) struct Facts {
    entries: Vec<Arc<Formula>>,
    by_formula: BTreeMap<Arc<Formula>, FactId>,
}

impl Facts {
    pub(super) fn find(&self, formula: &Formula) -> Option<FactId> {
        self.by_formula.get(formula).copied()
    }

    pub(super) fn get(&self, id: FactId) -> &Formula {
        &self.entries[id.0]
    }

    /// Called after graph/storage limits and formula depth have been checked.
    pub(super) fn intern(&mut self, formula: Formula) -> FactId {
        if let Some(id) = self.find(&formula) {
            return id;
        }
        let id = FactId(self.entries.len());
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
}
