//! Iterative DAG traversal and simultaneous substitution. No recursion follows
//! a term's mathematical depth, and each shared node is rewritten once.

use super::*;
use std::collections::BTreeSet;

impl Terms {
    /// Follow distinct DAG nodes, so repeated references to a shared subtree
    /// cost one traversal rather than expanding it into a tree.
    pub fn free_variables(&self, root: Id, work: &mut Work) -> ArithmeticResult<BTreeSet<String>> {
        let mut seen = BTreeSet::new();
        let mut pending = vec![root];
        let mut variables = BTreeSet::new();
        while let Some(id) = pending.pop() {
            work.charge(1)?;
            if !seen.insert(id) {
                continue;
            }
            match self.node(id)? {
                Node::Variable(name) => {
                    work.charge(name.len())?;
                    variables.insert(name.clone());
                }
                Node::Application { arguments, .. } => {
                    work.charge(arguments.len())?;
                    pending.extend(arguments.iter().copied());
                }
                Node::Sum(row) => {
                    work.charge(row.terms.len())?;
                    pending.extend(row.terms.keys().copied());
                }
            }
        }
        Ok(variables)
    }

    /// Simultaneous substitution visits every application argument. Inserted
    /// terms are not rewritten again, and shared subterms remain shared.
    pub fn substitute(
        &mut self,
        root: Id,
        bindings: &BTreeMap<String, Id>,
        work: &mut Work,
    ) -> ArithmeticResult<Id> {
        self.node(root)?;
        if bindings.is_empty() {
            work.charge(1)?;
            return Ok(root);
        }
        for &value in bindings.values() {
            work.charge(1)?;
            self.node(value)?;
        }
        let mut rewritten = BTreeMap::new();
        let mut pending = vec![(root, false)];
        while let Some((id, ready)) = pending.pop() {
            work.charge(1)?;
            if rewritten.contains_key(&id) {
                continue;
            }
            let node = Arc::clone(&self.nodes[id.index]);
            if !ready {
                pending.push((id, true));
                match node.as_ref() {
                    Node::Application { arguments, .. } => {
                        work.charge(arguments.len())?;
                        pending.extend(arguments.iter().rev().map(|&id| (id, false)));
                    }
                    Node::Sum(row) => {
                        work.charge(row.terms.len())?;
                        pending.extend(row.terms.keys().rev().map(|&id| (id, false)));
                    }
                    Node::Variable(_) => {}
                }
                continue;
            }
            let new = match node.as_ref() {
                Node::Variable(name) => bindings.get(name).copied().unwrap_or(id),
                Node::Application { symbol, arguments } => {
                    work.charge(arguments.len())?;
                    let arguments = arguments.iter().map(|id| rewritten[id]).collect::<Vec<_>>();
                    self.application(symbol, &arguments, work)?
                }
                Node::Sum(row) => {
                    let mut result = self.number(row.constant, work)?;
                    for (atom, coefficient) in &row.terms {
                        let term = self.scale(rewritten[atom], *coefficient, work)?;
                        result = self.add(result, term, work)?;
                    }
                    result
                }
            };
            rewritten.insert(id, new);
        }
        Ok(rewritten[&root])
    }
}
