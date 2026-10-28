//! Explicitly rebuild reachable terms in another arena. Child identities are
//! mapped before parents; sharing is preserved without copying unrelated nodes.

use super::*;

impl Terms {
    pub fn import(
        &mut self,
        source: &Self,
        roots: &[Id],
        work: &mut Work,
    ) -> ArithmeticResult<Vec<Id>> {
        work.charge(roots.len())?;
        for &root in roots {
            source.node(root)?;
        }
        let mut mapped = BTreeMap::new();
        let mut pending = roots
            .iter()
            .rev()
            .map(|&id| (id, false))
            .collect::<Vec<_>>();
        while let Some((id, ready)) = pending.pop() {
            work.charge(1)?;
            if mapped.contains_key(&id) {
                continue;
            }
            let node = source.node(id)?;
            if !ready {
                pending.push((id, true));
                match node {
                    Node::Variable(_) => {}
                    Node::Application { arguments, .. } => {
                        work.charge(arguments.len())?;
                        pending.extend(arguments.iter().rev().map(|&id| (id, false)));
                    }
                    Node::Sum(row) => {
                        work.charge(row.terms.len())?;
                        pending.extend(row.terms.keys().rev().map(|&id| (id, false)));
                    }
                }
                continue;
            }
            let new = match node {
                Node::Variable(name) => self.variable(name, work)?,
                Node::Application { symbol, arguments } => {
                    work.charge(arguments.len())?;
                    let arguments = arguments.iter().map(|id| mapped[id]).collect::<Vec<_>>();
                    self.application(symbol, &arguments, work)?
                }
                Node::Sum(row) => {
                    work.charge(row.terms.len())?;
                    self.sum(
                        Affine {
                            constant: row.constant,
                            terms: row
                                .terms
                                .iter()
                                .map(|(id, coefficient)| (mapped[id], *coefficient))
                                .collect(),
                        },
                        work,
                    )?
                }
            };
            mapped.insert(id, new);
        }
        Ok(roots.iter().map(|root| mapped[root]).collect())
    }
}
