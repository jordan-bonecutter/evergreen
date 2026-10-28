//! Stable artifact commitments omit arena IDs. They identify regenerated queries;
//! the arithmetic checker still compares exact atom IDs, never digest equality.

use super::*;
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CommittedAtom {
    id: Id,
    digest: [u8; 32],
}

impl CommittedAtom {
    pub fn digest(&self) -> &[u8; 32] {
        &self.digest
    }
}

fn text(hash: &mut Sha256, value: &str) {
    hash.update((value.len() as u64).to_le_bytes());
    hash.update(value.as_bytes());
}

impl Terms {
    fn commitments(
        &self,
        roots: &[Id],
        work: &mut Work,
    ) -> ArithmeticResult<BTreeMap<Id, [u8; 32]>> {
        work.charge(roots.len())?;
        for &root in roots {
            self.node(root)?;
        }
        let mut done = BTreeMap::new();
        let mut pending = roots
            .iter()
            .rev()
            .map(|&id| (id, false))
            .collect::<Vec<_>>();
        while let Some((id, ready)) = pending.pop() {
            work.charge(1)?;
            if done.contains_key(&id) {
                continue;
            }
            let node = self.node(id)?;
            if let Some(digest) = self.commitments[id.index].get() {
                done.insert(id, *digest);
                continue;
            }
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
            let digest = hash_node(node, &done, work)?;
            // Nodes are immutable. This cache depends only on their structure,
            // never a caller path, proof assumption, or mutable plane contents.
            let digest = *self.commitments[id.index].get_or_init(|| digest);
            done.insert(id, digest);
        }
        Ok(done)
    }

    pub fn commitment(&self, root: Id, work: &mut Work) -> ArithmeticResult<[u8; 32]> {
        Ok(self.commitments(&[root], work)?[&root])
    }

    /// Prepare structured rows for the ordinary certificate recording/replay
    /// path. Commitments are shared across the entire query's reachable DAG.
    pub fn committed_rows(
        &self,
        rows: &[Affine<Id>],
        work: &mut Work,
    ) -> ArithmeticResult<Vec<Affine<CommittedAtom>>> {
        let mut roots = Vec::new();
        for row in rows {
            work.charge(1usize.saturating_add(row.terms.len()))?;
            for &atom in row.terms.keys() {
                if matches!(self.node(atom)?, Node::Sum(_)) {
                    return Err(
                        "structured arithmetic rows must use normalized scalar atoms".into(),
                    );
                }
                roots.push(atom);
            }
        }
        let commitments = self.commitments(&roots, work)?;
        rows.iter()
            .map(|row| {
                work.charge(1usize.saturating_add(row.terms.len()))?;
                Ok(Affine {
                    constant: row.constant,
                    terms: row
                        .terms
                        .iter()
                        .map(|(id, coefficient)| {
                            (
                                CommittedAtom {
                                    id: *id,
                                    digest: commitments[id],
                                },
                                *coefficient,
                            )
                        })
                        .collect(),
                })
            })
            .collect()
    }
}

fn hash_node(
    node: &Node,
    done: &BTreeMap<Id, [u8; 32]>,
    work: &mut Work,
) -> ArithmeticResult<[u8; 32]> {
    let mut hash = Sha256::new();
    hash.update(b"evergreen-scalar-term-v1\0");
    match node {
        Node::Variable(name) => {
            work.charge(name.len())?;
            hash.update([0]);
            text(&mut hash, name);
        }
        Node::Application { symbol, arguments } => {
            work.charge(
                symbol
                    .len()
                    .saturating_add(arguments.len().saturating_mul(32)),
            )?;
            hash.update([1]);
            text(&mut hash, symbol);
            hash.update((arguments.len() as u64).to_le_bytes());
            for argument in arguments {
                hash.update(done[argument]);
            }
        }
        Node::Sum(row) => {
            work.charge(row.terms.len().saturating_mul(48).saturating_add(16))?;
            hash.update([2]);
            hash.update(row.constant.to_le_bytes());
            let mut terms = row
                .terms
                .iter()
                .map(|(id, coefficient)| (done[id], *coefficient))
                .collect::<Vec<_>>();
            terms.sort_unstable();
            hash.update((terms.len() as u64).to_le_bytes());
            for (digest, coefficient) in terms {
                hash.update(digest);
                hash.update(coefficient.to_le_bytes());
            }
        }
    }
    Ok(hash.finalize().into())
}
