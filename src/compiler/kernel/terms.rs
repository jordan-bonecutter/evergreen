//! Immutable, interned scalar terms. Applications retain every argument; their
//! identity is structural rather than a string containing a printed expression.
//! The arithmetic kernel treats applications as atoms, with no memory axioms.

use super::{Affine, ArithmeticResult};
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc, OnceLock,
};

mod commitment;
mod traversal;
pub use commitment::CommittedAtom;

#[cfg(test)]
mod tests;

static NEXT_ARENA: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id {
    arena: u64,
    index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Variable(String),
    Application { symbol: String, arguments: Vec<Id> },
    Sum(Affine<Id>),
}

/// A caller supplies one budget for the complete operation, including its
/// suboperations. Exhaustion is an error, never a partially valid proof term.
pub struct Work {
    remaining: usize,
    spent: usize,
}

impl Work {
    pub fn new(limit: usize) -> Self {
        Self {
            remaining: limit,
            spent: 0,
        }
    }

    pub fn spent(&self) -> usize {
        self.spent
    }

    fn charge(&mut self, amount: usize) -> ArithmeticResult<()> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or("scalar term work limit reached")?;
        self.spent += amount;
        Ok(())
    }
}

pub struct Terms {
    arena: u64,
    nodes: Vec<Arc<Node>>,
    interned: BTreeMap<Arc<Node>, Id>,
    commitments: Vec<OnceLock<[u8; 32]>>,
}

impl Terms {
    pub fn new() -> ArithmeticResult<Self> {
        let arena = NEXT_ARENA
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
            .map_err(|_| "scalar term arena identity limit reached")?;
        Ok(Self {
            arena,
            nodes: Vec::new(),
            interned: BTreeMap::new(),
            commitments: Vec::new(),
        })
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    fn node(&self, id: Id) -> ArithmeticResult<&Node> {
        if id.arena != self.arena {
            return Err("scalar term belongs to another arena".into());
        }
        self.nodes
            .get(id.index)
            .map(Arc::as_ref)
            .ok_or_else(|| "unknown scalar term".into())
    }

    fn intern(&mut self, node: Node, work: &mut Work) -> ArithmeticResult<Id> {
        work.charge(1)?;
        if let Some(id) = self.interned.get(&node) {
            return Ok(*id);
        }
        let id = Id {
            arena: self.arena,
            index: self.nodes.len(),
        };
        let node = Arc::new(node);
        self.nodes.push(Arc::clone(&node));
        self.commitments.push(OnceLock::new());
        self.interned.insert(node, id);
        Ok(id)
    }

    pub fn number(&mut self, n: i128, work: &mut Work) -> ArithmeticResult<Id> {
        self.intern(Node::Sum(Affine::number(n)), work)
    }

    pub fn variable(&mut self, name: &str, work: &mut Work) -> ArithmeticResult<Id> {
        work.charge(name.len())?;
        self.intern(Node::Variable(name.to_owned()), work)
    }

    pub fn application(
        &mut self,
        symbol: &str,
        arguments: &[Id],
        work: &mut Work,
    ) -> ArithmeticResult<Id> {
        work.charge(symbol.len().saturating_add(arguments.len()))?;
        for &argument in arguments {
            self.node(argument)?;
        }
        self.intern(
            Node::Application {
                symbol: symbol.to_owned(),
                arguments: arguments.to_vec(),
            },
            work,
        )
    }

    /// Extract a normalized arithmetic row. Only variables and applications
    /// are keys; nested sums have already been flattened with checked arithmetic.
    pub fn affine(&self, id: Id, work: &mut Work) -> ArithmeticResult<Affine<Id>> {
        match self.node(id)? {
            Node::Sum(row) => {
                work.charge(1usize.saturating_add(row.terms.len()))?;
                Ok(row.clone())
            }
            _ => {
                work.charge(1)?;
                Ok(Affine::variable(id))
            }
        }
    }

    fn sum(&mut self, row: Affine<Id>, work: &mut Work) -> ArithmeticResult<Id> {
        if row.constant == 0 && row.terms.len() == 1 {
            let (&id, &coefficient) = row.terms.first_key_value().unwrap();
            if coefficient == 1 {
                return Ok(id);
            }
        }
        self.intern(Node::Sum(row), work)
    }

    pub fn add(&mut self, a: Id, b: Id, work: &mut Work) -> ArithmeticResult<Id> {
        let a = self.affine(a, work)?;
        let b = self.affine(b, work)?;
        work.charge(a.terms.len().saturating_add(b.terms.len()))?;
        self.sum(a.add(&b)?, work)
    }

    pub fn scale(&mut self, value: Id, factor: i128, work: &mut Work) -> ArithmeticResult<Id> {
        let row = self.affine(value, work)?;
        work.charge(row.terms.len())?;
        self.sum(row.scale(factor)?, work)
    }
}
