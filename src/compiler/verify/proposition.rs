//! Propositions and connective normalization. Declaring a formula
//! creates no evidence; inference rules consume separate proof identities.

use crate::compiler::kernel::Linear;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Formula {
    True,
    False,
    Ge(Linear),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Implies(Box<Self>, Box<Self>),
}

impl Formula {
    pub(super) fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Self::True => out.push(0),
            Self::False => out.push(1),
            Self::Ge(row) => {
                out.push(2);
                out.extend(row.constant.to_le_bytes());
                out.extend((row.terms.len() as u64).to_le_bytes());
                for (name, coefficient) in &row.terms {
                    out.extend((name.len() as u64).to_le_bytes());
                    out.extend(name.as_bytes());
                    out.extend(coefficient.to_le_bytes());
                }
            }
            Self::And(a, b) | Self::Or(a, b) => {
                out.push(if matches!(self, Self::And(..)) { 3 } else { 4 });
                a.encode(out);
                b.encode(out);
            }
            Self::Not(p) => {
                out.push(5);
                p.encode(out);
            }
            Self::Implies(a, b) => {
                out.push(6);
                a.encode(out);
                b.encode(out);
            }
        }
    }

    pub(super) fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, p) | (p, Self::True) => p,
            (a, b) if a == b => a,
            (a, b) => Self::And(Box::new(a), Box::new(b)),
        }
    }

    pub(super) fn or(self, other: Self) -> Self {
        match (self, other) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, p) | (p, Self::False) => p,
            (a, b) if a == b => a,
            (a, b) => Self::Or(Box::new(a), Box::new(b)),
        }
    }

    pub(super) fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(p) => *p,
            p => Self::Not(Box::new(p)),
        }
    }
}

impl Formula {
    // Retain connective structure for introduction/elimination rules, while
    // exact matching keeps the existing normalization of logical expressions.
    pub(super) fn normalized(&self) -> Self {
        match self {
            Self::And(a, b) => a.normalized().and(b.normalized()),
            Self::Or(a, b) => a.normalized().or(b.normalized()),
            Self::Implies(a, b) => a.normalized().not().or(b.normalized()),
            Self::Not(p) => p.normalized().not(),
            _ => self.clone(),
        }
    }
}
