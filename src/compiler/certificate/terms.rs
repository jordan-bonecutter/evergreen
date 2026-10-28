//! Query commitments for named and structured arithmetic atoms. Digests select
//! an artifact record; the ordinary kernel checks it against the actual rows.

use super::*;
use crate::compiler::kernel::terms::CommittedAtom;

pub(crate) trait ArtifactAtom: Ord + Clone {
    fn statement_hash(rows: &[Affine<Self>]) -> String;
}

impl ArtifactAtom for String {
    fn statement_hash(rows: &[Affine<Self>]) -> String {
        let mut h = Sha256::new();
        h.update(b"evergreen-linear-v1\0");
        h.update((rows.len() as u64).to_le_bytes());
        for row in rows {
            h.update(row.constant.to_le_bytes());
            h.update((row.terms.len() as u64).to_le_bytes());
            for (name, coefficient) in &row.terms {
                h.update((name.len() as u64).to_le_bytes());
                h.update(name.as_bytes());
                h.update(coefficient.to_le_bytes());
            }
        }
        format!("{:x}", h.finalize())
    }
}

impl ArtifactAtom for CommittedAtom {
    fn statement_hash(rows: &[Affine<Self>]) -> String {
        let mut hash = Sha256::new();
        hash.update(b"evergreen-structured-linear-v1\0");
        hash.update((rows.len() as u64).to_le_bytes());
        for row in rows {
            hash.update(row.constant.to_le_bytes());
            let mut terms = row
                .terms
                .iter()
                .map(|(atom, coefficient)| (*atom.digest(), *coefficient))
                .collect::<Vec<_>>();
            terms.sort_unstable();
            hash.update((terms.len() as u64).to_le_bytes());
            for (digest, coefficient) in terms {
                hash.update(digest);
                hash.update(coefficient.to_le_bytes());
            }
        }
        format!("{:x}", hash.finalize())
    }
}

#[cfg(test)]
mod tests;
