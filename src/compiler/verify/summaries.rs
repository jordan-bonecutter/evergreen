//! Checked call summaries: trust dependencies and isolated allocation effects.
//! Safety and advertised postconditions remain separate dependencies.

use super::*;
use crate::compiler::certificate::TrustId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Aspect {
    Safety,
    Contract,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Summary {
    pub(super) safety: BTreeSet<TrustId>,
    pub(super) contract: BTreeSet<TrustId>,
    // Every checked return consumes all unique inputs and owns a fresh result.
    pub(super) fresh_allocation: bool,
}

#[derive(Default)]
struct Dependencies {
    trusts: BTreeSet<TrustId>,
    recursive: BTreeSet<Aspect>,
}

impl Context<'_> {
    fn roots_dependencies(&mut self, roots: &[evidence::NodeId]) -> Result<Dependencies> {
        let mut out = Dependencies::default();
        // Nodes already cache whether their ancestry contains trust or a
        // pending recursive summary. Trust-free subgraphs need no traversal
        // when computing a declaration's trust summary.
        self.charge_value_work(roots.len())?;
        let relevant = roots
            .iter()
            .copied()
            .filter(|&node| {
                self.proof.evidence.has_admissions(node)
                    || self.proof.evidence.has_pending_summaries(node)
            })
            .collect::<Vec<_>>();
        let dependencies = self.proof.evidence.admissions_many(&relevant);
        self.charge_value_work(dependencies.work)?;
        for source in dependencies.admissions {
            out.trusts.insert(self.proof.evidence.trust(source)?);
        }
        out.recursive.extend(dependencies.pending_summaries);
        Ok(out)
    }

    pub(super) fn declaration_requirements(&mut self) -> Result<Requirements> {
        Ok(Requirements {
            safety: self.roots_dependencies(&self.proof.uses.clone())?,
            contract: self.roots_dependencies(&self.proof.contract_uses.clone())?,
            fresh_allocation: Some(self.execution.fresh_allocation_result),
        })
    }
}

#[derive(Default)]
pub(super) struct Requirements {
    safety: Dependencies,
    contract: Dependencies,
    fresh_allocation: Option<bool>,
}

impl Requirements {
    pub(super) fn extend(&mut self, other: Self) {
        if let Some(other) = other.fresh_allocation {
            // One branch returning an input allocation rules out this effect.
            self.fresh_allocation = Some(self.fresh_allocation.unwrap_or(true) && other);
        }
        self.safety.trusts.extend(other.safety.trusts);
        self.safety.recursive.extend(other.safety.recursive);
        self.contract.trusts.extend(other.contract.trusts);
        self.contract.recursive.extend(other.contract.recursive);
    }

    pub(super) fn summary(self) -> Summary {
        let Self {
            safety,
            contract,
            fresh_allocation,
        } = self;
        let mut summary = Summary {
            safety: safety.trusts,
            contract: contract.trusts,
            fresh_allocation: fresh_allocation.unwrap_or(false),
        };
        loop {
            let before = summary.clone();
            summary.contract.extend(summary.safety.iter().copied());
            if safety.recursive.contains(&Aspect::Contract) {
                summary.safety.extend(summary.contract.iter().copied());
            }
            // Safety self-references add nothing; the contract already includes
            // safety. These two monotone sets reach a fixed point in at most
            // two expansions, without introducing a cyclic proof premise.
            if summary == before {
                break;
            }
        }
        summary
    }
}

impl Context<'_> {
    pub(super) fn import_summary(
        &mut self,
        name: &str,
        aspect: Aspect,
    ) -> Result<Vec<evidence::NodeId>> {
        let Some(summary) = self.declarations.summaries.get(name) else {
            if self.execution.current.as_deref() == Some(name) {
                return Ok(vec![self.proof.evidence.reference(vec![], Some(aspect))?]);
            }
            return Err(format!("missing checked trust summary for {name}"));
        };
        let trusts = match aspect {
            Aspect::Safety => &summary.safety,
            Aspect::Contract => &summary.contract,
        };
        let mut parents = Vec::new();
        for &trust in trusts {
            parents.push(self.proof.evidence.import_trust(trust)?);
        }
        self.charge_value_work(parents.len())?;
        Ok(parents)
    }
}

#[cfg(test)]
mod tests;
