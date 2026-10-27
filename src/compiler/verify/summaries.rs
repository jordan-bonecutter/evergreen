//! Trust dependencies exported by checked declarations. Safety and advertised
//! postconditions are separate: calling a function need not use its postcondition.

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
}

#[derive(Default)]
struct Dependencies {
    trusts: BTreeSet<TrustId>,
    recursive: BTreeSet<Aspect>,
}

impl Context<'_> {
    fn roots_dependencies(&mut self, roots: &[evidence::NodeId]) -> Result<Dependencies> {
        let mut out = Dependencies::default();
        for &node in roots {
            let dependencies = self.evidence_dependencies(node)?;
            for source in dependencies.admissions {
                out.trusts.insert(self.proof.evidence.trust(source)?);
            }
            out.recursive.extend(dependencies.pending_summaries);
        }
        Ok(out)
    }

    pub(super) fn declaration_requirements(&mut self) -> Result<Requirements> {
        Ok(Requirements {
            safety: self.roots_dependencies(&self.proof.uses.clone())?,
            contract: self.roots_dependencies(&self.proof.contract_uses.clone())?,
        })
    }
}

#[derive(Default)]
pub(super) struct Requirements {
    safety: Dependencies,
    contract: Dependencies,
}

impl Requirements {
    pub(super) fn extend(&mut self, other: Self) {
        self.safety.trusts.extend(other.safety.trusts);
        self.safety.recursive.extend(other.safety.recursive);
        self.contract.trusts.extend(other.contract.trusts);
        self.contract.recursive.extend(other.contract.recursive);
    }

    pub(super) fn summary(self) -> Summary {
        let Self { safety, contract } = self;
        let mut summary = Summary {
            safety: safety.trusts,
            contract: contract.trusts,
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
