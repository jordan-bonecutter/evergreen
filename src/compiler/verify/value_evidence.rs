//! Transport an advertised call result into its binding. The mathematical value
//! is identical; its state dependency becomes the receiver's initial revision.
//! Ordinary assignments do not inherit this transport automatically.

use super::*;

pub(super) struct CallResult {
    pub(super) value: Symbol,
    pub(super) proof: evidence::NodeId,
    pub(super) origin: subjects::Snapshot,
    pub(super) control: Formula,
}

impl Context<'_> {
    pub(super) fn publish_call_contract(
        &mut self,
        node: evidence::NodeId,
        subjects: subjects::Snapshot,
        value: &Symbol,
        line: usize,
    ) -> Result<Vec<evidence::NodeId>> {
        let clauses = self.contract_clauses(node, subjects)?;
        let origin = self.claim_subjects(&Expr {
            kind: Kind::Name("result".into()),
            line,
        })?;
        let control = self.proof.control.clone().unwrap_or(Formula::True);
        let cost = symbol_weight(value)?
            .saturating_add(origin.storage_weight()?)
            .saturating_add(control.storage_weight()?);
        for &proof in &clauses {
            self.proof.claims.insert(proof);
            self.charge_value_work(cost)?;
            self.proof.results.push(CallResult {
                value: value.clone(),
                proof,
                origin: origin.clone(),
                control: control.clone(),
            });
        }
        Ok(clauses)
    }

    pub(super) fn bind_call_evidence(
        &mut self,
        name: &str,
        value: &Symbol,
        start: usize,
        line: usize,
    ) -> Result<()> {
        let pending = self.proof.results.split_off(start);
        for result in pending.into_iter().filter(|result| result.value == *value) {
            // A branch's returned guarantee cannot become unconditional just
            // because both branches happened to produce equal scalar values.
            if !self.checked_entails(&result.control)? {
                continue;
            }
            let Some(mut snapshot) = self.proof.evidence.subjects(result.proof).cloned() else {
                continue;
            };
            let target = self.claim_subjects(&Expr {
                kind: Kind::Name(name.into()),
                line,
            })?;
            let key = snapshot.key.clone();
            snapshot.replace_read(&result.origin, &target);
            if snapshot.key == key {
                continue;
            }
            let claim = self.proof.evidence.claim(result.proof)?.clone();
            let node = self
                .proof
                .evidence
                .derive(claim, evidence::Rule::Reuse(result.proof))?;
            self.publish_evidence(node, snapshot)?;
            self.proof.claims.remove(&result.proof);
            self.proof.claims.insert(node);
        }
        Ok(())
    }
}
