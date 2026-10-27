//! Transport an advertised call result into its binding. The mathematical value
//! is identical; its state dependency becomes the receiver's initial revision.
//! Ordinary assignments do not inherit this transport automatically.

use super::*;

pub(super) struct CallResult {
    pub(super) value: Symbol,
    pub(super) proof: evidence::NodeId,
    pub(super) origin: subjects::Snapshot,
}

impl Context<'_> {
    pub(super) fn bind_call_evidence(
        &mut self,
        name: &str,
        value: &Symbol,
        start: usize,
        line: usize,
    ) -> Result<()> {
        let pending = self.proof.results.split_off(start);
        for result in pending.into_iter().filter(|result| result.value == *value) {
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
