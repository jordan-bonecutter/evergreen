//! Publish independent conjuncts of a contract as separate proof candidates.
//! For example, an exchange's new contents do not depend on its old-result fact.

use super::*;

impl Context<'_> {
    pub(in crate::compiler::verify) fn contract_clauses(
        &mut self,
        root: evidence::NodeId,
        snapshot: subjects::Snapshot,
    ) -> Result<Vec<evidence::NodeId>> {
        let mut pending = vec![(root, snapshot)];
        let mut clauses = Vec::new();
        while let Some((proof, snapshot)) = pending.pop() {
            self.charge_value_work(1)?;
            match self.proof.evidence.claim(proof)?.clone() {
                Formula::And(a, b) => {
                    // Equality also elaborates into two inequalities. Both
                    // keep the equality's footprint; source && splits it.
                    let left_snapshot = snapshot
                        .branch("&&", false)
                        .unwrap_or_else(|| snapshot.clone());
                    let right_snapshot = snapshot.branch("&&", true).unwrap_or(snapshot);
                    let left = self
                        .proof
                        .evidence
                        .derive(*a, evidence::Rule::AndLeft(proof))?;
                    let right = self
                        .proof
                        .evidence
                        .derive(*b, evidence::Rule::AndRight(proof))?;
                    pending.push((right, right_snapshot));
                    pending.push((left, left_snapshot));
                }
                Formula::True => {}
                _ => {
                    if self.proof.evidence.subjects(proof).is_none() {
                        self.publish_evidence(proof, snapshot)?;
                    }
                    clauses.push(proof);
                }
            }
        }
        Ok(clauses)
    }
}
