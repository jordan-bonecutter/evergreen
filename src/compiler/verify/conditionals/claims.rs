//! Retain logical branch results as guarded candidates. Their original subjects
//! are never rewritten to the joined revision or declared unconditionally live.

use super::*;

impl Context<'_> {
    pub(super) fn retain_conditional_claims(
        &mut self,
        left: BTreeSet<evidence::NodeId>,
        right: BTreeSet<evidence::NodeId>,
        condition: &Formula,
    ) -> Result<()> {
        self.charge_value_work(left.len().saturating_add(right.len()))?;
        let control = self.proof.control.clone().unwrap_or(Formula::True);
        for node in left.union(&right).copied() {
            if self.proof.evidence.claim(node)?.is_arithmetic()
                || self.proof.evidence.has_admissions(node)
                || self.proof.evidence.has_pending_summaries(node)
                || self.proof.evidence.check_closed(node).is_err()
            {
                continue;
            }
            let Some(snapshot) = self
                .proof
                .evidence
                .subjects(node)
                .cloned()
                .filter(|s| s.complete)
            else {
                continue;
            };
            let branch = match (left.contains(&node), right.contains(&node)) {
                (true, true) => Formula::True,
                (true, false) => condition.clone(),
                _ => condition.clone().not(),
            };
            let guard = self
                .proof
                .claim_guards
                .get(&node)
                .cloned()
                .unwrap_or(Formula::True)
                .and(control.clone())
                .and(branch);
            self.charge_value_work(
                guard
                    .storage_weight()?
                    .saturating_add(snapshot.storage_weight()?),
            )?;
            self.proof.claim_guards.insert(node, guard);
            self.proof.claims.insert(node);
            self.proof.subjects.publish(node, &snapshot);
        }
        Ok(())
    }
}
