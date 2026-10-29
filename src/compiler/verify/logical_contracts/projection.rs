//! Project only the requested logical clause. A conditional source must be
//! current before selecting an alternative, and selection needs checked guards.

use super::*;

impl Context<'_> {
    pub(super) fn contract_contains(&mut self, claim: &Formula, goal: &Formula) -> Result<bool> {
        let goal = goal.normalized();
        let mut pending = vec![claim];
        while let Some(claim) = pending.pop() {
            self.charge_value_work(1)?;
            if std::mem::discriminant(claim) == std::mem::discriminant(&goal)
                && claim.normalized().alpha_equal(&goal)
            {
                return Ok(true);
            }
            if let Formula::And(a, b) | Formula::Or(a, b) = claim {
                pending.push(b);
                pending.push(a);
            }
        }
        Ok(false)
    }

    pub(super) fn project_contract_fact(
        &mut self,
        root: evidence::NodeId,
        goal: &Formula,
    ) -> Result<Option<evidence::NodeId>> {
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            let claim = self.proof.evidence.claim(node)?.clone();
            self.charge_value_work(claim.storage_weight()?)?;
            if claim.normalized().alpha_equal(&goal.normalized()) {
                return Ok(Some(node));
            }
            match claim {
                Formula::And(a, b) => {
                    for (claim, rule) in [
                        (*a, evidence::Rule::AndLeft(node)),
                        (*b, evidence::Rule::AndRight(node)),
                    ] {
                        if self.contract_contains(&claim, goal)? {
                            pending.push(self.proof.evidence.derive(claim, rule)?);
                        }
                    }
                }
                Formula::Or(a, b) => {
                    if let Some(selected) = self.select_contract_alternative(node, &a, &b)? {
                        pending.push(selected);
                    }
                }
                _ => {}
            }
        }
        Ok(None)
    }
}
