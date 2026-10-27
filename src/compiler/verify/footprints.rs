//! Allocation presence is distinct from owning a live handle. Conditional
//! storage may be ignored only with checked, admission-free reachability.

use super::*;

impl Context<'_> {
    pub(super) fn record_plane_presence(&mut self, plane: PlaneId) -> Result<()> {
        let guard = self
            .storage
            .allocation_guard
            .clone()
            .unwrap_or(Formula::True)
            .and(self.proof.control.clone().unwrap_or(Formula::True));
        self.charge_value_work(guard.storage_weight()?)?;
        if guard != Formula::True {
            self.storage.presence.insert(plane, guard);
        }
        Ok(())
    }

    pub(super) fn plane_presence(&self, plane: PlaneId) -> Formula {
        self.storage
            .presence
            .get(&plane)
            .cloned()
            .unwrap_or(Formula::True)
    }

    pub(super) fn checked_impossible(
        &mut self,
        context: &paths::Paths,
        guard: &Formula,
    ) -> Result<bool> {
        if guard == &Formula::False {
            return Ok(true);
        }
        let tested = extend_from(
            context,
            guard,
            false,
            paths::Origin::NegatedGoal,
            self.session,
            &mut self.work.value_work,
        )?;
        let mut support = tested.closed.clone();
        for path in tested.iter() {
            let Some(rows) = self.session.probe_with_support(path)? else {
                return Ok(false);
            };
            support.add_rows(path, &rows);
        }
        for &parent in &support.parents {
            let dependencies = self.evidence_dependencies(parent)?;
            if !dependencies.admissions.is_empty() || !dependencies.pending_summaries.is_empty() {
                return Ok(false);
            }
        }
        let proof = self
            .proof
            .evidence
            .arithmetic(guard.clone().not(), support)?;
        self.proof.evidence.check_closed(proof)?;
        self.proof.uses.push(proof);
        Ok(true)
    }

    pub(super) fn checked_entails(&mut self, guard: &Formula) -> Result<bool> {
        if guard == &Formula::True {
            return Ok(true);
        }
        self.checked_impossible(&self.proof.paths.clone(), &guard.clone().not())
    }
}
