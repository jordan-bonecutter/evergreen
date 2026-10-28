//! Admissions are candidates for individual proof obligations. They never
//! constrain execution paths merely by being declared.

use super::*;
mod contracts;
mod guards;
mod history;
use history::Demand;
pub(super) use history::RecursiveContext;

impl Formula {
    pub(super) fn variables(&self, work: &mut usize) -> Result<BTreeSet<String>> {
        *work = work.saturating_add(self.storage_weight()?);
        if *work > MAX_VALUE_WORK {
            return Err("proof relevance work limit reached".into());
        }
        self.free_variables()
    }
}

impl Context<'_> {
    pub(super) fn evidence_dependencies(
        &mut self,
        node: evidence::NodeId,
    ) -> Result<evidence::AdmissionDependencies> {
        let dependencies = self.proof.evidence.admissions(node);
        self.charge_value_work(dependencies.work)?;
        Ok(dependencies)
    }

    fn relevant_claims(
        &mut self,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<Vec<evidence::NodeId>> {
        let variables = goal.variables(&mut self.work.value_work)?;
        let mut relevant = Vec::new();
        let mut historical = Demand::from_subjects(subjects);
        let candidates = if let Some(subjects) = subjects.filter(|s| s.complete) {
            self.proof
                .subjects
                .candidates(subjects)
                .intersection(&self.proof.claims)
                .copied()
                .collect::<BTreeSet<_>>()
        } else {
            self.proof.claims.clone()
        };
        for node in candidates {
            if !self.proof.evidence.claim(node)?.is_arithmetic() {
                continue;
            }
            let Some(snapshot) = self.proof.evidence.subjects(node) else {
                continue;
            };
            self.work.value_work = self.work.value_work.saturating_add(snapshot.reads.len());
            if self.work.value_work > MAX_VALUE_WORK {
                return Err("proof subject relevance work limit reached".into());
            }
            let available =
                self.proof
                    .subjects
                    .availability(snapshot, &self.storage.memory, None)?;
            if available == Formula::False {
                continue;
            }
            let same_subject = subjects.is_some_and(|goal| {
                goal.complete
                    && (snapshot.key == goal.key
                        || !snapshot.reads.is_disjoint(&goal.reads)
                        || snapshot.past.values().any(|reads| {
                            !reads.is_disjoint(&goal.reads)
                                || goal
                                    .past
                                    .values()
                                    .any(|required| !reads.is_disjoint(required))
                        }))
            });
            let live_dependency = !snapshot.reads.is_empty() || snapshot.past.is_empty();
            if same_subject
                || live_dependency
                    && !variables.is_disjoint(
                        &self
                            .proof
                            .evidence
                            .claim(node)?
                            .variables(&mut self.work.value_work)?,
                    )
            {
                let snapshot = snapshot.clone();
                let scope = self
                    .reference_claim_scope(&snapshot, subjects)?
                    .and(available);
                relevant.push(self.proof.evidence.guard(node, &scope)?);
                historical.extend_under(&snapshot, &scope);
            }
        }
        self.recursive_demands(&mut historical, &variables)?;
        relevant.extend(self.follow_history(historical, subjects)?);
        // Revalidation of an already-evaluated value may reuse that exact
        // property. It must not turn historical argument assertions into a
        // general contradiction context for new values sharing SSA variables.
        if !variables.is_empty() {
            for &node in &self.proof.value_claims {
                let claim = self.proof.evidence.claim(node)?;
                claim.variables(&mut self.work.value_work)?;
                if claim.normalized() == goal.normalized() {
                    relevant.push(node);
                }
            }
        }
        self.charge_value_work(
            self.proof
                .claims
                .len()
                .saturating_add(self.proof.value_claims.len()),
        )?;
        Ok(relevant)
    }

    pub(super) fn arithmetic_support_for(
        &mut self,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
        label: &str,
        line: usize,
    ) -> Result<paths::Support> {
        self.work.obligations += 1;
        let candidates = self.relevant_claims(goal, subjects)?;
        let checked = extend_from(
            &self.proof.paths,
            goal,
            true,
            paths::Origin::NegatedGoal,
            self.session,
            &mut self.work.value_work,
        )?;
        if candidates.is_empty() {
            return self.check_arithmetic_paths(&checked, label, line);
        }
        // Prefer a checked proof with no admissions. Optional query failures
        // are recorded, making the fallback and its support replayable.
        let mut ordinary = checked.closed.clone();
        let mut complete = true;
        for path in checked.iter() {
            if let Some(support) = self.session.probe_with_support(path)? {
                ordinary.add_rows(path, &support);
            } else {
                complete = false;
                break;
            }
        }
        if complete {
            return Ok(ordinary);
        }
        let mut temporary = self.candidate_paths(&candidates)?;
        temporary = extend_from(
            &temporary,
            goal,
            true,
            paths::Origin::NegatedGoal,
            self.session,
            &mut self.work.value_work,
        )?;
        self.check_arithmetic_paths(&temporary, label, line)
    }

    fn check_arithmetic_paths(
        &mut self,
        paths: &paths::Paths,
        label: &str,
        line: usize,
    ) -> Result<paths::Support> {
        let mut dependencies = paths.closed.clone();
        for path in paths.iter() {
            let support = self
                .session
                .prove_with_support(path)
                .map_err(|e| format!("line {line}: cannot prove {label}: {e}"))?;
            dependencies.add_rows(path, &support);
        }
        Ok(dependencies)
    }

    pub(super) fn prove_subjects(
        &mut self,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
        label: &str,
        line: usize,
    ) -> Result<evidence::NodeId> {
        if !goal.is_arithmetic() {
            let node = self.prove_logical_contract(goal, subjects, label, line)?;
            self.proof.evidence.check_closed(node)?;
            self.proof.uses.push(node);
            return Ok(node);
        }
        let support = self.arithmetic_support_for(goal, subjects, label, line)?;
        let node = self.proof.evidence.arithmetic(goal.clone(), support)?;
        self.proof.evidence.check_closed(node)?;
        self.proof.uses.push(node);
        Ok(node)
    }
}

#[cfg(test)]
mod tests;
