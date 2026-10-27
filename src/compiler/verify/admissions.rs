//! Admissions are candidates for individual proof obligations. They never
//! constrain execution paths merely by being declared.

use super::*;

impl Formula {
    fn variables(&self, work: &mut usize) -> Result<BTreeSet<String>> {
        let mut variables = BTreeSet::new();
        let mut pending = vec![self];
        while let Some(formula) = pending.pop() {
            let cost = match formula {
                Self::Ge(row) => row.terms.len().saturating_add(1),
                _ => 1,
            };
            *work = work.saturating_add(cost);
            if *work > MAX_VALUE_WORK {
                return Err("proof relevance work limit reached".into());
            }
            match formula {
                Self::Ge(row) => variables.extend(row.terms.keys().cloned()),
                Self::Not(p) => pending.push(p),
                Self::And(a, b) | Self::Or(a, b) | Self::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                _ => {}
            }
        }
        Ok(variables)
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
        for &node in &self.proof.claims {
            let Some(snapshot) = self.proof.evidence.subjects(node) else {
                continue;
            };
            self.work.value_work = self.work.value_work.saturating_add(snapshot.reads.len());
            if self.work.value_work > MAX_VALUE_WORK {
                return Err("proof subject relevance work limit reached".into());
            }
            if !self.proof.subjects.current(snapshot, &self.storage.memory) {
                continue;
            }
            let same_subject = subjects.is_some_and(|goal| {
                goal.complete
                    && (snapshot.key == goal.key || !snapshot.reads.is_disjoint(&goal.reads))
            });
            if same_subject
                || !variables.is_disjoint(
                    &self
                        .proof
                        .evidence
                        .claim(node)
                        .variables(&mut self.work.value_work)?,
                )
            {
                relevant.push(node);
            }
        }
        // Revalidation of an already-evaluated value may reuse that exact
        // property. It must not turn historical argument assertions into a
        // general contradiction context for new values sharing SSA variables.
        if !variables.is_empty() {
            for &node in &self.proof.value_claims {
                let claim = self.proof.evidence.claim(node);
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
        let mut temporary = self.proof.paths.clone();
        for node in candidates {
            temporary = extend_from(
                &temporary,
                self.proof.evidence.claim(node),
                false,
                paths::Origin::Evidence(node),
                self.session,
                &mut self.work.value_work,
            )?;
        }
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
        let support = self.arithmetic_support_for(goal, subjects, label, line)?;
        let node = self.proof.evidence.arithmetic(goal.clone(), support)?;
        self.proof.uses.push(node);
        Ok(node)
    }
}

#[cfg(test)]
mod tests;
