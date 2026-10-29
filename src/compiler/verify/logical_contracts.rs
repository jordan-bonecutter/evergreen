//! Logical contract clauses retain their evidence and state subjects. They
//! never become arithmetic rows merely because a declaration imported them.

use super::*;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod type_tests;

impl Context<'_> {
    pub(super) fn guarded_claim_evidence(
        &mut self,
        node: evidence::NodeId,
        scope: &Formula,
    ) -> Result<Option<evidence::NodeId>> {
        if *scope == Formula::True {
            return Ok(Some(node));
        }
        let Some(support) = self.probe_guard(&self.proof.paths.clone(), scope)? else {
            return Ok(None);
        };
        if support.parents.iter().any(|&parent| {
            self.proof.evidence.has_admissions(parent)
                || self.proof.evidence.has_pending_summaries(parent)
        }) {
            return Ok(None);
        }
        self.work.obligations += 1;
        let condition = self.proof.evidence.arithmetic(scope.clone(), support)?;
        let theorem = self.proof.evidence.guard(node, scope)?;
        self.proof
            .evidence
            .derive(
                self.proof.evidence.claim(node)?.clone(),
                evidence::Rule::ImpElim {
                    theorem,
                    argument: condition,
                },
            )
            .map(Some)
    }
    pub(super) fn logical_claim_scope(
        &mut self,
        node: evidence::NodeId,
        snapshot: &subjects::Snapshot,
    ) -> Result<Formula> {
        if let Some(guard) = self.proof.claim_guards.get(&node).cloned() {
            let available = self
                .proof
                .subjects
                .branch_availability(snapshot, &self.storage.memory)?;
            Ok(guard.and(available))
        } else {
            self.proof
                .subjects
                .availability(snapshot, &self.storage.memory, None)
        }
    }
    pub(super) fn assume_declared_invariant(&mut self, expression: &Expr) -> Result<()> {
        let proposition = self.proposition(expression)?;
        if proposition.is_arithmetic() {
            self.assume(&proposition)
        } else {
            let subjects = self.claim_subjects(expression)?;
            self.import_logical_contract(proposition, subjects, self.proof.contract_parents.clone())
        }
    }

    pub(super) fn import_logical_contract(
        &mut self,
        proposition: Formula,
        snapshot: subjects::Snapshot,
        parents: Vec<evidence::NodeId>,
    ) -> Result<()> {
        let root = self.proof.evidence.contract(proposition, parents)?;
        self.import_contract_evidence(root, snapshot)
    }

    pub(super) fn import_contract_evidence(
        &mut self,
        root: evidence::NodeId,
        snapshot: subjects::Snapshot,
    ) -> Result<()> {
        for node in self.contract_clauses(root, snapshot)? {
            let claim = self.proof.evidence.claim(node)?.clone();
            if claim.is_arithmetic() && self.evidence_dependencies(node)?.admissions.is_empty() {
                self.assume_from(&claim, paths::Origin::Evidence(node))?;
            } else {
                self.proof.claims.insert(node);
            }
        }
        Ok(())
    }

    pub(super) fn logical_assumption(
        &mut self,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<Option<evidence::NodeId>> {
        let witnesses = self.proof.witnesses.values().copied().collect::<Vec<_>>();
        self.charge_value_work(witnesses.len())?;
        let mut admitted = None;
        for node in witnesses {
            let claim = self.proof.evidence.claim(node)?.clone();
            if self.witness_matches(node, &claim, goal, subjects)? {
                if self.evidence_dependencies(node)?.admissions.is_empty() {
                    return Ok(Some(node));
                }
                admitted.get_or_insert(node);
            }
        }
        if goal.is_arithmetic() {
            return Ok(admitted);
        }
        let candidates = if let Some(subjects) = subjects.filter(|s| s.complete) {
            self.proof
                .subjects
                .candidates(subjects)
                .intersection(&self.proof.claims)
                .copied()
                .collect::<Vec<_>>()
        } else {
            self.proof.claims.iter().copied().collect()
        };
        self.charge_value_work(candidates.len())?;
        for node in candidates {
            let claim = self.proof.evidence.claim(node)?.clone();
            self.charge_value_work(claim.storage_weight()?)?;
            if !claim.normalized().alpha_equal(&goal.normalized()) {
                continue;
            }
            let Some(snapshot) = self.proof.evidence.subjects(node).cloned() else {
                continue;
            };
            // An admission cannot jump to a different value merely because
            // elaboration simplified both propositions to the same formula.
            let trusted = !self.evidence_dependencies(node)?.admissions.is_empty();
            if trusted && !subjects.is_some_and(|goal| goal.complete && goal.key == snapshot.key) {
                continue;
            }
            let available = self.logical_claim_scope(node, &snapshot)?;
            let scope = self
                .reference_claim_scope(&snapshot, subjects)?
                .and(available);
            let Some(node) = self.guarded_claim_evidence(node, &scope)? else {
                continue;
            };
            if !trusted {
                return Ok(Some(node));
            }
            admitted.get_or_insert(node);
        }
        Ok(admitted)
    }

    pub(super) fn prove_logical_contract(
        &mut self,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
        label: &str,
        line: usize,
    ) -> Result<evidence::NodeId> {
        if let Some(node) = self.logical_assumption(goal, subjects)? {
            self.work.obligations += 1;
            return self
                .proof
                .evidence
                .derive(goal.clone(), evidence::Rule::Reuse(node));
        }
        // Implicit proofs use the same checked rules as source scripts. This
        // introduces arbitrary indices; it never samples or enumerates a range.
        let mut steps = Vec::new();
        if let Some(subjects) = subjects {
            self.charge_value_work(subjects.storage_weight()?)?;
        }
        let mut pending = vec![(goal, subjects.cloned(), 0)];
        while let Some((part, subjects, depth)) = pending.pop() {
            self.charge_value_work(1)?;
            if depth >= 64 || steps.len() >= 1024 {
                return Err(format!("line {line}: logical contract proof limit reached"));
            }
            if !part.is_arithmetic() && self.logical_assumption(part, subjects.as_ref())?.is_some()
            {
                steps.push("omega".into());
                continue;
            }
            match part {
                Formula::Forall { body, .. } => {
                    steps.push(format!("intro {}", self.fresh_name()));
                    pending.push((body, None, depth + 1));
                }
                Formula::And(a, b) if !part.is_arithmetic() => {
                    steps.push("constructor".into());
                    let left = subjects.as_ref().and_then(|s| s.branch("&&", false));
                    let right = subjects.as_ref().and_then(|s| s.branch("&&", true));
                    pending.push((b, right, depth + 1));
                    pending.push((a, left, depth + 1));
                }
                _ => steps.push("omega".into()),
            }
        }
        self.proof_script_for(goal, label, line, &steps, subjects)
    }
}
