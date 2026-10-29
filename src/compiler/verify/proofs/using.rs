//! Explicit proof transformation using the existing implication rules.

use super::*;

impl Context<'_> {
    pub(super) fn using_proof(
        &mut self,
        goal: &Formula,
        name: &str,
        script: &mut Script<'_>,
        depth: usize,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<evidence::NodeId> {
        let source = self.proof.witnesses.get(name).copied().ok_or_else(|| {
            format!(
                "line {}: using {name} requires a checked proof",
                script.line
            )
        })?;
        self.require_live_witness(source, name, script.line)?;
        let premise = self.proof.evidence.claim(source)?.clone();
        self.charge_value_work(
            premise
                .storage_weight()?
                .saturating_add(goal.storage_weight()?),
        )?;
        let implication = Formula::Implies(Box::new(premise), Box::new(goal.clone()));
        let premise_subjects = self
            .proof
            .evidence
            .subjects(source)
            .or_else(|| self.proof.scoped_subjects.get(&source));
        let implication_subjects = premise_subjects.zip(subjects).and_then(|(before, after)| {
            if !before.complete || !after.complete {
                return None;
            }
            Some(subjects::Snapshot::from_key(subjects::ClaimKey::Binary(
                "=>".into(),
                Box::new(before.key.clone()?),
                Box::new(after.key.clone()?),
            )))
        });
        if let Some(snapshot) = &implication_subjects {
            self.charge_value_work(snapshot.storage_weight()?)?;
        }
        // The continuation proves a theorem about immutable proposition values.
        // Its conclusion retains the requested current-state subjects.
        let theorem = self.proof_goal(
            &implication,
            script,
            depth + 1,
            implication_subjects.as_ref(),
        )?;
        self.proof.evidence.derive(
            goal.clone(),
            Rule::ImpElim {
                theorem,
                argument: source,
            },
        )
    }
}
