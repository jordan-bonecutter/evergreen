//! Universal tactics select scoped eigenvariables and specialization terms.
//! The evidence kernel checks the rule; subjects preserve source state identity.

use super::*;

#[cfg(test)]
mod tests;

impl Context<'_> {
    pub(super) fn introduce_universal(
        &mut self,
        goal: &Formula,
        name: &str,
        script: &mut Script<'_>,
        depth: usize,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<evidence::NodeId> {
        let line = script.line;
        let Formula::Forall {
            variable,
            domain,
            body,
        } = goal
        else {
            return Err(format!(
                "line {line}: universal introduction requires a universal goal"
            ));
        };
        self.fresh_binding(name, line)?;
        let eigenvariable = self.fresh_name();
        let term = Linear::variable(&eigenvariable);
        let domain = domain.substitute(variable, &term)?;
        let body = body.substitute(variable, &term)?;
        let argument = subjects::Snapshot::from_key(subjects::ClaimKey::LogicalVariable(
            eigenvariable.clone(),
        ));
        let parts = match subjects {
            Some(subjects) => subjects.universal_parts(&argument, &mut self.work.value_work)?,
            None => None,
        };
        let (hypothesis, premise) = self.proof.evidence.hypothesis(domain)?;
        let internal = format!("evg_domain_{}", self.work.fresh);
        let consequence = self.with_logical_binding(name, &eigenvariable, false, |ctx| {
            ctx.with_proof_hypotheses(&[(&internal, premise)], line, |ctx| {
                ctx.proof_goal(
                    &body,
                    script,
                    depth + 1,
                    parts.as_ref().map(|(_, body)| body),
                )
            })
        })?;
        self.proof.evidence.derive(
            goal.clone(),
            Rule::ForallIntro {
                hypothesis,
                body: consequence,
                eigenvariable,
            },
        )
    }

    pub(super) fn specialize_universal(
        &mut self,
        goal: &Formula,
        step: &str,
        script: &mut Script<'_>,
        depth: usize,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<evidence::NodeId> {
        let line = script.line;
        let parts = step.split_whitespace().collect::<Vec<_>>();
        let (name, argument, binding) = match parts.as_slice() {
            ["specialize", name, argument] => (*name, *argument, None),
            ["specialize", name, argument, "as", binding] => (*name, *argument, Some(*binding)),
            _ => return Err(format!("line {line}: malformed specialization step")),
        };
        if let Some(binding) = binding {
            self.fresh_binding(binding, line)?;
        }
        let theorem = self.proof.witnesses.get(name).copied().ok_or_else(|| {
            format!("line {line}: specialize {name} requires a checked universal proof")
        })?;
        self.require_live_witness(theorem, name, line)?;
        let Formula::Forall {
            variable,
            domain,
            body,
        } = self.proof.evidence.claim(theorem)?.clone()
        else {
            return Err(format!(
                "line {line}: specialize {name} requires a universal proof"
            ));
        };
        let (term, term_subjects) = self.quantified_argument(argument, line)?;
        let expected = body.substitute(&variable, &term)?;
        if binding.is_none() && !self.same_proposition(&expected, goal)? {
            return Err(format!(
                "line {line}: specialize {name} proves a different proposition"
            ));
        }
        let parts = match self
            .proof
            .evidence
            .subjects(theorem)
            .or_else(|| self.proof.scoped_subjects.get(&theorem))
        {
            Some(subjects) => {
                subjects.universal_parts(&term_subjects, &mut self.work.value_work)?
            }
            None => None,
        };
        let preserves_subjects = parts.as_ref().is_some_and(|(_, body)| {
            body.complete
                && (binding.is_some()
                    || subjects.is_some_and(|goal| goal.complete && goal.key == body.key))
        });
        if !self.evidence_dependencies(theorem)?.admissions.is_empty() && !preserves_subjects {
            return Err(format!(
                "line {line}: specialize {name} concludes a different subject or state"
            ));
        }
        let domain = self.proof_goal(
            &domain.substitute(&variable, &term)?,
            script,
            depth + 1,
            parts.as_ref().map(|(domain, _)| domain),
        )?;
        let instance = self.proof.evidence.derive(
            if binding.is_some() {
                expected
            } else {
                goal.clone()
            },
            Rule::ForallElim {
                theorem,
                domain,
                term,
            },
        )?;
        if let Some(binding) = binding {
            // Intermediate subjects stay local, including when the instance
            // depends on an open quantifier domain. Nothing is published yet.
            if let Some((_, body)) = parts {
                self.charge_value_work(body.storage_weight()?)?;
                self.proof.scoped_subjects.insert(instance, body);
            }
            let result = self.with_proof_hypotheses(&[(binding, instance)], line, |ctx| {
                ctx.proof_goal(goal, script, depth + 1, subjects)
            });
            self.proof.scoped_subjects.remove(&instance);
            result
        } else {
            Ok(instance)
        }
    }
}
