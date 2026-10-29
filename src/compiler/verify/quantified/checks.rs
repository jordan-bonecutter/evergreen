//! Definedness obligations are checked over the domain before a quantified
//! formula becomes usable. Nested scopes preserve every enclosing binder.

use super::*;

pub(in crate::compiler::verify) struct Check {
    pub(super) condition: Formula,
    pub(super) label: String,
    pub(super) line: usize,
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn defer_quantified_check(
        &mut self,
        condition: Formula,
        label: String,
        line: usize,
    ) -> Result<()> {
        self.locals
            .quantified_checks
            .last_mut()
            .ok_or("missing quantified definedness scope")?
            .push(Check {
                condition,
                label,
                line,
            });
        Ok(())
    }

    pub(super) fn finish_quantified_checks(
        &mut self,
        variable: &str,
        domain: &Formula,
        checks: Vec<Check>,
    ) -> Result<()> {
        for check in checks {
            let goal = Formula::Forall {
                variable: variable.into(),
                domain: Box::new(domain.clone()),
                body: Box::new(check.condition),
            };
            self.charge_value_work(goal.storage_weight()?)?;
            if let Some(parent) = self.locals.quantified_checks.last_mut() {
                parent.push(Check {
                    condition: goal,
                    ..check
                });
                continue;
            }
            if let Some(&node) = self.proof.definedness.get(&goal) {
                self.proof.uses.push(node);
                continue;
            }
            if let Some(node) = self.independent_definedness(&goal)? {
                self.proof.evidence.check_closed(node)?;
                self.proof.definedness.insert(goal, node);
                self.proof.uses.push(node);
                continue;
            }
            let mut steps = Vec::new();
            let mut tail = &goal;
            while let Formula::Forall { body, .. } = tail {
                steps.push(format!("intro evg_definedness_check_{}", steps.len()));
                tail = body;
            }
            steps.push("omega".into());
            let node = self.proof_script_for(&goal, &check.label, check.line, &steps, None)?;
            self.proof.uses.push(node);
        }
        Ok(())
    }

    // No caller facts, claims, guards, or admissions enter this proof. Its only
    // premises are the domains introduced here and discharged by ForallIntro.
    fn independent_definedness(&mut self, goal: &Formula) -> Result<Option<evidence::NodeId>> {
        let mut domains = paths::Paths::unit();
        let mut tail = goal.clone();
        let mut frames = Vec::new();
        while let Formula::Forall {
            variable,
            domain,
            body,
        } = &tail
        {
            self.charge_value_work(tail.storage_weight()?)?;
            let eigenvariable = self.fresh_name();
            let term = Linear::variable(&eigenvariable);
            let domain = domain.substitute(variable, &term)?;
            let body = body.substitute(variable, &term)?;
            let (hypothesis, premise) = self.proof.evidence.hypothesis(domain.clone())?;
            domains = extend_from(
                &domains,
                &domain,
                false,
                paths::Origin::Evidence(premise),
                self.session,
                &mut self.work.value_work,
            )?;
            frames.push((tail, hypothesis, eigenvariable));
            tail = body;
        }
        if !tail.is_arithmetic() {
            return Ok(None);
        }
        let Some(support) = self.probe_guard(&domains, &tail)? else {
            return Ok(None);
        };
        self.work.obligations += 1;
        let mut node = self.proof.evidence.arithmetic(tail, support)?;
        for (claim, hypothesis, eigenvariable) in frames.into_iter().rev() {
            node = self.proof.evidence.derive(
                claim,
                evidence::Rule::ForallIntro {
                    hypothesis,
                    body: node,
                    eigenvariable,
                },
            )?;
        }
        Ok(Some(node))
    }
}
