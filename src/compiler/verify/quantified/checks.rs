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
            let mut steps = Vec::new();
            let mut tail = &goal;
            let mut domains = paths::Paths::unit();
            while let Formula::Forall { domain, body, .. } = tail {
                domains = extend(
                    &domains,
                    domain,
                    false,
                    self.session,
                    &mut self.work.value_work,
                )?;
                steps.push(format!("intro evg_definedness_check_{}", steps.len()));
                tail = body;
            }
            steps.push("omega".into());
            // Preconditions often follow from the quantified domains alone. Prove
            // those in an independent context so unrelated storage case splits
            // cannot introduce imported dependencies into ForallIntro.
            let independent = self.probe_guard(&domains, tail)?.is_some();
            let saved =
                independent.then(|| std::mem::replace(&mut self.proof.paths, paths::Paths::unit()));
            let result = self.proof_script_for(&goal, &check.label, check.line, &steps, None);
            if let Some(saved) = saved {
                self.proof.paths = saved;
            }
            let node = result?;
            self.proof.uses.push(node);
        }
        Ok(())
    }
}
