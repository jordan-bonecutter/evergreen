//! Case proofs for resource states that cannot be merged. Each leaf checks the
//! complete continuation in its own concrete storage world. Compatible bodies
//! keep the ordinary joined pass; only an incompatible resource join retries.
//! Replaying a prefix is bootstrap work, charged across the entire case tree.

use super::*;
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Site {
    function: Option<String>,
    line: usize,
    guard: Formula,
}

#[derive(Clone)]
struct Decision {
    site: Site,
    yes: bool,
}

enum Request {
    Separate,
    Fork(Vec<Decision>),
    Closed,
}

#[derive(PartialEq, Eq, Hash)]
enum ResultKey {
    Decision(Vec<bool>),
    Source {
        function: Option<String>,
        expression: Expr,
        expected: Option<Ty>,
    },
}

#[derive(Default)]
struct SyntaxWeight(usize);

impl Hasher for SyntaxWeight {
    fn write(&mut self, bytes: &[u8]) {
        self.0 = self.0.saturating_add(bytes.len());
    }

    fn finish(&self) -> u64 {
        0
    }
}

#[derive(Default)]
pub(super) struct Trace {
    plan: Option<Vec<Decision>>,
    visited: Vec<Decision>,
    outputs: Vec<(ResultKey, Site, Ty)>,
    request: Option<Request>,
}

pub(super) fn check(
    function: &Function,
    declarations: Declarations<'_>,
    session: &mut Session,
) -> Result<(usize, bool, summaries::Summary)> {
    let mut pending = vec![None];
    let mut requirements = summaries::Requirements::default();
    let mut output_types: HashMap<ResultKey, (Site, Ty)> = HashMap::new();
    let mut obligations = 0;
    let mut partial = false;
    let mut value_work = 0;
    let mut eval_steps = 0;
    while let Some(plan) = pending.pop() {
        let mut context = Context::new(declarations, session);
        context.cases.plan = plan;
        context.work.value_work = value_work;
        context.work.eval_steps = eval_steps;
        let checked = context
            .enter_function(function)
            .and_then(|()| context.check_declaration_body(function));
        value_work = context.work.value_work;
        eval_steps = context.work.eval_steps;
        obligations += context.work.obligations;
        match context.cases.request.take() {
            Some(Request::Separate) => pending.push(Some(Vec::new())),
            Some(Request::Fork(prefix)) => {
                for yes in [false, true] {
                    let mut next = prefix.clone();
                    next.last_mut().ok_or("empty resource case fork")?.yes = yes;
                    pending.push(Some(next));
                }
            }
            Some(Request::Closed) => {}
            None => {
                checked?;
                if context
                    .cases
                    .plan
                    .as_ref()
                    .is_some_and(|plan| context.cases.visited.len() < plan.len())
                {
                    return Err("resource case replay ended before its saved decisions".into());
                }
                partial |= context.execution.partial_execution;
                requirements.extend(context.declaration_requirements()?);
            }
        }
        for (key, site, ty) in context.cases.outputs {
            if let Some((previous_site, previous_type)) = output_types.get(&key) {
                if (matches!(key, ResultKey::Decision(_)) && previous_site != &site)
                    || previous_type != &ty
                {
                    return Err(format!(
                        "line {}: resource case branches must have the same result type",
                        site.line
                    ));
                }
            } else {
                output_types.insert(key, (site, ty));
            }
        }
    }
    Ok((obligations, partial, requirements.summary()))
}

impl Context<'_> {
    pub(super) fn resource_join_error<T>(&mut self, message: String) -> Result<T> {
        if self.execution.phase == Phase::Runtime && self.cases.plan.is_none() {
            self.charge_value_work(1)?;
            self.cases.request = Some(Request::Separate);
        }
        Err(message)
    }

    pub(super) fn separate_cases(&self) -> bool {
        self.execution.phase == Phase::Runtime && self.cases.plan.is_some()
    }

    pub(super) fn specification_case(&self) -> bool {
        self.execution.phase == Phase::Specification && self.cases.plan.is_some()
    }

    pub(super) fn select_case(&mut self, guard: &Formula, line: usize) -> Result<bool> {
        if self.cases.request.is_some() {
            return Err("resource case continuation is pending".into());
        }
        let site = Site {
            function: self.execution.current.clone(),
            line,
            guard: guard.clone(),
        };
        self.charge_value_work(1 + guard.storage_weight()? + self.cases.visited.len())?;
        let next = self
            .cases
            .plan
            .as_ref()
            .and_then(|plan| plan.get(self.cases.visited.len()))
            .cloned();
        let yes = if let Some(decision) = next {
            if decision.site != site {
                return Err("resource case replay changed its control-flow trace".into());
            }
            decision.yes
        } else if self.checked_entails(guard)? {
            true
        } else if self.checked_entails(&guard.clone().not())? {
            false
        } else {
            // The driver proves both continuations. A request is internal
            // control flow, never a source axiom or an exported summary.
            let weight = self.cases.visited.iter().try_fold(
                1 + guard.storage_weight()?,
                |weight, decision| -> Result<usize> {
                    Ok(weight.saturating_add(1 + decision.site.guard.storage_weight()?))
                },
            )?;
            self.charge_value_work(weight.saturating_mul(3))?;
            let mut prefix = self.cases.visited.clone();
            prefix.push(Decision { site, yes: false });
            self.cases.request = Some(Request::Fork(prefix));
            return Err("resource case continuations require separate checking".into());
        };
        let selected = if yes {
            guard.clone()
        } else {
            guard.clone().not()
        };
        if self.checked_entails(&selected.clone().not())? {
            self.cases.request = Some(Request::Closed);
            return Err("resource case is checked unreachable".into());
        }
        self.cases.visited.push(Decision { site, yes });
        self.proof.paths = extend(
            &self.proof.paths,
            &selected,
            false,
            self.session,
            &mut self.work.value_work,
        )?;
        self.proof.control = Some(
            self.proof
                .control
                .clone()
                .unwrap_or(Formula::True)
                .and(selected),
        );
        Ok(yes)
    }

    pub(super) fn record_case_result(&mut self, key: Vec<bool>, value: &Symbol) -> Result<()> {
        let decision = self
            .cases
            .visited
            .get(key.len())
            .ok_or("missing resource case decision")?;
        let site = decision.site.clone();
        self.charge_value_work(key.len() + symbol_weight(value)?)?;
        self.cases
            .outputs
            .push((ResultKey::Decision(key), site, value.ty()));
        Ok(())
    }

    pub(super) fn record_source_case_result(
        &mut self,
        expression: &Expr,
        expected: Option<&Ty>,
        value: &Symbol,
    ) -> Result<()> {
        // Prefix keys alone miss a later conditional whose guard has become
        // known differently in earlier cases. Its lexical source type must
        // also agree. HashMap compares complete syntax, including on a hash
        // collision; the work charge includes traversing and cloning that key.
        let mut weight = SyntaxWeight::default();
        expression.hash(&mut weight);
        expected.hash(&mut weight);
        self.charge_value_work(weight.0.saturating_mul(3))?;
        let key = ResultKey::Source {
            function: self.execution.current.clone(),
            expression: expression.clone(),
            expected: expected.cloned(),
        };
        let site = Site {
            function: self.execution.current.clone(),
            line: expression.line,
            guard: Formula::True,
        };
        self.cases.outputs.push((key, site, value.ty()));
        Ok(())
    }

    pub(super) fn case_key(&self) -> Vec<bool> {
        self.cases
            .visited
            .iter()
            .map(|decision| decision.yes)
            .collect()
    }
}
