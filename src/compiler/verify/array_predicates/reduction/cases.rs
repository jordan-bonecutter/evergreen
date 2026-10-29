//! Arithmetic guards can split a selector proof into checked logical cases.
//! The disjunction itself is proved by the ordinary arithmetic certificate.

use super::*;

impl Context<'_> {
    pub(super) fn reduce_selector_choice(
        &mut self,
        goal: &Formula,
        left: &Formula,
        right: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        let left_parts = [
            Some(left),
            match left {
                Formula::And(a, _) => Some(&**a),
                _ => None,
            },
        ];
        let right_parts = [
            Some(right),
            match right {
                Formula::And(a, _) => Some(&**a),
                _ => None,
            },
        ];
        for a in left_parts.into_iter().flatten() {
            for b in right_parts.into_iter().flatten() {
                if a.is_arithmetic() && b.normalized() == a.clone().not().normalized() {
                    return self.selector_arithmetic_cases(goal, a, depth + 1);
                }
            }
        }
        Ok(None)
    }

    pub(super) fn selector_arithmetic_cases(
        &mut self,
        goal: &Formula,
        guard: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        self.charge_value_work(guard.storage_weight()?)?;
        if self.selector_arithmetic_support(guard)?.is_some()
            || self
                .selector_arithmetic_support(&guard.clone().not())?
                .is_some()
        {
            return Ok(None);
        }
        let split = guard.clone().or(guard.clone().not());
        let support = self
            .probe_guard(&paths::Paths::unit(), &split)?
            .ok_or("arithmetic selector split could not be certified")?;
        self.work.obligations += 1;
        let source = self.proof.evidence.arithmetic(split, support)?;
        let (left_hypothesis, left) = self.proof.evidence.hypothesis(guard.clone())?;
        let (right_hypothesis, right) = self.proof.evidence.hypothesis(guard.clone().not())?;
        let name = self.fresh_name();
        let Some(left) = self.with_proof_hypotheses(&[(&name, left)], 0, |ctx| {
            ctx.reduce_selector_formula(goal, depth + 1)
        })?
        else {
            return Ok(None);
        };
        let name = self.fresh_name();
        let Some(right) = self.with_proof_hypotheses(&[(&name, right)], 0, |ctx| {
            ctx.reduce_selector_formula(goal, depth + 1)
        })?
        else {
            return Ok(None);
        };
        self.proof
            .evidence
            .derive(
                goal.clone(),
                evidence::Rule::OrElim {
                    source,
                    left_hypothesis,
                    left,
                    right_hypothesis,
                    right,
                },
            )
            .map(Some)
    }
}
