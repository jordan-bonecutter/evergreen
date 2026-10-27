//! Apply historical frames once per branch condition. Repeating an implication
//! for every fact would enumerate the same case split exponentially.

use super::*;

impl Context<'_> {
    pub(super) fn reference_claim_scope(
        &mut self,
        snapshot: &subjects::Snapshot,
        goal: Option<&subjects::Snapshot>,
    ) -> Result<Formula> {
        let Some(goal) = goal.filter(|goal| goal.complete) else {
            return Ok(Formula::True);
        };
        if snapshot.key == goal.key {
            return Ok(Formula::True);
        };
        let (a_guarded, a) = snapshot.guarded_reads(false)?;
        let (b_guarded, b) = goal.guarded_reads(false)?;
        if !a_guarded && !b_guarded {
            return Ok(Formula::True);
        };
        let mut scope = Formula::False;
        for (a, a_guard) in &a {
            for (b, b_guard) in &b {
                self.charge_value_work(1 + a_guard.storage_weight()? + b_guard.storage_weight()?)?;
                let aliases = self.proof.subjects.same_read_region(*a, *b)?;
                scope = scope.or(a_guard.clone().and(b_guard.clone()).and(aliases));
            }
        }
        Ok(scope)
    }

    fn probe_guard(
        &mut self,
        paths: &paths::Paths,
        guard: &Formula,
    ) -> Result<Option<paths::Support>> {
        let negated = extend_from(
            paths,
            guard,
            true,
            paths::Origin::NegatedGoal,
            self.session,
            &mut self.work.value_work,
        )?;
        let mut support = negated.closed.clone();
        for path in negated.iter() {
            let Some(rows) = self.session.probe_with_support(path)? else {
                return Ok(None);
            };
            support.add_rows(path, &rows);
        }
        Ok(Some(support))
    }

    fn extend_candidates(
        &mut self,
        mut paths: paths::Paths,
        candidates: &[evidence::NodeId],
    ) -> Result<paths::Paths> {
        for &node in candidates {
            paths = extend_from(
                &paths,
                self.proof.evidence.claim(node)?,
                false,
                paths::Origin::Evidence(node),
                self.session,
                &mut self.work.value_work,
            )?;
        }
        Ok(paths)
    }

    fn apply_guarded(
        &mut self,
        paths: paths::Paths,
        theorem: evidence::NodeId,
        candidates: &[evidence::NodeId],
    ) -> Result<paths::Paths> {
        let mut conclusions = Vec::new();
        for &node in candidates {
            let Formula::Implies(_, consequence) = self.proof.evidence.claim(node)? else {
                return Err("historical frame lost its condition".into());
            };
            conclusions.push(self.proof.evidence.derive(
                (**consequence).clone(),
                evidence::Rule::ImpElim {
                    theorem: node,
                    argument: theorem,
                },
            )?);
        }
        self.extend_candidates(paths, &conclusions)
    }

    pub(super) fn candidate_paths(
        &mut self,
        candidates: &[evidence::NodeId],
    ) -> Result<paths::Paths> {
        let mut ordinary = Vec::new();
        let mut guarded: BTreeMap<Formula, Vec<evidence::NodeId>> = BTreeMap::new();
        for &node in candidates {
            if let Some(guard) = self.proof.evidence.guarded_condition(node) {
                guarded.entry(guard).or_default().push(node);
            } else {
                ordinary.push(node);
            }
        }
        let mut result = paths::Paths::from(Vec::new());
        result.closed = self.proof.paths.closed.clone();
        for base in self.proof.paths.iter().cloned().collect::<Vec<_>>() {
            // Resolve frame conditions using checked execution facts. Candidate
            // admissions cannot decide whether an old revision is applicable.
            let checked = paths::Paths::from(vec![base]);
            let mut temporary = self.extend_candidates(checked.clone(), &ordinary)?;
            for (guard, candidates) in &guarded {
                if let Some(support) = self.probe_guard(&checked, guard)? {
                    let theorem = self.proof.evidence.arithmetic(guard.clone(), support)?;
                    temporary = self.apply_guarded(temporary, theorem, candidates)?;
                } else if self.probe_guard(&checked, &guard.clone().not())?.is_none() {
                    // If the execution context does not decide the condition,
                    // check both cases, adding all same-guard facts together.
                    let positive = extend_from(
                        &checked,
                        guard,
                        false,
                        paths::Origin::Unresolved,
                        self.session,
                        &mut self.work.value_work,
                    )?;
                    let support = self
                        .probe_guard(&positive, guard)?
                        .ok_or("case condition failed to establish itself")?;
                    let theorem = self.proof.evidence.arithmetic(guard.clone(), support)?;
                    let yes = extend_from(
                        &temporary,
                        guard,
                        false,
                        paths::Origin::Evidence(theorem),
                        self.session,
                        &mut self.work.value_work,
                    )?;
                    let no = extend_from(
                        &temporary,
                        guard,
                        true,
                        paths::Origin::Unresolved,
                        self.session,
                        &mut self.work.value_work,
                    )?;
                    temporary = self.apply_guarded(yes, theorem, candidates)?;
                    temporary.extend(no);
                    temporary = paths::bounded(temporary, self.session, &mut self.work.value_work)?;
                }
            }
            result.extend(temporary);
        }
        paths::bounded(result, self.session, &mut self.work.value_work)
    }
}
