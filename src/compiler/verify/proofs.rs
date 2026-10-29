//! Small propositional proof rules. Arithmetic leaves still use certificates.

use super::*;
use evidence::Rule;

#[cfg(test)]
mod tests;
mod universal;
mod using;

struct Script<'a> {
    steps: &'a [String],
    next: usize,
    label: &'a str,
    line: usize,
}

impl<'a> Script<'a> {
    fn take(&mut self) -> Result<&'a str> {
        let step = self
            .steps
            .get(self.next)
            .ok_or_else(|| format!("line {}: proof has an unfinished goal", self.line))?;
        self.next += 1;
        Ok(step)
    }
}

impl Context<'_> {
    // Prefer the explicit local premises of a logical proof. Unrelated runtime
    // path closures must not become dependencies of a universally valid lemma.
    pub(super) fn scoped_arithmetic_support(
        &mut self,
        goal: &Formula,
    ) -> Result<Option<paths::Support>> {
        let nodes = self.proof.witnesses.values().copied().collect::<Vec<_>>();
        self.charge_value_work(nodes.len())?;
        let mut local = paths::Paths::unit();
        let mut scoped = false;
        for node in nodes {
            if self.proof.evidence.check_closed(node).is_ok() {
                continue;
            }
            self.charge_value_work(self.proof.evidence.claim(node)?.storage_weight()?)?;
            let claim = self.proof.evidence.claim(node)?.clone();
            if claim.is_arithmetic() {
                scoped = true;
                local = extend_from(
                    &local,
                    &claim,
                    false,
                    paths::Origin::Evidence(node),
                    self.session,
                    &mut self.work.value_work,
                )?;
            }
        }
        if scoped {
            self.probe_guard(&local, goal)
        } else {
            Ok(None)
        }
    }

    #[cfg(test)]
    pub(super) fn proof_script(
        &mut self,
        goal: &Formula,
        label: &str,
        line: usize,
        steps: &[String],
    ) -> Result<evidence::NodeId> {
        self.proof_script_for(goal, label, line, steps, None)
    }

    pub(super) fn proof_script_for(
        &mut self,
        goal: &Formula,
        label: &str,
        line: usize,
        steps: &[String],
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<evidence::NodeId> {
        if steps.len() > 1024 {
            return Err(format!(
                "line {line}: proof script limit reached (1024 steps)"
            ));
        }
        if steps.iter().any(|step| step == "trustme") {
            if steps.len() != 1 {
                return Err(format!(
                    "line {line}: trustme must be a single explicit proof term"
                ));
            }
            let mut proposition = Vec::new();
            goal.normalized().encode(&mut proposition);
            let rows = self
                .proof
                .paths
                .iter()
                .map(|path| path.to_vec())
                .collect::<Vec<_>>();
            let trust = self.session.trust(&rows, &proposition, line, label)?;
            self.work.obligations += 1;
            let node = self.proof.evidence.admit_source(goal.clone(), trust)?;
            debug_assert!(self.proof.evidence.admissions(node).complete);
            return Ok(node);
        }
        let mut script = Script {
            steps,
            next: 0,
            label,
            line,
        };
        let node = self
            .proof_goal(goal, &mut script, 0, subjects)
            .map_err(|error| {
                if error.starts_with("line ") {
                    error
                } else {
                    format!("line {line}: cannot prove {label}: {error}")
                }
            })?;
        if script.next != steps.len() {
            return Err(format!(
                "line {line}: unused proof steps after the goal was closed"
            ));
        }
        self.proof.evidence.check_closed(node)?;
        Ok(node)
    }

    fn same_proposition(&mut self, a: &Formula, b: &Formula) -> Result<bool> {
        self.charge_value_work(symbol_weight(&Symbol::Bool(a.clone()))?)?;
        // Identical syntax needs no normalization or second formula copy.
        // State/admission checks still run in witness_matches after this test.
        if a == b {
            return Ok(true);
        }
        self.charge_value_work(symbol_weight(&Symbol::Bool(b.clone()))?)?;
        Ok(a.normalized().alpha_equal(&b.normalized()))
    }

    pub(super) fn witness_matches(
        &mut self,
        node: evidence::NodeId,
        claim: &Formula,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<bool> {
        if !self.same_proposition(claim, goal)? {
            return Ok(false);
        }
        if !self.proof.evidence.has_admissions(node) {
            return Ok(true);
        }
        let Some(snapshot) = self
            .proof
            .evidence
            .subjects(node)
            .or_else(|| self.proof.scoped_subjects.get(&node))
        else {
            return Ok(true);
        };
        Ok(self
            .proof
            .subjects
            .current(snapshot, &self.storage.memory)?
            && subjects.is_some_and(|goal| goal.complete && snapshot.key == goal.key))
    }

    fn require_live_witness(
        &mut self,
        node: evidence::NodeId,
        name: &str,
        line: usize,
    ) -> Result<()> {
        if !self.proof.evidence.has_admissions(node) {
            return Ok(());
        }
        if let Some(snapshot) = self
            .proof
            .evidence
            .subjects(node)
            .or_else(|| self.proof.scoped_subjects.get(&node))
        {
            if !self
                .proof
                .subjects
                .current(snapshot, &self.storage.memory)?
            {
                return Err(format!(
                    "line {line}: proof {name} refers to an earlier or unresolved state"
                ));
            }
        }
        Ok(())
    }

    pub(super) fn with_proof_hypotheses<T>(
        &mut self,
        hypotheses: &[(&str, evidence::NodeId)],
        line: usize,
        check: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let mut names = BTreeSet::new();
        for (name, node) in hypotheses {
            self.fresh_binding(name, line)?;
            if !names.insert(*name) {
                return Err(format!("line {line}: duplicate proof hypothesis {name}"));
            }
            self.charge_value_work(symbol_weight(&Symbol::Bool(
                self.proof.evidence.claim(*node)?.clone(),
            ))?)?;
        }
        let snapshot_work = self.proof.paths.iter().fold(0usize, |total, path| {
            path.iter().fold(total, |total, row| {
                total.saturating_add(1usize.saturating_add(row.terms.len()))
            })
        });
        self.charge_value_work(snapshot_work)?;
        let paths = self.proof.paths.clone();
        let result = (|| {
            for (name, node) in hypotheses {
                let premise = self.proof.evidence.claim(*node)?.clone();
                self.proof.witnesses.insert((*name).into(), *node);
                // Quantifiers and predicate atoms remain scoped logical
                // witnesses. Only arithmetic propositions become solver rows;
                // specialization and cases must expose their consequences.
                if premise.is_arithmetic() {
                    self.assume_from(&premise, paths::Origin::Evidence(*node))?;
                }
            }
            check(self)
        })();
        for (name, _) in hypotheses {
            self.proof.witnesses.remove(*name);
        }
        self.proof.paths = paths;
        result
    }

    fn unreachable_logical_goal(&mut self, goal: &Formula) -> Result<Option<evidence::NodeId>> {
        if let Some(support) = self.scoped_arithmetic_support(&Formula::False)? {
            let impossible = self.proof.evidence.arithmetic(Formula::False, support)?;
            return self
                .proof
                .evidence
                .derive(goal.clone(), Rule::FalseElim(impossible))
                .map(Some);
        }
        let paths = self.proof.paths.clone();
        let Some(support) = self.probe_guard(&paths, &Formula::False)? else {
            return Ok(None);
        };
        for &parent in &support.parents {
            if self.proof.evidence.has_admissions(parent)
                || self.proof.evidence.has_pending_summaries(parent)
            {
                return Ok(None);
            }
        }
        // Empty quantified domains need no facts about an arbitrary slot.
        // Keep local hypotheses open until the enclosing introduction rule
        // discharges them; runtime reachability checks require closed proofs.
        self.work.obligations += 1;
        let contradiction = self.proof.evidence.arithmetic(Formula::False, support)?;
        self.proof
            .evidence
            .derive(goal.clone(), Rule::FalseElim(contradiction))
            .map(Some)
    }

    fn proof_goal(
        &mut self,
        goal: &Formula,
        script: &mut Script<'_>,
        depth: usize,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<evidence::NodeId> {
        let label = script.label;
        let line = script.line;
        if depth >= 64 {
            return Err(format!(
                "line {line}: proof goal nesting limit reached (64)"
            ));
        }
        self.charge_value_work(1)?;
        let step = script.take()?;
        match step {
            "omega" | "rfl" | "simp_all" | "decide" => {
                if goal.is_arithmetic() {
                    if let Some(support) = self.scoped_arithmetic_support(goal)? {
                        self.work.obligations += 1;
                        return self.proof.evidence.arithmetic(goal.clone(), support);
                    }
                }
                if !goal.is_arithmetic() {
                    if let Some(node) = self.logical_assumption(goal, subjects)? {
                        return self.proof.evidence.derive(goal.clone(), Rule::Reuse(node));
                    }
                    if let Some(node) = self.unreachable_logical_goal(goal)? {
                        return Ok(node);
                    }
                }
                if let Some(proven) = self.prove_indexed_value_equality(goal)? {
                    return Ok(proven);
                }
                if let Some(proven) = self.prove_indexed_predicate(goal, subjects, label, line)? {
                    return Ok(proven);
                }
                let parents = self.arithmetic_support_for(goal, subjects, label, line)?;
                self.proof.evidence.arithmetic(goal.clone(), parents)
            }
            "assumption" => {
                if let Some(node) = self.logical_assumption(goal, subjects)? {
                    self.work.obligations += 1;
                    return self.proof.evidence.derive(goal.clone(), Rule::Reuse(node));
                }
                Err(format!(
                    "line {line}: cannot prove {label}: assumption found no checked proof of this proposition"
                ))
            }
            "constructor" => {
                let Formula::And(a, b) = goal else {
                    return Err(format!(
                        "line {line}: constructor requires a conjunction goal"
                    ));
                };
                let left_subjects = subjects.and_then(|s| s.branch("&&", false));
                let right_subjects = subjects.and_then(|s| s.branch("&&", true));
                let a = self.proof_goal(a, script, depth + 1, left_subjects.as_ref())?;
                let b = self.proof_goal(b, script, depth + 1, right_subjects.as_ref())?;
                self.proof
                    .evidence
                    .derive(goal.clone(), Rule::AndIntro(a, b))
            }
            "left" | "right" => {
                let Formula::Or(a, b) = goal else {
                    return Err(format!("line {line}: {step} requires a disjunction goal"));
                };
                let branch_subjects = subjects.and_then(|s| s.branch("||", step == "right"));
                let premise = self.proof_goal(
                    if step == "left" { a } else { b },
                    script,
                    depth + 1,
                    branch_subjects.as_ref(),
                )?;
                let rule = if step == "left" {
                    Rule::OrLeft(premise)
                } else {
                    Rule::OrRight(premise)
                };
                self.proof.evidence.derive(goal.clone(), rule)
            }
            _ if step.starts_with("using ") => {
                self.using_proof(goal, &step[6..], script, depth, subjects)
            }
            _ if step.starts_with("exact ") => {
                let name = &step[6..];
                let proven = self.proof.witnesses.get(name).cloned().ok_or_else(|| format!("line {line}: {name} is not a checked proof; fact declarations are propositions, not assumptions"))?;
                let claim = self.proof.evidence.claim(proven)?.clone();
                if !self.witness_matches(proven, &claim, goal, subjects)? {
                    return Err(format!("line {line}: exact {name} proves a different proposition or an earlier state"));
                }
                self.work.obligations += 1;
                self.proof
                    .evidence
                    .derive(goal.clone(), Rule::Reuse(proven))
            }
            _ if step.starts_with("intro ") => {
                if matches!(goal, Formula::Forall { .. }) {
                    return self.introduce_universal(goal, &step[6..], script, depth, subjects);
                }
                let (premise, consequence) = match goal {
                    Formula::Implies(a, b) => (&**a, &**b),
                    Formula::Not(a) => (&**a, &Formula::False),
                    _ => {
                        return Err(format!(
                            "line {line}: intro requires a universal, implication, or negation goal"
                        ))
                    }
                };
                let name = &step[6..];
                let consequence_subjects = subjects.and_then(|s| s.branch("=>", true));
                let (hypothesis, premise_node) = self.proof.evidence.hypothesis(premise.clone())?;
                let consequence =
                    self.with_proof_hypotheses(&[(name, premise_node)], line, |ctx| {
                        ctx.proof_goal(
                            consequence,
                            script,
                            depth + 1,
                            consequence_subjects.as_ref(),
                        )
                    })?;
                self.proof.evidence.derive(
                    goal.clone(),
                    Rule::ImpIntro {
                        hypothesis,
                        body: consequence,
                    },
                )
            }
            _ if step.starts_with("specialize ") => {
                self.specialize_universal(goal, step, script, depth, subjects)
            }
            _ if step.starts_with("cases ") => {
                let parts = step.split_whitespace().collect::<Vec<_>>();
                if let ["cases", name] = parts.as_slice() {
                    let node = self.proof.witnesses.get(*name).copied();
                    if !node.is_some_and(|id| {
                        matches!(self.proof.evidence.claim(id), Ok(Formula::False))
                    }) {
                        return Err(format!("line {line}: cases {name} without a pattern requires a checked proof of false"));
                    }
                    self.require_live_witness(node.unwrap(), name, line)?;
                    self.work.obligations += 1;
                    return self
                        .proof
                        .evidence
                        .derive(goal.clone(), Rule::FalseElim(node.unwrap()));
                }
                let ["cases", name, "with", first, separator, second] = parts.as_slice() else {
                    return Err(format!("line {line}: malformed cases step"));
                };
                let theorem =
                    self.proof.witnesses.get(*name).cloned().ok_or_else(|| {
                        format!("line {line}: cases {name} requires a checked proof")
                    })?;
                self.require_live_witness(theorem, name, line)?;
                let claim = self.proof.evidence.claim(theorem)?.clone();
                match (claim, *separator) {
                    (Formula::And(a, b), ",") => {
                        let left = self.proof.evidence.derive(*a, Rule::AndLeft(theorem))?;
                        let right = self.proof.evidence.derive(*b, Rule::AndRight(theorem))?;
                        let branch = self.with_proof_hypotheses(&[(first, left), (second, right)], line, |ctx| {
                            ctx.proof_goal(goal, script, depth + 1, subjects)
                        })?;
                        self.proof.evidence.derive(goal.clone(), Rule::Reuse(branch))
                    }
                    (Formula::Or(a, b), "|") => {
                        // Validate both names before starting either branch.
                        self.fresh_binding(first, line)?;
                        self.fresh_binding(second, line)?;
                        let (left_hypothesis, left_node) = self.proof.evidence.hypothesis(*a)?;
                        let (right_hypothesis, right_node) = self.proof.evidence.hypothesis(*b)?;
                        let left = self.with_proof_hypotheses(&[(first, left_node)], line, |ctx| {
                            ctx.proof_goal(goal, script, depth + 1, subjects)
                        })?;
                        let right = self.with_proof_hypotheses(&[(second, right_node)], line, |ctx| {
                            ctx.proof_goal(goal, script, depth + 1, subjects)
                        })?;
                        self.proof.evidence.derive(goal.clone(), Rule::OrElim {
                            source: theorem, left_hypothesis, left, right_hypothesis, right,
                        })
                    }
                    _ => Err(format!("line {line}: cases requires a conjunction with ',' or a disjunction with '|'")),
                }
            }
            _ if step.starts_with("apply ") => {
                let name = &step[6..];
                let source =
                    self.proof.witnesses.get(name).copied().ok_or_else(|| {
                        format!("line {line}: apply {name} requires a checked proof")
                    })?;
                self.require_live_witness(source, name, line)?;
                let mut theorem = self.proof.evidence.claim(source)?.clone();
                let mut theorem_subjects = self
                    .proof
                    .evidence
                    .subjects(source)
                    .or_else(|| self.proof.scoped_subjects.get(&source))
                    .cloned();
                let mut premises = Vec::new();
                while !self.same_proposition(&theorem, goal)? {
                    match theorem {
                        Formula::Implies(premise, consequence) => {
                            let premise_subjects = theorem_subjects
                                .as_ref()
                                .and_then(|s| s.branch("=>", false));
                            premises.push((*premise, premise_subjects));
                            theorem_subjects =
                                theorem_subjects.as_ref().and_then(|s| s.branch("=>", true));
                            theorem = *consequence;
                        }
                        Formula::Not(premise) => {
                            premises.push((*premise, None));
                            theorem_subjects = None;
                            theorem = Formula::False;
                        }
                        _ => {
                            return Err(format!(
                                "line {line}: apply {name} does not conclude this goal"
                            ))
                        }
                    }
                }
                if self.proof.evidence.has_admissions(source) {
                    if let Some(conclusion) = &theorem_subjects {
                        if !subjects.is_some_and(|goal| goal.complete && goal.key == conclusion.key)
                        {
                            return Err(format!(
                                "line {line}: apply {name} concludes a different subject or state"
                            ));
                        }
                    }
                }
                let mut applied = source;
                for (premise, premise_subjects) in premises {
                    let argument =
                        self.proof_goal(&premise, script, depth + 1, premise_subjects.as_ref())?;
                    let conclusion = match self.proof.evidence.claim(applied)? {
                        Formula::Implies(_, result) => (**result).clone(),
                        Formula::Not(_) => Formula::False,
                        _ => return Err("application lost its implication premise".into()),
                    };
                    applied = self.proof.evidence.derive(
                        conclusion,
                        Rule::ImpElim {
                            theorem: applied,
                            argument,
                        },
                    )?;
                }
                self.work.obligations += 1;
                self.proof
                    .evidence
                    .derive(goal.clone(), Rule::Reuse(applied))
            }
            _ => Err(format!("line {line}: unsupported proof step {step}")),
        }
    }
}
