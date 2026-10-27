//! Small propositional proof rules. Arithmetic leaves still use certificates.

use super::*;

impl Formula {
    // Retain connective structure for introduction/elimination rules, while
    // exact matching keeps the existing normalization of logical expressions.
    pub(super) fn normalized(&self) -> Self {
        match self {
            Self::And(a, b) => a.normalized().and(b.normalized()),
            Self::Or(a, b) => a.normalized().or(b.normalized()),
            Self::Implies(a, b) => a.normalized().not().or(b.normalized()),
            Self::Not(p) => p.normalized().not(),
            _ => self.clone(),
        }
    }
}

impl Context<'_> {
    pub(super) fn proof_script(
        &mut self,
        goal: &Formula,
        label: &str,
        line: usize,
        steps: &[String],
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
            self.session.trust(&rows, &proposition, line, label)?;
            self.work.obligations += 1;
            let node = self.proof.evidence.insert(goal.clone(), vec![], true)?;
            debug_assert!(self.proof.evidence.admissions(node).complete);
            return Ok(node);
        }
        let mut next = 0;
        let node = self.proof_goal(goal, label, line, steps, &mut next, 0)?;
        if next != steps.len() {
            return Err(format!(
                "line {line}: unused proof steps after the goal was closed"
            ));
        }
        Ok(node)
    }

    fn same_proposition(&mut self, a: &Formula, b: &Formula) -> Result<bool> {
        self.charge_value_work(symbol_weight(&Symbol::Bool(a.clone()))?)?;
        self.charge_value_work(symbol_weight(&Symbol::Bool(b.clone()))?)?;
        Ok(a.normalized() == b.normalized())
    }

    fn with_proof_hypotheses(
        &mut self,
        hypotheses: &[(&str, &Formula)],
        parents: &[evidence::NodeId],
        line: usize,
        check: impl FnOnce(&mut Self) -> Result<evidence::NodeId>,
    ) -> Result<evidence::NodeId> {
        let mut names = BTreeSet::new();
        for (name, premise) in hypotheses {
            self.fresh_binding(name, line)?;
            if !names.insert(*name) {
                return Err(format!("line {line}: duplicate proof hypothesis {name}"));
            }
            self.charge_value_work(symbol_weight(&Symbol::Bool((*premise).clone()))?)?;
        }
        let snapshot_work = self.proof.paths.iter().fold(0usize, |total, path| {
            path.iter().fold(total, |total, row| {
                total.saturating_add(1usize.saturating_add(row.terms.len()))
            })
        });
        self.charge_value_work(snapshot_work)?;
        let paths = self.proof.paths.clone();
        let result = (|| {
            for (name, premise) in hypotheses {
                let node =
                    self.proof
                        .evidence
                        .insert((*premise).clone(), parents.to_vec(), false)?;
                self.proof.witnesses.insert((*name).into(), node);
                self.assume_from(premise, paths::Origin::Evidence(node))?;
            }
            check(self)
        })();
        for (name, _) in hypotheses {
            self.proof.witnesses.remove(*name);
        }
        self.proof.paths = paths;
        result
    }

    fn proof_goal(
        &mut self,
        goal: &Formula,
        label: &str,
        line: usize,
        steps: &[String],
        next: &mut usize,
        depth: usize,
    ) -> Result<evidence::NodeId> {
        if depth >= 64 {
            return Err(format!(
                "line {line}: proof goal nesting limit reached (64)"
            ));
        }
        self.charge_value_work(1)?;
        let step = steps
            .get(*next)
            .ok_or_else(|| format!("line {line}: proof has an unfinished goal"))?;
        *next += 1;
        match step.as_str() {
            "omega" | "rfl" | "simp_all" | "decide" => {
                let parents = self.arithmetic_support(goal, label, line)?;
                self.proof.evidence.arithmetic(goal.clone(), parents)
            }
            "assumption" => {
                let names = self.proof.witnesses.keys().cloned().collect::<Vec<_>>();
                self.charge_value_work(names.len())?;
                for name in names {
                    let node = self.proof.witnesses[&name];
                    let candidate = self.proof.evidence.claim(node).clone();
                    if self.same_proposition(&candidate, goal)? {
                        self.work.obligations += 1;
                        return self.proof.evidence.insert(goal.clone(), vec![node], false);
                    }
                }
                Err(format!(
                    "line {line}: assumption found no checked proof of this proposition"
                ))
            }
            "constructor" => {
                let Formula::And(a, b) = goal else {
                    return Err(format!(
                        "line {line}: constructor requires a conjunction goal"
                    ));
                };
                let a = self.proof_goal(a, label, line, steps, next, depth + 1)?;
                let b = self.proof_goal(b, label, line, steps, next, depth + 1)?;
                self.proof.evidence.insert(goal.clone(), vec![a, b], false)
            }
            "left" | "right" => {
                let Formula::Or(a, b) = goal else {
                    return Err(format!("line {line}: {step} requires a disjunction goal"));
                };
                let premise = self.proof_goal(
                    if step == "left" { a } else { b },
                    label,
                    line,
                    steps,
                    next,
                    depth + 1,
                )?;
                self.proof
                    .evidence
                    .insert(goal.clone(), vec![premise], false)
            }
            _ if step.starts_with("exact ") => {
                let name = &step[6..];
                let proven = self.proof.witnesses.get(name).cloned().ok_or_else(|| format!("line {line}: {name} is not a checked proof; fact declarations are propositions, not assumptions"))?;
                let claim = self.proof.evidence.claim(proven).clone();
                if !self.same_proposition(&claim, goal)? {
                    return Err(format!("line {line}: exact {name} proves a different proposition or an earlier state"));
                }
                self.work.obligations += 1;
                self.proof
                    .evidence
                    .insert(goal.clone(), vec![proven], false)
            }
            _ if step.starts_with("intro ") => {
                let (premise, consequence) = match goal {
                    Formula::Implies(a, b) => (&**a, &**b),
                    Formula::Not(a) => (&**a, &Formula::False),
                    _ => {
                        return Err(format!(
                            "line {line}: intro requires an implication or negation goal"
                        ))
                    }
                };
                let name = &step[6..];
                let consequence =
                    self.with_proof_hypotheses(&[(name, premise)], &[], line, |ctx| {
                        ctx.proof_goal(consequence, label, line, steps, next, depth + 1)
                    })?;
                self.proof
                    .evidence
                    .insert(goal.clone(), vec![consequence], false)
            }
            _ if step.starts_with("cases ") => {
                let parts = step.split_whitespace().collect::<Vec<_>>();
                if let ["cases", name] = parts.as_slice() {
                    let node = self.proof.witnesses.get(*name).copied();
                    if !node
                        .is_some_and(|id| matches!(self.proof.evidence.claim(id), Formula::False))
                    {
                        return Err(format!("line {line}: cases {name} without a pattern requires a checked proof of false"));
                    }
                    self.work.obligations += 1;
                    return self
                        .proof
                        .evidence
                        .insert(goal.clone(), vec![node.unwrap()], false);
                }
                let ["cases", name, "with", first, separator, second] = parts.as_slice() else {
                    return Err(format!("line {line}: malformed cases step"));
                };
                let theorem =
                    self.proof.witnesses.get(*name).cloned().ok_or_else(|| {
                        format!("line {line}: cases {name} requires a checked proof")
                    })?;
                let claim = self.proof.evidence.claim(theorem).clone();
                match (claim, *separator) {
                    (Formula::And(a, b), ",") => {
                        let branch = self.with_proof_hypotheses(&[(first, &a), (second, &b)], &[theorem], line, |ctx| {
                            ctx.proof_goal(goal, label, line, steps, next, depth + 1)
                        })?;
                        self.proof.evidence.insert(goal.clone(), vec![theorem, branch], false)
                    }
                    (Formula::Or(a, b), "|") => {
                        // Validate both names before starting either branch.
                        self.fresh_binding(first, line)?;
                        self.fresh_binding(second, line)?;
                        let left = self.with_proof_hypotheses(&[(first, &a)], &[theorem], line, |ctx| {
                            ctx.proof_goal(goal, label, line, steps, next, depth + 1)
                        })?;
                        let right = self.with_proof_hypotheses(&[(second, &b)], &[theorem], line, |ctx| {
                            ctx.proof_goal(goal, label, line, steps, next, depth + 1)
                        })?;
                        self.proof.evidence.insert(goal.clone(), vec![theorem, left, right], false)
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
                let mut theorem = self.proof.evidence.claim(source).clone();
                let mut premises = Vec::new();
                while !self.same_proposition(&theorem, goal)? {
                    match theorem {
                        Formula::Implies(premise, consequence) => {
                            premises.push(*premise);
                            theorem = *consequence;
                        }
                        Formula::Not(premise) => {
                            premises.push(*premise);
                            theorem = Formula::False;
                        }
                        _ => {
                            return Err(format!(
                                "line {line}: apply {name} does not conclude this goal"
                            ))
                        }
                    }
                }
                let mut parents = vec![source];
                for premise in premises {
                    parents.push(self.proof_goal(&premise, label, line, steps, next, depth + 1)?);
                }
                self.work.obligations += 1;
                self.proof.evidence.insert(goal.clone(), parents, false)
            }
            _ => Err(format!("line {line}: unsupported proof step {step}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_context<T>(session: &mut Session, check: impl FnOnce(&mut Context<'_>) -> T) -> T {
        let functions = BTreeMap::new();
        let structs = BTreeMap::new();
        let names = BTreeSet::new();
        let declarations = Declarations {
            functions: &functions,
            structs: &structs,
            drops: &names,
            destructors: &functions,
            helpers: &names,
            cleanup_helpers: &names,
        };
        check(&mut Context::new(declarations, session))
    }

    fn script(ctx: &mut Context<'_>, goal: &Formula, steps: &[&str]) -> evidence::NodeId {
        let steps = steps
            .iter()
            .map(|step| (*step).to_owned())
            .collect::<Vec<_>>();
        ctx.proof_script(goal, "evidence test", 1, &steps).unwrap()
    }

    #[test]
    fn tactics_track_only_the_admissions_they_use_and_replay_the_same_graph() {
        fn check(session: &mut Session) -> evidence::AdmissionDependencies {
            with_context(session, |ctx| {
                let unused = script(ctx, &Formula::False, &["trustme"]);
                ctx.proof.witnesses.insert("unused".into(), unused);
                let premise = Formula::Ge(Linear::variable("premise"));
                let conclusion = Formula::Ge(Linear::variable("conclusion"));
                let implication =
                    Formula::Implies(Box::new(premise.clone()), Box::new(conclusion.clone()));
                let theorem = script(ctx, &implication, &["trustme"]);
                ctx.proof.witnesses.insert("theorem".into(), theorem);
                let premise_node = script(ctx, &premise, &["trustme"]);
                ctx.proof.witnesses.insert("premise".into(), premise_node);
                let root = script(ctx, &conclusion, &["apply theorem", "exact premise"]);
                let dependencies = ctx.proof.evidence.admissions(root);
                assert!(dependencies.complete);
                assert_eq!(
                    dependencies.admissions,
                    BTreeSet::from([theorem, premise_node])
                );
                assert!(!dependencies.admissions.contains(&unused));
                dependencies
            })
        }
        let mut recording = Session::recording();
        let expected = check(&mut recording);
        recording.finish().unwrap();
        let bundle = recording.bundle("proof graph replay").unwrap();
        let mut replay = Session::replay(&bundle);
        assert_eq!(check(&mut replay), expected);
        replay.finish().unwrap();
        assert_eq!(replay.search_count(), 0);
    }

    #[test]
    fn arithmetic_edges_use_checked_row_support_on_search_and_replay() {
        fn check(session: &mut Session) -> evidence::AdmissionDependencies {
            with_context(session, |ctx| {
                let x = Linear::variable("x");
                let used_claim = Formula::Ge(x.clone());
                let unused_claim = Formula::Ge(Linear::variable("unrelated"));
                let used = script(ctx, &used_claim, &["trustme"]);
                let unused = script(ctx, &unused_claim, &["trustme"]);
                ctx.assume_from(&used_claim, paths::Origin::Evidence(used))
                    .unwrap();
                ctx.assume_from(&unused_claim, paths::Origin::Evidence(unused))
                    .unwrap();
                let goal = Formula::Ge(x.add(&Linear::number(1)).unwrap());
                let root = script(ctx, &goal, &["omega"]);
                let dependencies = ctx.proof.evidence.admissions(root);
                assert_eq!(dependencies.admissions, BTreeSet::from([used]));
                // Pruned alternatives and other path context still need
                // dependency explanations before completeness is justified.
                assert!(!dependencies.complete);
                dependencies
            })
        }
        let mut recording = Session::recording();
        let expected = check(&mut recording);
        recording.finish().unwrap();
        let bundle = recording.bundle("arithmetic proof graph replay").unwrap();
        let mut replay = Session::replay(&bundle);
        assert_eq!(check(&mut replay), expected);
        replay.finish().unwrap();
        assert_eq!(replay.search_count(), 0);
    }

    #[test]
    fn cases_keeps_source_dependency_after_local_hypotheses_leave_scope() {
        with_context(&mut Session::search(), |ctx| {
            let proposition = Formula::Ge(Linear::variable("p"));
            let conjunction = Formula::And(Box::new(proposition.clone()), Box::new(Formula::True));
            let source = script(ctx, &conjunction, &["trustme"]);
            ctx.proof.witnesses.insert("source".into(), source);
            let result = script(ctx, &proposition, &["cases source with p , q", "exact p"]);
            assert!(!ctx.proof.witnesses.contains_key("p"));
            assert!(!ctx.proof.witnesses.contains_key("q"));
            assert_eq!(
                ctx.proof.evidence.admissions(result).admissions,
                BTreeSet::from([source])
            );
        });
    }

    #[test]
    fn introduction_preserves_claim_and_does_not_admit_its_hypothesis() {
        with_context(&mut Session::search(), |ctx| {
            let premise = Formula::Ge(Linear::variable("p"));
            let goal = Formula::Implies(Box::new(premise.clone()), Box::new(premise));
            let root = script(ctx, &goal, &["intro h", "exact h"]);
            assert_eq!(ctx.proof.evidence.claim(root), &goal);
            let dependencies = ctx.proof.evidence.admissions(root);
            assert!(dependencies.complete);
            assert!(dependencies.admissions.is_empty());
            assert!(!ctx.proof.witnesses.contains_key("h"));
        });
    }
}
