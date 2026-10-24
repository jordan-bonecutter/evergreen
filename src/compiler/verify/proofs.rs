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
    ) -> Result<()> {
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
            self.session.trust(&self.paths, &proposition, line, label)?;
            self.obligations += 1;
            return Ok(());
        }
        let mut next = 0;
        self.proof_goal(goal, label, line, steps, &mut next, 0)?;
        if next != steps.len() {
            return Err(format!(
                "line {line}: unused proof steps after the goal was closed"
            ));
        }
        Ok(())
    }

    fn same_proposition(&mut self, a: &Formula, b: &Formula) -> Result<bool> {
        self.charge_value_work(symbol_weight(&Symbol::Bool(a.clone()))?)?;
        self.charge_value_work(symbol_weight(&Symbol::Bool(b.clone()))?)?;
        Ok(a.normalized() == b.normalized())
    }

    fn with_proof_hypotheses(
        &mut self,
        hypotheses: &[(&str, &Formula)],
        line: usize,
        check: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        let mut names = BTreeSet::new();
        for (name, premise) in hypotheses {
            self.fresh_binding(name, line)?;
            if !names.insert(*name) {
                return Err(format!("line {line}: duplicate proof hypothesis {name}"));
            }
            self.charge_value_work(symbol_weight(&Symbol::Bool((*premise).clone()))?)?;
        }
        let snapshot_work = self.paths.iter().fold(0usize, |total, path| {
            path.iter().fold(total, |total, row| {
                total.saturating_add(1usize.saturating_add(row.terms.len()))
            })
        });
        self.charge_value_work(snapshot_work)?;
        let paths = self.paths.clone();
        let result = (|| {
            for (name, premise) in hypotheses {
                self.proofs.insert((*name).into(), (*premise).clone());
                self.assume(premise)?;
            }
            check(self)
        })();
        for (name, _) in hypotheses {
            self.proofs.remove(*name);
        }
        self.paths = paths;
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
    ) -> Result<()> {
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
            "omega" | "rfl" | "simp_all" | "decide" => self.prove(goal, label, line),
            "assumption" => {
                let names = self.proofs.keys().cloned().collect::<Vec<_>>();
                self.charge_value_work(names.len())?;
                for name in names {
                    let candidate = self.proofs[&name].clone();
                    if self.same_proposition(&candidate, goal)? {
                        self.obligations += 1;
                        return Ok(());
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
                self.proof_goal(a, label, line, steps, next, depth + 1)?;
                self.proof_goal(b, label, line, steps, next, depth + 1)
            }
            "left" | "right" => {
                let Formula::Or(a, b) = goal else {
                    return Err(format!("line {line}: {step} requires a disjunction goal"));
                };
                self.proof_goal(
                    if step == "left" { a } else { b },
                    label,
                    line,
                    steps,
                    next,
                    depth + 1,
                )
            }
            _ if step.starts_with("exact ") => {
                let name = &step[6..];
                let proven = self.proofs.get(name).cloned().ok_or_else(|| format!("line {line}: {name} is not a checked proof; fact declarations are propositions, not assumptions"))?;
                if !self.same_proposition(&proven, goal)? {
                    return Err(format!("line {line}: exact {name} proves a different proposition or an earlier state"));
                }
                self.obligations += 1;
                Ok(())
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
                self.with_proof_hypotheses(&[(name, premise)], line, |ctx| {
                    ctx.proof_goal(consequence, label, line, steps, next, depth + 1)
                })
            }
            _ if step.starts_with("cases ") => {
                let parts = step.split_whitespace().collect::<Vec<_>>();
                if let ["cases", name] = parts.as_slice() {
                    if !matches!(self.proofs.get(*name), Some(Formula::False)) {
                        return Err(format!("line {line}: cases {name} without a pattern requires a checked proof of false"));
                    }
                    self.obligations += 1;
                    return Ok(());
                }
                let ["cases", name, "with", first, separator, second] = parts.as_slice() else {
                    return Err(format!("line {line}: malformed cases step"));
                };
                let theorem =
                    self.proofs.get(*name).cloned().ok_or_else(|| {
                        format!("line {line}: cases {name} requires a checked proof")
                    })?;
                match (theorem, *separator) {
                    (Formula::And(a, b), ",") => {
                        self.with_proof_hypotheses(&[(first, &a), (second, &b)], line, |ctx| {
                            ctx.proof_goal(goal, label, line, steps, next, depth + 1)
                        })
                    }
                    (Formula::Or(a, b), "|") => {
                        // Validate both names before starting either branch.
                        self.fresh_binding(first, line)?;
                        self.fresh_binding(second, line)?;
                        self.with_proof_hypotheses(&[(first, &a)], line, |ctx| {
                            ctx.proof_goal(goal, label, line, steps, next, depth + 1)
                        })?;
                        self.with_proof_hypotheses(&[(second, &b)], line, |ctx| {
                            ctx.proof_goal(goal, label, line, steps, next, depth + 1)
                        })
                    }
                    _ => Err(format!("line {line}: cases requires a conjunction with ',' or a disjunction with '|'")),
                }
            }
            _ if step.starts_with("apply ") => {
                let name = &step[6..];
                let mut theorem =
                    self.proofs.get(name).cloned().ok_or_else(|| {
                        format!("line {line}: apply {name} requires a checked proof")
                    })?;
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
                for premise in premises {
                    self.proof_goal(&premise, label, line, steps, next, depth + 1)?;
                }
                self.obligations += 1;
                Ok(())
            }
            _ => Err(format!("line {line}: unsupported proof step {step}")),
        }
    }
}
