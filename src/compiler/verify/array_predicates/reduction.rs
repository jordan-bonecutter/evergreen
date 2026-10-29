//! Construct proofs of selector definitions from arithmetic guards and scoped
//! logical premises. Every connective and specialization uses kernel rules.

use super::*;

mod cases;
mod negative;

impl Context<'_> {
    pub(in crate::compiler::verify) fn reduce_selector_formula(
        &mut self,
        goal: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        self.charge_value_work(goal.storage_weight()?)?;
        if depth >= 64 {
            return Err("selector proof reduction depth limit reached".into());
        }
        if goal.is_arithmetic() {
            let support = match self.scoped_arithmetic_support(goal)? {
                Some(support) => Some(support),
                None => self.probe_guard(&self.proof.paths.clone(), goal)?,
            };
            return match support {
                Some(support) => {
                    self.work.obligations += 1;
                    self.proof
                        .evidence
                        .arithmetic(goal.clone(), support)
                        .map(Some)
                }
                None => Ok(None),
            };
        }
        if let Some(node) = self.logical_assumption(goal, None)? {
            return Ok(Some(node));
        }
        if let Some(node) = self.prove_indexed_value_equality(goal)? {
            return Ok(Some(node));
        }
        match goal {
            Formula::Forall {
                variable,
                domain,
                body,
            } => {
                let eigenvariable = self.fresh_name();
                let term = Linear::variable(&eigenvariable);
                let domain = domain.substitute(variable, &term)?;
                let body = body.substitute(variable, &term)?;
                let (hypothesis, premise) = self.proof.evidence.hypothesis(domain)?;
                let name = self.fresh_name();
                let result =
                    self.with_logical_binding(&eigenvariable, &eigenvariable, false, |ctx| {
                        ctx.with_proof_hypotheses(&[(&name, premise)], 0, |ctx| {
                            ctx.reduce_selector_formula(&body, depth + 1)
                        })
                    })?;
                let Some(body) = result else {
                    return Ok(None);
                };
                self.proof
                    .evidence
                    .derive(
                        goal.clone(),
                        evidence::Rule::ForallIntro {
                            hypothesis,
                            body,
                            eigenvariable,
                        },
                    )
                    .map(Some)
            }
            Formula::And(a, b) => {
                let Some(left) = self.reduce_selector_formula(a, depth + 1)? else {
                    return Ok(None);
                };
                let Some(right) = self.reduce_selector_formula(b, depth + 1)? else {
                    return Ok(None);
                };
                self.proof
                    .evidence
                    .derive(goal.clone(), evidence::Rule::AndIntro(left, right))
                    .map(Some)
            }
            Formula::Or(a, b) => {
                let rule = if let Some(left) = self.reduce_selector_formula(a, depth + 1)? {
                    evidence::Rule::OrLeft(left)
                } else if let Some(right) = self.reduce_selector_formula(b, depth + 1)? {
                    evidence::Rule::OrRight(right)
                } else {
                    return self.reduce_selector_choice(goal, a, b, depth + 1);
                };
                self.proof.evidence.derive(goal.clone(), rule).map(Some)
            }
            Formula::Not(body) => {
                if let Some(node) = self.scoped_selector_instance(goal, depth + 1)? {
                    return Ok(Some(node));
                }
                self.reduce_negative_selector(goal, body, depth + 1)
            }
            Formula::Predicate { symbol, .. } => {
                if let Some(node) = self.scoped_selector_instance(goal, depth + 1)? {
                    return Ok(Some(node));
                }
                let Some(&definition) = self.arrays.predicate_definitions.get(symbol) else {
                    return Ok(None);
                };
                let body = self.proof.evidence.predicate_definition(
                    definition,
                    goal,
                    &mut self.work.value_work,
                    MAX_VALUE_WORK,
                )?;
                let Some(premise) = self.reduce_selector_formula(&body, depth + 1)? else {
                    return Ok(None);
                };
                let implication = Formula::Implies(Box::new(body), Box::new(goal.clone()));
                let theorem = self.proof.evidence.derive(
                    implication,
                    evidence::Rule::UnfoldPredicate {
                        definition,
                        reverse: true,
                    },
                )?;
                self.proof
                    .evidence
                    .derive(
                        goal.clone(),
                        evidence::Rule::ImpElim {
                            theorem,
                            argument: premise,
                        },
                    )
                    .map(Some)
            }
            _ => Ok(None),
        }
    }

    pub(in crate::compiler::verify) fn selector_contradiction(
        &mut self,
        first: evidence::NodeId,
        second: evidence::NodeId,
    ) -> Result<evidence::NodeId> {
        let a = self.proof.evidence.claim(first)?;
        let b = self.proof.evidence.claim(second)?;
        let same = |a: &Formula, b: &Formula| a.normalized().alpha_equal(&b.normalized());
        let rule = match (a, b) {
            (Formula::False, _) => evidence::Rule::Reuse(first),
            (_, Formula::False) => evidence::Rule::Reuse(second),
            (Formula::Not(inner), b) if same(inner, b) => evidence::Rule::ImpElim {
                theorem: first,
                argument: second,
            },
            (a, Formula::Not(inner)) if same(a, inner) => evidence::Rule::ImpElim {
                theorem: second,
                argument: first,
            },
            _ => {
                return Err(
                    "selector negation did not yield complementary checked propositions".into(),
                )
            }
        };
        self.proof.evidence.derive(Formula::False, rule)
    }

    pub(super) fn scoped_selector_instance(
        &mut self,
        goal: &Formula,
        depth: usize,
    ) -> Result<Option<evidence::NodeId>> {
        // Specialization matches one selector atom, optionally negated. A
        // compound goal cannot match any candidate: reduce its connectives
        // first instead of walking every in-scope range for each connective.
        if !matches!(goal, Formula::Predicate { .. })
            && !matches!(goal, Formula::Not(inner) if matches!(inner.as_ref(), Formula::Predicate { .. }))
        {
            return Ok(None);
        }
        let candidates = self
            .proof
            .witnesses
            .values()
            .copied()
            .chain(self.proof.claims.iter().copied())
            .collect::<BTreeSet<_>>();
        let (open, closed): (Vec<_>, Vec<_>) = candidates
            .into_iter()
            .partition(|&node| self.proof.evidence.check_closed(node).is_err());
        let nodes = open.into_iter().chain(closed).collect::<Vec<_>>();
        self.charge_value_work(nodes.len())?;
        for theorem in nodes {
            if observations::atom(goal).is_some_and(|(symbol, _, _)| {
                !self
                    .proof
                    .evidence
                    .claim_mentions_predicate(theorem, symbol)
            }) {
                continue;
            }
            // A live, checked contract can be restricted to a smaller domain.
            // Historical or admitted ranges still need explicit transport.
            if self.proof.evidence.check_closed(theorem).is_ok()
                && !self.unadmitted_evidence(theorem)?
            {
                continue;
            }
            self.charge_value_work(self.proof.evidence.claim(theorem)?.storage_weight()?)?;
            let Formula::Forall {
                variable,
                domain,
                body,
            } = self.proof.evidence.claim(theorem)?.clone()
            else {
                continue;
            };
            let mut pending = vec![(&*body, Vec::new())];
            while let Some((part, path)) = pending.pop() {
                self.charge_value_work(1 + path.len())?;
                if let Formula::And(a, b) = part {
                    let mut left = path.clone();
                    left.push(false);
                    let mut right = path;
                    right.push(true);
                    pending.extend([(&**a, left), (&**b, right)]);
                    continue;
                }
                let exact = observations::specialization_term(part, goal, &variable)?;
                let mut congruence = Vec::new();
                let term = if let Some(term) = exact {
                    term
                } else {
                    // One bound index may occur in several predicate arguments.
                    // A guarded store can make those arguments equal without
                    // making their syntax identical. Check each equality before
                    // transporting the specialized predicate through congruence.
                    let (
                        Formula::Predicate {
                            symbol: a,
                            arguments: aa,
                        },
                        Formula::Predicate {
                            symbol: b,
                            arguments: ba,
                        },
                    ) = (part, goal)
                    else {
                        continue;
                    };
                    if a != b || aa.len() != ba.len() {
                        continue;
                    }
                    let mut candidate = None;
                    for (pattern, wanted) in aa.iter().zip(ba) {
                        if pattern.terms.contains_key(&variable) {
                            candidate =
                                observations::specialization_index(pattern, wanted, &variable)?;
                            if candidate.is_some() {
                                break;
                            }
                        }
                    }
                    let Some(term) = candidate else { continue };
                    let Formula::Predicate { arguments, .. } = part.substitute(&variable, &term)?
                    else {
                        unreachable!()
                    };
                    for (actual, wanted) in arguments.iter().zip(ba) {
                        let Some(proof) =
                            self.reduce_selector_formula(&equal(actual, wanted)?, depth + 1)?
                        else {
                            break;
                        };
                        congruence.push(proof);
                    }
                    if congruence.len() != ba.len() {
                        continue;
                    }
                    term
                };
                let mut source = theorem;
                if self.proof.evidence.check_closed(theorem).is_ok() {
                    let Some(snapshot) = self.proof.evidence.subjects(theorem).cloned() else {
                        continue;
                    };
                    let scope = self.logical_claim_scope(theorem, &snapshot)?;
                    let Some(scoped) = self.guarded_claim_evidence(theorem, &scope)? else {
                        continue;
                    };
                    source = scoped;
                }
                let domain = domain.substitute(&variable, &term)?;
                let Some(domain) = self.reduce_selector_formula(&domain, depth + 1)? else {
                    continue;
                };
                let mut instance = self.proof.evidence.derive(
                    body.substitute(&variable, &term)?,
                    evidence::Rule::ForallElim {
                        theorem: source,
                        domain,
                        term,
                    },
                )?;
                for right in path {
                    let Formula::And(a, b) = self.proof.evidence.claim(instance)?.clone() else {
                        return Err("universal projection lost its conjunction".into());
                    };
                    instance = self.proof.evidence.derive(
                        if right { *b } else { *a },
                        if right {
                            evidence::Rule::AndRight(instance)
                        } else {
                            evidence::Rule::AndLeft(instance)
                        },
                    )?;
                }
                if !congruence.is_empty() {
                    instance = self.proof.evidence.derive(
                        goal.clone(),
                        evidence::Rule::PredicateCongruence {
                            source: instance,
                            equalities: congruence,
                        },
                    )?;
                }
                return Ok(Some(instance));
            }
        }
        Ok(None)
    }
}
