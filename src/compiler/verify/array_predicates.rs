//! Read-only selector definitions over immutable sparse array versions. Their
//! mathematical bodies contain type tags, not payloads or ownership claims.

use super::*;

mod observations;

#[cfg(test)]
mod input_tests;
#[cfg(test)]
mod observation_tests;
#[cfg(test)]
mod tests;

pub(super) struct Selector {
    symbol: String,
    captures: Vec<String>,
}

pub(super) fn indexed_type_parts(expression: &Expr) -> Option<(&Expr, &Expr, &Expr, bool)> {
    let Kind::Binary(op, a, b) = &expression.kind else {
        return None;
    };
    if !matches!(op.as_str(), "==" | "!=") {
        return None;
    }
    for (observation, target) in [(a, b), (b, a)] {
        if let Kind::Call(name, arguments) = &observation.kind {
            if name == "typeof" && arguments.len() == 1 {
                if let Kind::Index(base, index) = &arguments[0].kind {
                    return Some((base, index, target, op == "!="));
                }
            }
        }
    }
    None
}

pub(super) fn literal_target(ctx: &Context<'_>, expression: &Expr) -> Option<Ty> {
    match &expression.kind {
        Kind::Name(name) if ctx.locals.values.contains_key(name) => None,
        Kind::Call(name, args) if args.len() == 1 => {
            let inner = literal_target(ctx, &args[0])?;
            match name.as_str() {
                "shape" if !matches!(inner, Ty::Shape(_)) => Some(Ty::Shape(Box::new(inner))),
                "unique" => Some(Ty::Unique(Box::new(inner))),
                "shared" => Some(Ty::Shared(Box::new(inner))),
                _ => None,
            }
        }
        Kind::Unary(op, inner) if op == "&" => {
            literal_target(ctx, inner).map(|ty| Ty::Ref(Box::new(ty)))
        }
        _ => ctx.type_literal(expression),
    }
}

fn member(value: &Symbol, target: &Ty) -> Result<Formula> {
    if let Symbol::Union {
        members, active, ..
    } = value
    {
        let mut cases = Vec::new();
        for (tag, ty) in members.iter().enumerate() {
            cases.push(
                unions::type_equal(ty, target)?.and(equal(active, &Linear::number(tag as i128))?),
            );
        }
        Ok(combine(cases, false))
    } else {
        unions::type_equal(&value.ty(), target)
    }
}

fn combine(mut parts: Vec<Formula>, conjunction: bool) -> Formula {
    if parts.is_empty() {
        return if conjunction {
            Formula::True
        } else {
            Formula::False
        };
    }
    while parts.len() > 1 {
        let mut next = Vec::with_capacity(parts.len().div_ceil(2));
        let mut parts_iter = parts.into_iter();
        while let Some(a) = parts_iter.next() {
            next.push(match parts_iter.next() {
                Some(b) if conjunction => a.and(b),
                Some(b) => a.or(b),
                None => a,
            });
        }
        parts = next;
    }
    parts.pop().unwrap()
}

impl Context<'_> {
    pub(super) fn eval_indexed_type_predicate(&mut self, expression: &Expr) -> Result<Symbol> {
        let (base, index, target, negated) =
            indexed_type_parts(expression).ok_or("expected an indexed type comparison")?;
        let target = literal_target(self, target)
            .ok_or("indexed type comparisons need a literal member type")?;
        let index = self.eval(index, Some(&Ty::Int))?.number()?;
        let array = self.storage(base)?;
        self.charge_value_work(symbol_weight(&array)?)?;
        let Symbol::Array {
            element,
            len,
            items,
            cells,
            identity,
        } = &array
        else {
            return Err("indexed type predicates require array storage".into());
        };
        let bounds =
            Formula::Ge(index.clone()).and(Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?));
        self.locals
            .quantified_checks
            .last_mut()
            .ok_or("indexed type predicates require an arithmetic quantifier domain")?
            .push(bounds);
        let key = (identity.clone(), target.clone());
        if !self.arrays.type_predicates.contains_key(&key)
            && self.arrays.inputs.contains(identity)
            && matches!(element.as_ref(), Ty::Union(_))
            && items.is_none()
        {
            // An input array has no uniform default. Give its immutable
            // version an uninterpreted selector, never an invented type fact.
            // Sparse observations cannot define its unobserved remainder.
            let symbol = self.fresh_name();
            self.proof
                .evidence
                .declare_predicate(symbol.clone(), vec!["index".into()])?;
            self.arrays.type_predicates.insert(
                key.clone(),
                Selector {
                    symbol,
                    captures: Vec::new(),
                },
            );
        }
        if !self.arrays.type_predicates.contains_key(&key) {
            let initial = match self.arrays.history.get(identity) {
                Some(ArrayHistory::Uninitialized(value) | ArrayHistory::Fill(value)) => {
                    Some(member(value, &target)?)
                }
                _ if !matches!(element.as_ref(), Ty::Union(_)) => {
                    Some(unions::type_equal(element, &target)?)
                }
                _ => None,
            };
            let variable = "evg_selector_index";
            let input = Linear::variable(variable);
            let mut exclusions = Vec::new();
            let mut alternatives = Vec::new();
            let mut visit = |at: &Linear, value: &Symbol| -> Result<()> {
                let matches = member(value, &target)?;
                // Read observations matching the uniform default add no exception.
                if initial.as_ref() == Some(&matches) {
                    return Ok(());
                }
                let same = equal(&input, at)?;
                exclusions.push(same.clone().not());
                alternatives.push(same.and(matches));
                Ok(())
            };
            if let Some(items) = items {
                // Literal elements are already explicit data; no capacity is enumerated.
                for (i, value) in items.iter().enumerate() {
                    visit(&Linear::number(i as i128), value)?;
                }
            }
            for (at, value) in cells {
                visit(at, value)?;
            }
            let default = match initial {
                Some(initial) => initial,
                None if items.is_some() => Formula::False,
                None => return Err("indexed union predicates need a known default or explicit literal elements; input and store summaries remain unfinished".into()),
            };
            alternatives.push(default.and(combine(exclusions, true)));
            let body = Formula::Ge(input.clone())
                .and(Formula::Ge(len.sub(&input)?.add(&Linear::number(-1))?))
                .and(combine(alternatives, false));
            self.charge_value_work(body.storage_weight()?)?;
            let captures = body
                .free_variables()?
                .into_iter()
                .filter(|name| name != variable)
                .collect::<Vec<_>>();
            let parameters = std::iter::once(variable.to_owned())
                .chain(captures.iter().cloned())
                .collect();
            let symbol = self.fresh_name();
            let definition =
                self.proof
                    .evidence
                    .define_predicate(symbol.clone(), parameters, body)?;
            self.arrays
                .predicate_definitions
                .insert(symbol.clone(), definition);
            self.arrays
                .type_predicates
                .insert(key.clone(), Selector { symbol, captures });
        }
        let selector = &self.arrays.type_predicates[&key];
        let arguments = std::iter::once(index)
            .chain(selector.captures.iter().map(Linear::variable))
            .collect();
        let predicate = Formula::Predicate {
            symbol: selector.symbol.clone(),
            arguments,
        };
        Ok(Symbol::Bool(if negated {
            predicate.not()
        } else {
            predicate
        }))
    }

    pub(super) fn prove_indexed_predicate(
        &mut self,
        goal: &Formula,
        subjects: Option<&subjects::Snapshot>,
        label: &str,
        line: usize,
    ) -> Result<Option<evidence::NodeId>> {
        let (atom, negated) = match goal {
            Formula::Predicate { .. } => (goal, false),
            Formula::Not(atom) if matches!(atom.as_ref(), Formula::Predicate { .. }) => {
                (atom.as_ref(), true)
            }
            _ => return Ok(None),
        };
        let Formula::Predicate { symbol, .. } = atom else {
            return Ok(None);
        };
        let Some(&definition) = self.arrays.predicate_definitions.get(symbol) else {
            return Ok(None);
        };
        let body = self.proof.evidence.predicate_definition(
            definition,
            atom,
            &mut self.work.value_work,
            MAX_VALUE_WORK,
        )?;
        let wanted = if negated {
            body.clone().not()
        } else {
            body.clone()
        };
        let support = self.arithmetic_support_for(&wanted, subjects, label, line)?;
        let proven = self.proof.evidence.arithmetic(wanted, support)?;
        let implication = if negated {
            Formula::Implies(Box::new(atom.clone()), Box::new(body.clone()))
        } else {
            Formula::Implies(Box::new(body.clone()), Box::new(atom.clone()))
        };
        let reduction = self.proof.evidence.derive(
            implication,
            evidence::Rule::UnfoldPredicate {
                definition,
                reverse: !negated,
            },
        )?;
        if !negated {
            return self
                .proof
                .evidence
                .derive(
                    goal.clone(),
                    evidence::Rule::ImpElim {
                        theorem: reduction,
                        argument: proven,
                    },
                )
                .map(Some);
        }
        let (hypothesis, premise) = self.proof.evidence.hypothesis(atom.clone())?;
        let body = self.proof.evidence.derive(
            body,
            evidence::Rule::ImpElim {
                theorem: reduction,
                argument: premise,
            },
        )?;
        let contradiction = self.proof.evidence.derive(
            Formula::False,
            evidence::Rule::ImpElim {
                theorem: proven,
                argument: body,
            },
        )?;
        self.proof
            .evidence
            .derive(
                goal.clone(),
                evidence::Rule::ImpIntro {
                    hypothesis,
                    body: contradiction,
                },
            )
            .map(Some)
    }

    pub(super) fn finish_quantified_checks(
        &mut self,
        variable: &str,
        domain: &Formula,
        checks: Vec<Formula>,
        line: usize,
    ) -> Result<()> {
        for check in checks {
            let goal = Formula::Forall {
                variable: variable.into(),
                domain: Box::new(domain.clone()),
                body: Box::new(check),
            };
            self.charge_value_work(goal.storage_weight()?)?;
            if let Some(parent) = self.locals.quantified_checks.last_mut() {
                parent.push(goal);
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
                steps.push(format!("intro evg_index_check_{}", steps.len()));
                tail = body;
            }
            steps.push("omega".into());
            // Bounds often follow from the quantified domains alone. Prove
            // those in an independent context so unrelated storage case splits
            // cannot introduce imported dependencies into ForallIntro.
            let independent = self.probe_guard(&domains, tail)?.is_some();
            let saved =
                independent.then(|| std::mem::replace(&mut self.proof.paths, paths::Paths::unit()));
            let result =
                self.proof_script_for(&goal, "quantified array index bounds", line, &steps, None);
            if let Some(saved) = saved {
                self.proof.paths = saved;
            }
            let node = result?;
            self.proof.uses.push(node);
        }
        Ok(())
    }
}
