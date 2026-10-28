//! Read-only selector definitions over immutable sparse array versions. Their
//! mathematical bodies contain type tags, not payloads or ownership claims.

use super::*;

mod definitions;
mod observations;
pub(super) use observations::specialization_index;
mod reduction;

#[cfg(test)]
mod input_tests;
#[cfg(test)]
mod observation_tests;
#[cfg(test)]
mod store_tests;
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

pub(super) fn combine(mut parts: Vec<Formula>, conjunction: bool) -> Formula {
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
        let Symbol::Array { len, identity, .. } = &array else {
            return Err("indexed type predicates require array storage".into());
        };
        let bounds =
            Formula::Ge(index.clone()).and(Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?));
        self.defer_quantified_check(
            bounds,
            "quantified array index bounds".into(),
            expression.line,
        )?;
        self.ensure_type_selector(&array, &target, 0)?;
        let key = (identity.clone(), target.clone());
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
            Formula::And(..) | Formula::Or(..) | Formula::Not(..) => {
                return self.reduce_selector_formula(goal, 0);
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
        let proven = if wanted.is_arithmetic() {
            if let Some(node) = self.reduce_selector_formula(&wanted, 0)? {
                node
            } else {
                let support = self.arithmetic_support_for(&wanted, subjects, label, line)?;
                self.proof.evidence.arithmetic(wanted, support)?
            }
        } else {
            let Some(node) = self.reduce_selector_formula(&wanted, 0)? else {
                return Err(format!("line {line}: cannot prove {label}: selector reduction needs a checked premise for its earlier contents version"));
            };
            node
        };
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
        let contradiction = self.selector_contradiction(proven, body)?;
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
}
