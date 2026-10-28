//! Scalar payload equalities retain immutable contents identities and explicit
//! indices. Observing a range creates no per-element storage or ownership view.

use super::*;
use crate::compiler::kernel::terms::{Terms, Work};
use std::sync::Arc;

mod histories;
mod observations;
mod reads;
mod scalars;
pub(super) use reads::ReadBinding;

#[cfg(test)]
mod boolean_tests;
#[cfg(test)]
mod history_tests;
#[cfg(test)]
mod observation_tests;
#[cfg(test)]
mod read_tests;
#[cfg(test)]
mod tests;

// Each side is either an immutable contents identity (indexed by its argument)
// or a scalar argument. Runtime observations never define an unknown identity.
pub(super) type Key = (Option<String>, Option<String>);

pub(super) struct Equality {
    symbol: String,
    captures: Vec<String>,
}

pub(super) fn parts(expression: &Expr) -> Option<(&Expr, &Expr, bool)> {
    let Kind::Binary(op, a, b) = &expression.kind else {
        return None;
    };
    (matches!(op.as_str(), "==" | "!=")
        && (matches!(a.kind, Kind::Index(..)) || matches!(b.kind, Kind::Index(..))))
    .then_some((a, b, op == "!="))
}

struct Operand {
    ty: Ty,
    contents: Option<String>,
    argument: scalars::Argument,
}

fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Int | Ty::Nat | Ty::Machine(_) | Ty::Bool)
}

impl Context<'_> {
    pub(super) fn eval_indexed_value_equality(&mut self, expression: &Expr) -> Result<Symbol> {
        let (a, b, negated) = parts(expression).ok_or("expected an indexed value equality")?;
        let hint = self.hint(a).or_else(|| self.hint(b));
        let a = self.indexed_equality_operand(a, hint.as_ref())?;
        let b = self.indexed_equality_operand(b, Some(&a.ty))?;
        self.compatible(&a.ty, &b.ty, expression.line)?;
        let proposition = self.scalar_argument_cases(&a.argument, |ctx, left| {
            ctx.scalar_argument_cases(&b.argument, |ctx, right| {
                ctx.value_equality(&(a.contents.clone(), b.contents.clone()), left, right, 0)
            })
        })?;
        Ok(Symbol::Bool(if negated {
            proposition.not()
        } else {
            proposition
        }))
    }

    fn indexed_equality_operand(
        &mut self,
        expression: &Expr,
        expected: Option<&Ty>,
    ) -> Result<Operand> {
        let Kind::Index(base, index) = &expression.kind else {
            let value = self.eval(expression, expected)?;
            return Ok(Operand {
                ty: value.ty(),
                contents: None,
                argument: self.scalar_argument(&value)?,
            });
        };
        let index = self.eval(index, Some(&Ty::Int))?.number()?;
        let array = self.storage(base)?;
        self.charge_value_work(symbol_weight(&array)?)?;
        self.remember_scalar_literal(&array)?;
        let Symbol::Array {
            element,
            len,
            identity,
            items,
            cells,
        } = &array
        else {
            return Err("indexed value equalities require array storage".into());
        };
        if !scalar(element) {
            return Err("quantified payload equalities require initialized numeric or Boolean elements; resource, union, and shaped slots need their typed observation rules".into());
        }
        self.defer_quantified_check(
            Formula::Ge(index.clone()).and(Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?)),
            "quantified array index bounds".into(),
            expression.line,
        )?;
        // Only context-independent contents justify a uniform value. A branch's
        // observed cell is not a definition of the unobserved remainder.
        let uniform = match self.arrays.history.get(identity) {
            Some(ArrayHistory::Fill(value)) => Some(value),
            None if cells.is_empty() => items.as_ref().and_then(|items| {
                let first = items.first()?;
                items.iter().all(|item| item == first).then_some(first)
            }),
            _ => None,
        };
        if let Some(value) = uniform {
            return Ok(Operand {
                ty: (**element).clone(),
                contents: None,
                argument: self.scalar_argument(value)?,
            });
        }
        Ok(Operand {
            ty: (**element).clone(),
            contents: Some(identity.clone()),
            argument: scalars::Argument::Word(index),
        })
    }

    fn declare_value_equality(&mut self, key: &Key) -> Result<Equality> {
        let mut terms = Terms::new()?;
        let mut work = Work::new(MAX_VALUE_WORK.saturating_sub(self.work.value_work));
        let mut roots = Vec::new();
        for (parameter, contents) in [("left", &key.0), ("right", &key.1)] {
            let value = terms.variable(parameter, &mut work)?;
            roots.push(match contents {
                Some(identity) => {
                    terms.application(&format!("array_contents:{identity}"), &[value], &mut work)?
                }
                None => value,
            });
        }
        self.charge_value_work(work.spent())?;
        let symbol = self.fresh_name();
        self.proof.evidence.define_scalar_equality(
            symbol.clone(),
            vec!["left".into(), "right".into()],
            Arc::new(terms),
            roots[0],
            roots[1],
        )?;
        self.arrays
            .value_equality_origins
            .insert(symbol.clone(), key.clone());
        Ok(Equality {
            symbol,
            captures: Vec::new(),
        })
    }

    pub(super) fn prove_indexed_value_equality(
        &mut self,
        goal: &Formula,
    ) -> Result<Option<evidence::NodeId>> {
        let Formula::Predicate { symbol, arguments } = goal else {
            return Ok(None);
        };
        let Some((left, right)) = self.arrays.value_equality_origins.get(symbol).cloned() else {
            return Ok(None);
        };
        if left != right || left.is_none() {
            return self.prove_scalar_read_binding(goal, &(left, right));
        }
        let [a, b] = arguments.as_slice() else {
            return Err("indexed equality has the wrong arity".into());
        };
        if a == b {
            return self
                .proof
                .evidence
                .derive(goal.clone(), evidence::Rule::ScalarReflexivity)
                .map(Some);
        }
        let Some(indices) = self.reduce_selector_formula(&equal(a, b)?, 0)? else {
            return Ok(None);
        };
        self.proof
            .evidence
            .derive(
                goal.clone(),
                evidence::Rule::ScalarCongruence {
                    equalities: vec![indices],
                },
            )
            .map(Some)
    }
}
