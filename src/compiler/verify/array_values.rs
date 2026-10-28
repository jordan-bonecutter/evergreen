//! Scalar payload equalities retain immutable contents identities and explicit
//! indices. Observing a range creates no per-element storage or ownership view.

use super::*;
use crate::compiler::kernel::terms::{Terms, Work};
use std::sync::Arc;

mod defined;
mod histories;
mod observations;
mod projections;
mod reads;
mod scalars;
mod structural;
pub(super) use projections::Contents;
pub(super) use reads::ReadBinding;

#[cfg(test)]
mod boolean_tests;
#[cfg(test)]
mod field_relation_tests;
#[cfg(test)]
mod historical_observation_tests;
#[cfg(test)]
mod history_tests;
#[cfg(test)]
mod observation_tests;
#[cfg(test)]
mod projection_tests;
#[cfg(test)]
mod read_tests;
#[cfg(test)]
mod tests;

// Each side is either an immutable contents identity (indexed by its argument)
// or a scalar argument. Runtime observations never define an unknown identity.
pub(super) type Key = (Option<Contents>, Option<Contents>);

pub(super) struct Equality {
    symbol: String,
    captures: Vec<String>,
}

pub(super) fn parts(expression: &Expr) -> Option<(&Expr, &Expr, bool)> {
    let Kind::Binary(op, a, b) = &expression.kind else {
        return None;
    };
    (matches!(op.as_str(), "==" | "!=") && (indexed_base(a).is_some() || indexed_base(b).is_some()))
        .then_some((a, b, op == "!="))
}

pub(super) fn indexed_base(mut expression: &Expr) -> Option<(&Expr, &Expr)> {
    while let Kind::Field(base, _) = &expression.kind {
        expression = base;
    }
    match &expression.kind {
        Kind::Index(base, index) => Some((base, index)),
        _ => None,
    }
}

struct Operand {
    ty: Ty,
    contents: Option<Contents>,
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
        let Some((base, index, fields)) = projections::indexed_parts(expression) else {
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
            ..
        } = &array
        else {
            return Err("indexed value equalities require array storage".into());
        };
        let ty = self.scalar_projection_type((**element).clone(), &fields, expression.line)?;
        if !self.history_element(element) || !scalar(&ty) {
            return Err("quantified payload equalities require initialized numeric or Boolean elements; resource, union, and shaped slots need their typed observation rules".into());
        }
        self.defer_quantified_check(
            Formula::Ge(index.clone()).and(Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?)),
            "quantified array index bounds".into(),
            expression.line,
        )?;
        let contents = Contents {
            identity: identity.clone(),
            fields,
        };
        if let Some(value) = self.defined_array_value(&contents, None, 0)? {
            return Ok(Operand {
                ty,
                contents: None,
                argument: self.scalar_argument(&value)?,
            });
        }
        Ok(Operand {
            ty,
            contents: Some(contents),
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
                Some(contents) => contents.term(&mut terms, value, &mut work)?,
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
        let contents = left.as_ref().expect("same nonempty contents");
        if !contents.fields.is_empty() {
            let mut parent = contents.clone();
            parent.fields.pop();
            let premise = self.value_equality(&(Some(parent.clone()), Some(parent)), a, b, 0)?;
            let Some(premise) = self.prove_indexed_value_equality(&premise)? else {
                return Ok(None);
            };
            return self
                .proof
                .evidence
                .derive(
                    goal.clone(),
                    evidence::Rule::ScalarCongruence {
                        equalities: vec![premise],
                    },
                )
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
