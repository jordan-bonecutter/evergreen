//! Bounded, simultaneous substitution for diagnostic text only. Claims with
//! binders retain their original spelling rather than risking variable capture.

use super::*;
use std::collections::BTreeMap;

pub(crate) fn substituted(expr: &Expr, values: &BTreeMap<&str, &Expr>) -> String {
    replace(expr, values, &mut 80).map_or_else(|| expression(expr), |expr| expression(&expr))
}

fn replace(expr: &Expr, values: &BTreeMap<&str, &Expr>, budget: &mut usize) -> Option<Expr> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    if let Kind::Name(name) = &expr.kind {
        if let Some(value) = values.get(name.as_str()) {
            return Some((**value).clone());
        }
    }
    let mut result = expr.clone();
    match &mut result.kind {
        Kind::Forall { .. } | Kind::Block(..) | Kind::Generic { .. } => return None,
        Kind::Unary(_, value) | Kind::Field(value, _) | Kind::FactAt(value, _) => {
            **value = replace(value, values, budget)?;
        }
        Kind::Binary(_, a, b) | Kind::Index(a, b) => {
            **a = replace(a, values, budget)?;
            **b = replace(b, values, budget)?;
        }
        Kind::If(c, a, b) => {
            **c = replace(c, values, budget)?;
            **a = replace(a, values, budget)?;
            **b = replace(b, values, budget)?;
        }
        Kind::Call(_, args) | Kind::Array(args) => {
            for arg in args {
                *arg = replace(arg, values, budget)?;
            }
        }
        Kind::Record(_, fields) => {
            for (_, field) in fields {
                *field = replace(field, values, budget)?;
            }
        }
        Kind::Type(_)
        | Kind::Bytes(_)
        | Kind::Name(_)
        | Kind::Number(_)
        | Kind::Constant(..)
        | Kind::Bool(_)
        | Kind::Unit => {}
    }
    Some(result)
}
