//! Exact, context-independent scalar computation. No caller assumptions are used
//! to choose a branch or justify machine arithmetic, so cached results do not
//! silently depend on a path that may later be restored.

use super::*;
use std::sync::Arc;

#[cfg(test)]
mod tests;

pub(super) fn is_symbolic(value: &Value<'_>) -> bool {
    matches!(value, Value::SymbolicNumber(..) | Value::SymbolicBool(_))
}

pub(super) fn weight(value: &Value<'_>) -> Result<usize> {
    Ok(match value {
        Value::SymbolicNumber(_, n) => n.terms.len().saturating_add(1),
        Value::SymbolicBool(p) => p.storage_weight()?,
        _ => 1,
    })
}

fn number(ty: Ty, n: Linear) -> Result<Value<'static>> {
    if n.terms.is_empty() {
        Value::checked_number(ty, n.constant)
    } else {
        Ok(Value::SymbolicNumber(ty, Arc::new(n)))
    }
}

fn boolean(p: Formula) -> Value<'static> {
    match values::closed_boolean(&p) {
        Some(b) => Value::Bool(b),
        None => Value::SymbolicBool(Arc::new(p)),
    }
}

fn term(value: Value<'_>) -> Result<(Ty, Linear)> {
    match value {
        Value::Number(ty, n) => Ok((ty, Linear::number(n))),
        Value::SymbolicNumber(ty, n) => Ok((ty, Arc::unwrap_or_clone(n))),
        _ => Err("ideal scalar computation expected a number".into()),
    }
}

fn proposition(value: Value<'_>) -> Result<Formula> {
    match value {
        Value::Bool(b) => Ok(if b { Formula::True } else { Formula::False }),
        Value::SymbolicBool(p) => Ok(Arc::unwrap_or_clone(p)),
        _ => Err("ideal scalar computation expected a Boolean".into()),
    }
}

pub(super) fn unary(
    op: &str,
    value: Value<'_>,
    budget: &mut Budget,
) -> Result<Option<Value<'static>>> {
    budget.spend(weight(&value)?.saturating_mul(2))?;
    match op {
        "!" => Ok(Some(boolean(proposition(value)?.not()))),
        "-" => {
            let (ty, n) = term(value)?;
            if ty != Ty::Int {
                return Ok(None);
            }
            n.scale(-1).ok().map(|n| number(ty, n)).transpose()
        }
        _ => Ok(None),
    }
}

pub(super) fn convert(ty: Ty, value: Value<'_>) -> Result<Option<Value<'static>>> {
    if let Value::Number(_, n) = value {
        return Value::checked_number(ty, n).map(Some);
    }
    let Value::SymbolicNumber(source, n) = value else {
        return Ok(None);
    };
    let exact = ty == source
        || ty == Ty::Int
        || match (&source, &ty) {
            (Ty::Machine(from), Ty::Machine(to)) => {
                let (lo, hi) = from.bounds();
                let (target_lo, target_hi) = to.bounds();
                target_lo <= lo && hi <= target_hi
            }
            (Ty::Machine(from), Ty::Nat) => from.bounds().0 >= 0,
            _ => false,
        };
    Ok(exact.then_some(Value::SymbolicNumber(ty, n)))
}

pub(super) fn binary(
    op: &str,
    a: Value<'_>,
    b: Value<'_>,
    budget: &mut Budget,
) -> Result<Option<Value<'static>>> {
    // Boolean equality duplicates both operands; charge those copies up front.
    budget.spend(weight(&a)?.saturating_add(weight(&b)?).saturating_mul(4))?;
    if matches!(a, Value::Bool(_) | Value::SymbolicBool(_)) {
        let a = proposition(a)?;
        let b = proposition(b)?;
        let value = match op {
            "&&" => a.and(b),
            "||" => a.or(b),
            "=>" => a.not().or(b),
            "==" | "!=" => {
                let equal = a.clone().and(b.clone()).or(a.not().and(b.not()));
                if op == "==" {
                    equal
                } else {
                    equal.not()
                }
            }
            _ => return Ok(None),
        };
        return Ok(Some(boolean(value)));
    }
    let (ty, a) = term(a)?;
    let (_, b) = term(b)?;
    let comparison = match op {
        "==" => Some(equal(&a, &b)?),
        "!=" => Some(equal(&a, &b)?.not()),
        ">=" => Some(Formula::Ge(a.sub(&b)?)),
        "<=" => Some(Formula::Ge(b.sub(&a)?)),
        ">" => Some(Formula::Ge(a.sub(&b)?.add(&Linear::number(-1))?)),
        "<" => Some(Formula::Ge(b.sub(&a)?.add(&Linear::number(-1))?)),
        _ => None,
    };
    if let Some(p) = comparison {
        return Ok(Some(boolean(p)));
    }
    // The checked source contract may prove a narrower domain, but this cache
    // has no path-dependent premises. In particular, do not turn unspecified
    // machine arithmetic into a mathematical equality.
    if matches!(ty, Ty::Machine(_)) {
        return Ok(None);
    }
    let result = match op {
        "+" => a.add(&b).ok(),
        "-" => a.sub(&b).ok(),
        "*" if a.terms.is_empty() => b.scale(a.constant).ok(),
        "*" if b.terms.is_empty() => a.scale(b.constant).ok(),
        _ => None,
    };
    let Some(mut result) = result else {
        return Ok(None);
    };
    if ty == Ty::Nat && op == "-" {
        if !result.terms.is_empty() {
            return Ok(None);
        }
        result.constant = result.constant.max(0);
    }
    number(ty, result).map(Some)
}
