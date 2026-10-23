//! Conservative, checked effect summaries for invariant-independent helpers.
//! Accepted functions touch only scalar values and read-only scalar borrows.
//! Unknown effects remain unknown; callers must not assume they are harmless.
use crate::syntax::{Expr, Function, Kind, Statement, Type};
use std::collections::{BTreeMap, BTreeSet};

fn scalar(t: &Type) -> bool {
    matches!(t, Type::Machine(_) | Type::Bool | Type::Unit)
}
fn leaf(t: &Type) -> bool {
    scalar(t) || matches!(t, Type::Ref(inner) if matches!(**inner, Type::Machine(_) | Type::Bool))
}

fn hint(
    e: &Expr,
    env: &BTreeMap<String, Type>,
    functions: &BTreeMap<String, Function>,
) -> Option<Type> {
    match &e.kind {
        Kind::Name(n) => env.get(n).cloned(),
        Kind::Constant(t, _) => Some(Type::Machine(*t)),
        Kind::Unary(op, x) if op == "*" => {
            if let Some(Type::Ref(t)) = hint(x, env, functions) {
                Some(*t)
            } else {
                None
            }
        }
        Kind::Unary(_, x) => hint(x, env, functions),
        Kind::Binary(_, a, b) => hint(a, env, functions).or_else(|| hint(b, env, functions)),
        Kind::Call(n, _) => functions.get(n).map(|f| f.ret.clone()),
        _ => None,
    }
}

fn expression(
    e: &Expr,
    expected: Option<&Type>,
    env: &BTreeMap<String, Type>,
    functions: &BTreeMap<String, Function>,
    safe: &BTreeSet<String>,
) -> Option<Type> {
    let value = match &e.kind {
        Kind::Number(_) => expected.filter(|t| matches!(t, Type::Machine(_)))?.clone(),
        Kind::Constant(t, _) => Type::Machine(*t),
        Kind::Bool(_) => Type::Bool,
        Kind::Unit => Type::Unit,
        Kind::Name(n) => env.get(n)?.clone(),
        Kind::Unary(op, x) if op == "&" => {
            if !matches!(&x.kind, Kind::Name(_)) {
                return None;
            }
            let t = expression(x, None, env, functions, safe)?;
            if !matches!(t, Type::Machine(_) | Type::Bool) {
                return None;
            }
            Type::Ref(Box::new(t))
        }
        Kind::Unary(op, x) if op == "*" => {
            let Type::Ref(t) = expression(x, None, env, functions, safe)? else {
                return None;
            };
            if !scalar(&t) {
                return None;
            }
            *t
        }
        Kind::Unary(op, x) if op == "!" => {
            expression(x, Some(&Type::Bool), env, functions, safe)?;
            Type::Bool
        }
        Kind::Unary(_, x) => {
            let t = expected.cloned().or_else(|| hint(x, env, functions))?;
            if !matches!(t, Type::Machine(_)) {
                return None;
            }
            expression(x, Some(&t), env, functions, safe)?;
            t
        }
        Kind::Binary(op, a, b) => {
            if op == "&&" || op == "||" {
                expression(a, Some(&Type::Bool), env, functions, safe)?;
                expression(b, Some(&Type::Bool), env, functions, safe)?;
                Type::Bool
            } else {
                let arithmetic = matches!(op.as_str(), "+" | "-" | "*");
                let t = if arithmetic { expected.cloned() } else { None }
                    .or_else(|| hint(a, env, functions))
                    .or_else(|| hint(b, env, functions))?;
                if !matches!(t, Type::Machine(_)) {
                    return None;
                }
                expression(a, Some(&t), env, functions, safe)?;
                expression(b, Some(&t), env, functions, safe)?;
                if arithmetic {
                    t
                } else {
                    Type::Bool
                }
            }
        }
        Kind::If(c, a, b) => {
            expression(c, Some(&Type::Bool), env, functions, safe)?;
            let t = expression(a, expected, env, functions, safe)?;
            expression(b, Some(&t), env, functions, safe)?;
            t
        }
        Kind::Call(n, args) => {
            if !safe.contains(n) {
                return None;
            }
            let f = functions.get(n)?;
            if f.params.len() != args.len() {
                return None;
            }
            for ((_, t), e) in f.params.iter().zip(args) {
                expression(e, Some(t), env, functions, safe)?;
            }
            f.ret.clone()
        }
        _ => return None,
    };
    if !leaf(&value) || expected.is_some_and(|t| t != &value) {
        return None;
    }
    Some(value)
}

/// Applied only after type checking, bounds proofs, and termination checking.
pub(crate) fn invariant_independent(
    f: &Function,
    functions: &BTreeMap<String, Function>,
    safe: &BTreeSet<String>,
) -> bool {
    if f.ideal
        || !scalar(&f.ret)
        || f.params.iter().any(|(_, t)| !leaf(t))
        || f.drop_target.is_some()
    {
        return false;
    }
    let mut env: BTreeMap<String, Type> = f.params.iter().cloned().collect();
    // Contracts and their proof computations are erased, not runtime effects.
    for s in &f.body {
        match s {
            Statement::Let { name, ty, value } => {
                let Some(t) = expression(value, ty.as_ref(), &env, functions, safe) else {
                    return false;
                };
                env.insert(name.clone(), t);
            }
            Statement::Assign { target, value } => {
                let Kind::Name(n) = &target.kind else {
                    return false;
                };
                let Some(t) = env.get(n) else {
                    return false;
                };
                if expression(value, Some(t), &env, functions, safe).is_none() {
                    return false;
                }
            }
            Statement::Effect(e) => {
                if expression(e, None, &env, functions, safe).is_none() {
                    return false;
                }
            }
            Statement::Fact { .. } | Statement::Proof { .. } => {} // Checked proof code, erased at execution.
            Statement::Update { .. } => return false,
        }
    }
    expression(&f.result, Some(&f.ret), &env, functions, safe).is_some()
}
