//! Conservative, checked scalar effect summaries. Invariant-independent helpers
//! are read-only; ownership-free helpers may use checked write contracts.
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

struct Safe<'a> {
    known: &'a BTreeSet<String>,
    current: &'a str,
}

impl Safe<'_> {
    fn contains(&self, name: &str) -> bool {
        name == self.current || self.known.contains(name)
    }
}

fn expression(
    e: &Expr,
    expected: Option<&Type>,
    env: &BTreeMap<String, Type>,
    functions: &BTreeMap<String, Function>,
    safe: &Safe<'_>,
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
            if matches!(op.as_str(), "&&" | "||" | "=>") {
                expression(a, Some(&Type::Bool), env, functions, safe)?;
                expression(b, Some(&Type::Bool), env, functions, safe)?;
                Type::Bool
            } else {
                let arithmetic = matches!(op.as_str(), "+" | "-" | "*");
                let t = if arithmetic { expected.cloned() } else { None }
                    .or_else(|| hint(a, env, functions))
                    .or_else(|| hint(b, env, functions))?;
                let equality = matches!(op.as_str(), "==" | "!=");
                if !matches!(t, Type::Machine(_))
                    && !(equality && matches!(t, Type::Bool | Type::Ref(_)))
                {
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
            for ((name, t), e) in f.params.iter().zip(args) {
                if f.ideal_params.contains(name) {
                    continue;
                }
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
    scalar_effects(f, functions, safe, false)
}

/// Calls with scalar/reference interfaces and no creation, transfer, or cleanup
/// of runtime ownership. Writes remain subject to each caller's permissions.
pub(crate) fn ownership_free(
    f: &Function,
    functions: &BTreeMap<String, Function>,
    safe: &BTreeSet<String>,
) -> bool {
    scalar_effects(f, functions, safe, true)
}

fn scalar_effects(
    f: &Function,
    functions: &BTreeMap<String, Function>,
    safe: &BTreeSet<String>,
    writes: bool,
) -> bool {
    if f.ideal
        || f.partial
        || (!writes && !f.modifies.is_empty())
        || !(if writes { leaf(&f.ret) } else { scalar(&f.ret) })
        || f.params
            .iter()
            .any(|(n, t)| !f.ideal_params.contains(n) && !leaf(t))
        || f.drop_target.is_some()
    {
        return false;
    }
    // Effects of a self-recursive body are checked as a fixed point. Totality has
    // already been established, and every non-self effect is still inspected.
    let recursive_safe = Safe {
        known: safe,
        current: &f.name,
    };
    let safe = &recursive_safe;
    let mut env: BTreeMap<String, Type> = f
        .params
        .iter()
        .filter(|(n, _)| !f.ideal_params.contains(n))
        .cloned()
        .collect();
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
                let ty = match &target.kind {
                    Kind::Name(n) => env.get(n).cloned(),
                    Kind::Unary(op, _) if writes && op == "*" => {
                        expression(target, None, &env, functions, safe)
                    }
                    _ => None,
                };
                let Some(t) = ty else {
                    return false;
                };
                if expression(value, Some(&t), &env, functions, safe).is_none() {
                    return false;
                }
            }
            Statement::Effect(e) => {
                if expression(e, None, &env, functions, safe).is_none() {
                    return false;
                }
            }
            Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => {} // Checked proof code, erased at execution.
            Statement::Update { .. } | Statement::Destructure { .. } => return false,
        }
    }
    expression(&f.result, Some(&f.ret), &env, functions, safe).is_some()
}

pub(crate) fn recursive(function: &Function) -> bool {
    fn expression(e: &Expr, name: &str) -> bool {
        match &e.kind {
            Kind::Call(target, args) => target == name || args.iter().any(|e| expression(e, name)),
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => expression(e, name),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => expression(a, name) || expression(b, name),
            Kind::If(c, a, b) => expression(c, name) || expression(a, name) || expression(b, name),
            Kind::Array(items) => items.iter().any(|e| expression(e, name)),
            Kind::Record(_, fields) => fields.iter().any(|(_, e)| expression(e, name)),
            _ => false,
        }
    }

    fn statement(s: &Statement, name: &str) -> bool {
        match s {
            Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => false,
            Statement::Let { value, .. }
            | Statement::Destructure { value, .. }
            | Statement::Effect(value) => expression(value, name),
            Statement::Assign { target, value } => {
                expression(target, name) || expression(value, name)
            }
            Statement::Update { body, .. } => body.iter().any(|s| statement(s, name)),
        }
    }
    function.body.iter().any(|s| statement(s, &function.name))
        || expression(&function.result, &function.name)
}
