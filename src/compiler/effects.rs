//! Conservative, checked scalar effect summaries. Invariant-independent helpers
//! are read-only; ownership-free helpers may use checked write contracts.
//! Unknown effects remain unknown; callers must not assume they are harmless.

use crate::syntax::{Expr, Function, Kind, MachineInt, Statement, Struct, Type};
use std::collections::{BTreeMap, BTreeSet};

fn scalar(t: &Type) -> bool {
    matches!(t, Type::Machine(_) | Type::Bool | Type::Unit)
}

fn leaf(t: &Type) -> bool {
    scalar(t) || matches!(t, Type::Ref(_) | Type::Shape(_))
}

/// A verified unit function with no runtime body only disposes its parameters
/// through their normal checked scope cleanup. This grants no permission to
/// allocate, mutate caller storage, or run while invariants are suspended.
pub(crate) fn disposes_parameters(function: &Function) -> bool {
    !function.ideal
        && !function.partial
        && function.external.is_none()
        && function.drop_target.is_none()
        && function.modifies.is_empty()
        && function.ret == Type::Unit
        && matches!(function.result.kind, Kind::Unit)
        && function.body.iter().all(|statement| {
            matches!(
                statement,
                Statement::Fact { .. } | Statement::Proof { .. } | Statement::Ideal(_)
            )
        })
}

fn hint(
    e: &Expr,
    env: &BTreeMap<String, Type>,
    functions: &BTreeMap<String, Function>,
    structs: &BTreeMap<String, Struct>,
) -> Option<Type> {
    match &e.kind {
        Kind::Name(n) => env.get(n).cloned(),
        Kind::Constant(t, _) => Some(Type::Machine(*t)),
        Kind::Unary(op, x) if op == "*" => {
            if let Some(Type::Ref(t)) = hint(x, env, functions, structs) {
                Some(*t)
            } else {
                None
            }
        }
        Kind::Unary(_, x) => hint(x, env, functions, structs),
        Kind::Field(base, field) => {
            let Type::Named(name) = hint(base, env, functions, structs)? else {
                return None;
            };
            structs
                .get(&name)?
                .runtime_fields()
                .find(|(n, _)| n == field)
                .map(|(_, t)| t.clone())
        }
        Kind::Index(base, _) => {
            let Type::Array(element, _) = hint(base, env, functions, structs)? else {
                return None;
            };
            Some(*element)
        }
        Kind::Binary(_, a, b) => {
            hint(a, env, functions, structs).or_else(|| hint(b, env, functions, structs))
        }
        Kind::Call(n, _) if MachineInt::parse(n).is_some() => {
            MachineInt::parse(n).map(Type::Machine)
        }
        Kind::Call(n, _) => functions.get(n).map(|f| f.ret.clone()),
        _ => None,
    }
}

struct Safe<'a> {
    known: &'a BTreeSet<String>,
    current: &'a str,
    structs: &'a BTreeMap<String, Struct>,
}

impl Safe<'_> {
    fn contains(&self, name: &str) -> bool {
        name == self.current || self.known.contains(name)
    }
}

// Inspect storage without treating an intermediate record or owning pointer as
// an rvalue. Every evaluated pointer/index still passes through effect checking.
// The ordinary verifier checks liveness, bounds, invariants, and write authority.
fn place(
    e: &Expr,
    env: &BTreeMap<String, Type>,
    functions: &BTreeMap<String, Function>,
    safe: &Safe<'_>,
) -> Option<Type> {
    match &e.kind {
        Kind::Name(name) => env.get(name).cloned(),
        Kind::Unary(op, pointer) if op == "*" => {
            let ty = match &pointer.kind {
                Kind::Name(_) | Kind::Field(..) | Kind::Index(..) | Kind::Unary(_, _) => {
                    place(pointer, env, functions, safe)?
                }
                _ => expression(pointer, None, env, functions, safe)?,
            };
            match ty {
                Type::Ref(target) | Type::Unique(target) | Type::Shared(target) => Some(*target),
                _ => None,
            }
        }
        Kind::Field(base, field) => {
            let Type::Named(name) = place(base, env, functions, safe)? else {
                return None;
            };
            safe.structs
                .get(&name)?
                .runtime_fields()
                .find(|(n, _)| n == field)
                .map(|(_, t)| t.clone())
        }
        Kind::Index(base, index) => {
            let Type::Array(element, _) = place(base, env, functions, safe)? else {
                return None;
            };
            expression(
                index,
                Some(&Type::Machine(MachineInt::parse("usize")?)),
                env,
                functions,
                safe,
            )?;
            Some(*element)
        }
        _ => None,
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
        Kind::Unary(op, x) if op == "&" => Type::Ref(Box::new(place(x, env, functions, safe)?)),
        Kind::Unary(op, _) if op == "*" => place(e, env, functions, safe)?,
        Kind::Field(..) | Kind::Index(..) => place(e, env, functions, safe)?,
        Kind::Unary(op, x) if op == "!" => {
            expression(x, Some(&Type::Bool), env, functions, safe)?;
            Type::Bool
        }
        Kind::Unary(_, x) => {
            let t = expected
                .cloned()
                .or_else(|| hint(x, env, functions, safe.structs))?;
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
                    .or_else(|| hint(a, env, functions, safe.structs))
                    .or_else(|| hint(b, env, functions, safe.structs))?;
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
        Kind::Call(n, args) if MachineInt::parse(n).is_some() => {
            let [argument] = args.as_slice() else {
                return None;
            };
            let target = Type::Machine(MachineInt::parse(n)?);
            let source =
                hint(argument, env, functions, safe.structs).unwrap_or_else(|| target.clone());
            if !matches!(source, Type::Machine(_)) {
                return None;
            }
            expression(argument, Some(&source), env, functions, safe)?;
            target
        }
        Kind::Call(n, args) => {
            if !safe.contains(n) {
                return None;
            }
            let f = functions.get(n)?;
            let supplied = f.supplied_parameters(args.len()).ok()?;
            for ((name, t), e) in supplied.into_iter().zip(args) {
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
    structs: &BTreeMap<String, Struct>,
) -> bool {
    scalar_effects(f, functions, safe, structs, false)
}

/// Calls with scalar/reference interfaces and no creation, transfer, or cleanup
/// of runtime ownership. Writes remain subject to each caller's permissions.
pub(crate) fn ownership_free(
    f: &Function,
    functions: &BTreeMap<String, Function>,
    safe: &BTreeSet<String>,
    structs: &BTreeMap<String, Struct>,
) -> bool {
    scalar_effects(f, functions, safe, structs, true)
}

fn scalar_effects(
    f: &Function,
    functions: &BTreeMap<String, Function>,
    safe: &BTreeSet<String>,
    structs: &BTreeMap<String, Struct>,
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
        structs,
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
                    _ if writes => place(target, &env, functions, safe),
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
            Statement::Update { .. } | Statement::Destructure { .. } | Statement::While { .. } => {
                return false
            }
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
            Kind::Block(body, tail) => {
                body.iter().any(|s| statement(s, name)) || expression(tail, name)
            }
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
            Statement::While {
                condition, body, ..
            } => expression(condition, name) || body.iter().any(|s| statement(s, name)),
        }
    }
    function.body.iter().any(|s| statement(s, &function.name))
        || expression(&function.result, &function.name)
}

pub(crate) fn unmeasured_loops(function: &Function) -> bool {
    fn expression(e: &Expr) -> bool {
        match &e.kind {
            Kind::Block(body, tail) => body.iter().any(contains) || expression(tail),
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => expression(e),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => expression(a) || expression(b),
            Kind::If(c, a, b) => expression(c) || expression(a) || expression(b),
            Kind::Array(items) | Kind::Call(_, items) => items.iter().any(expression),
            Kind::Record(_, fields) => fields.iter().any(|(_, e)| expression(e)),
            _ => false,
        }
    }
    fn contains(statement: &Statement) -> bool {
        match statement {
            Statement::While {
                condition,
                decreases,
                body,
                ..
            } => decreases.is_none() || expression(condition) || body.iter().any(contains),
            Statement::Ideal(inner) => contains(inner),
            Statement::Update { body, .. } => body.iter().any(contains),
            Statement::Let { value, .. }
            | Statement::Destructure { value, .. }
            | Statement::Effect(value) => expression(value),
            Statement::Assign { target, value } => expression(target) || expression(value),
            Statement::Fact { .. } | Statement::Proof { .. } => false,
        }
    }
    function.body.iter().any(contains) || expression(&function.result)
}
