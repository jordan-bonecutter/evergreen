//! Check package declarations in dependency order, independent of filenames.
//! Source order does not grant access to unverified summaries. Recursive
//! functions still need the verifier's recursion rules; recursive types and
//! mutually recursive declarations remain unsupported.

use crate::syntax::{Expr, Function, Kind, Program, Statement, Type};
use std::collections::{BTreeMap, BTreeSet};

type Names = BTreeSet<String>;
type Result<T> = std::result::Result<T, String>;

fn expression(expr: &Expr, names: &mut Names, calls: bool) {
    match &expr.kind {
        Kind::Call(name, args) => {
            if calls {
                names.insert(name.clone());
            }
            for arg in args {
                expression(arg, names, calls);
            }
        }
        Kind::Record(name, fields) => {
            if !calls {
                names.insert(name.clone());
            }
            for (_, value) in fields {
                expression(value, names, calls);
            }
        }
        Kind::Unary(_, value) | Kind::Field(value, _) | Kind::FactAt(value, _) => {
            expression(value, names, calls)
        }
        Kind::Binary(_, left, right) | Kind::Index(left, right) => {
            expression(left, names, calls);
            expression(right, names, calls);
        }
        Kind::If(condition, left, right) => {
            expression(condition, names, calls);
            expression(left, names, calls);
            expression(right, names, calls);
        }
        Kind::Array(values) => {
            for value in values {
                expression(value, names, calls);
            }
        }
        _ => {}
    }
}

fn ty(ty: &Type, names: &mut Names, calls: bool) {
    match ty {
        Type::Named(name) if !calls => {
            names.insert(name.clone());
        }
        Type::Ref(inner) | Type::Plane(inner) | Type::Shape(inner) => self::ty(inner, names, calls),
        Type::Union(members) => {
            for member in members {
                self::ty(member, names, calls);
            }
        }
        Type::Array(inner, count) => {
            self::ty(inner, names, calls);
            expression(count, names, calls);
        }
        _ => {}
    }
}

fn statement(statement: &Statement, names: &mut Names) {
    match statement {
        Statement::Ideal(inner) => self::statement(inner, names),
        Statement::Let {
            ty: hint, value, ..
        } => {
            if let Some(hint) = hint {
                ty(hint, names, true);
            }
            expression(value, names, true);
        }
        Statement::Destructure { value, .. }
        | Statement::Fact { value, .. }
        | Statement::Effect(value) => expression(value, names, true),
        Statement::Proof { proposition, .. } => expression(proposition, names, true),
        Statement::Assign { target, value } => {
            expression(target, names, true);
            expression(value, names, true);
        }
        Statement::While {
            condition,
            invariant,
            modifies,
            body,
            ..
        } => {
            expression(condition, names, true);
            expression(invariant, names, true);
            for effect in modifies {
                expression(effect, names, true);
            }
            for item in body {
                self::statement(item, names);
            }
        }
        Statement::Update { places, body, .. } => {
            for place in places {
                expression(place, names, true);
            }
            for item in body {
                self::statement(item, names);
            }
        }
    }
}

fn function(function: &Function) -> Names {
    let mut names = Names::new();
    for (_, hint) in &function.params {
        ty(hint, &mut names, true);
    }
    ty(&function.ret, &mut names, true);
    for expr in function
        .pre
        .iter()
        .chain(function.post.iter())
        .chain(function.decreases.iter())
        .chain(function.modifies.iter())
    {
        expression(expr, &mut names, true);
    }
    for borrow in &function.borrows {
        expression(&borrow.reference, &mut names, true);
    }
    for item in &function.body {
        statement(item, &mut names);
    }
    expression(&function.result, &mut names, true);
    names
}

fn order(
    keys: &[(String, Option<String>)],
    dependencies: &[Names],
    self_recursion: bool,
) -> Result<Vec<usize>> {
    let indices = keys
        .iter()
        .enumerate()
        .map(|(index, (name, _))| (name.as_str(), index))
        .collect::<BTreeMap<_, _>>();
    let mut states = vec![0; keys.len()];
    let mut result = Vec::with_capacity(keys.len());
    for index in 0..keys.len() {
        let mut pending = vec![(index, false)];
        while let Some((current, complete)) = pending.pop() {
            if complete {
                states[current] = 2;
                result.push(current);
                continue;
            }
            match states[current] {
                2 => continue,
                1 => {
                    return Err(format!(
                        "mutually recursive declarations are unsupported: {}",
                        keys[current].0
                    ))
                }
                _ => {}
            }
            states[current] = 1;
            pending.push((current, true));
            for name in dependencies[current].iter().rev() {
                let Some(&dependency) = indices.get(name.as_str()) else {
                    continue;
                };
                if self_recursion && dependency == current {
                    continue;
                }
                pending.push((dependency, false));
            }
        }
    }
    Ok(result)
}

fn rearrange<T>(values: &mut Vec<T>, order: Vec<usize>) {
    let mut slots = std::mem::take(values)
        .into_iter()
        .map(Some)
        .collect::<Vec<_>>();
    values.extend(order.into_iter().map(|index| {
        slots[index]
            .take()
            .expect("each declaration scheduled once")
    }));
}

pub(super) fn schedule_types(program: &mut Program) -> Result<()> {
    let keys = program
        .structs
        .iter()
        .map(|s| (s.name.clone(), s.module.clone()))
        .collect::<Vec<_>>();
    let dependencies = program
        .structs
        .iter()
        .map(|s| {
            let mut names = Names::new();
            for (_, field) in &s.fields {
                ty(field, &mut names, false);
            }
            for (_, fact) in &s.facts {
                expression(fact, &mut names, false);
            }
            if let Some(invariant) = &s.invariant {
                expression(invariant, &mut names, false);
            }
            names
        })
        .collect::<Vec<_>>();
    rearrange(&mut program.structs, order(&keys, &dependencies, false)?);
    Ok(())
}

pub(super) fn schedule_functions(program: &mut Program) -> Result<()> {
    let keys = program
        .functions
        .iter()
        .map(|f| (f.name.clone(), f.module.clone()))
        .collect::<Vec<_>>();
    let dependencies = program.functions.iter().map(function).collect::<Vec<_>>();
    rearrange(&mut program.functions, order(&keys, &dependencies, true)?);
    Ok(())
}
