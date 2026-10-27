//! Check package declarations in dependency order, independent of filenames.
//! Source order does not grant access to unverified summaries. Recursive
//! functions still need the verifier's recursion rules; recursive types and
//! mutually recursive declarations remain unsupported.

use crate::syntax::{Function, Program, Struct, Type};
use std::collections::{BTreeMap, BTreeSet};

type Names = BTreeSet<String>;
type Result<T> = std::result::Result<T, String>;

mod uses;
use uses::{function, record};

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
        .map(|s| record(s).map(|uses| uses.types))
        .collect::<Result<Vec<_>>>()?;
    rearrange(&mut program.structs, order(&keys, &dependencies, false)?);
    Ok(())
}

pub(super) enum Declaration {
    Record(usize),
    Function(usize),
}

/// Refinements depend on verified functions, while signatures and bodies depend
/// on verified types. Their combined graph must not assume either side first.
pub(super) fn verification_order(
    structs: &[Struct],
    functions: &[Function],
) -> Result<Vec<Declaration>> {
    let mut keys = structs
        .iter()
        .map(|s| (format!("type {}", s.name), s.module.clone()))
        .collect::<Vec<_>>();
    keys.extend(
        functions
            .iter()
            .map(|f| (format!("function {}", f.name), f.module.clone())),
    );
    let definitions = structs
        .iter()
        .map(|s| (s.name.as_str(), s))
        .collect::<BTreeMap<_, _>>();
    let drops = functions
        .iter()
        .filter_map(|f| f.drop_target.as_deref().map(|name| (name, f.name.as_str())))
        .collect::<BTreeMap<_, _>>();
    let mut dependencies = Vec::with_capacity(keys.len());
    for s in structs {
        let uses = record(s)?;
        dependencies.push(combined(uses));
    }
    let mut work = 0;
    for f in functions {
        let uses = function(f)?;
        let mut cleanup = cleanup_dependencies(&uses.owned, &definitions, &drops, &mut work)?;
        cleanup.extend(combined(uses));
        dependencies.push(cleanup);
    }
    Ok(order(&keys, &dependencies, true)?
        .into_iter()
        .map(|index| {
            if index < structs.len() {
                Declaration::Record(index)
            } else {
                Declaration::Function(index - structs.len())
            }
        })
        .collect())
}

fn combined(uses: uses::Uses) -> Names {
    uses.types
        .into_iter()
        .map(|name| format!("type {name}"))
        .chain(
            uses.calls
                .into_iter()
                .map(|name| format!("function {name}")),
        )
        .collect()
}

fn cleanup_dependencies(
    owned: &Names,
    structs: &BTreeMap<&str, &Struct>,
    drops: &BTreeMap<&str, &str>,
    work: &mut usize,
) -> Result<Names> {
    let mut pending = owned.iter().cloned().collect::<Vec<_>>();
    let mut seen = Names::new();
    let mut dependencies = Names::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(definition) = structs.get(name.as_str()) else {
            continue;
        };
        if definition.ideal {
            continue;
        }
        if let Some(method) = drops.get(name.as_str()) {
            dependencies.insert(format!("function {method}"));
        }
        let mut fields = definition
            .runtime_fields()
            .map(|(_, ty)| ty)
            .collect::<Vec<_>>();
        while let Some(ty) = fields.pop() {
            *work += 1;
            if *work > 262_144 {
                return Err("declaration cleanup dependency work limit reached".into());
            }
            match ty {
                Type::Named(name) => pending.push(name.clone()),
                Type::Plane(inner) | Type::Array(inner, _) => fields.push(inner),
                Type::Union(members) => fields.extend(members),
                _ => {}
            }
        }
    }
    Ok(dependencies)
}
