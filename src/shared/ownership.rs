//! Structural ownership classification used by the checker and both backends.

use crate::syntax::{Struct, Type};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn is_move_only(
    t: &Type,
    structs: &BTreeMap<String, Struct>,
    drops: &BTreeSet<String>,
) -> bool {
    is_move_only_for(t, structs, drops, super::target::TargetKind::X86_64)
}

pub(crate) fn is_move_only_for(
    t: &Type,
    structs: &BTreeMap<String, Struct>,
    drops: &BTreeSet<String>,
    target: super::target::TargetKind,
) -> bool {
    match t {
        Type::Union(_) | Type::Shape(_) => true,
        Type::Unique(_) => true,
        Type::Machine(_) | Type::Bool | Type::Unit | Type::Ref(_) | Type::Shared(_) => {
            !target.profile().is_ok_and(|profile| profile.is_copy(t))
        }
        Type::Named(n) => {
            drops.contains(n)
                || structs.get(n).is_none_or(|s| {
                    !s.copy
                        || s.fields
                            .iter()
                            .any(|(_, t)| is_move_only_for(t, structs, drops, target))
                })
        }
        Type::Array(t, _) => is_move_only_for(t, structs, drops, target),
        _ => false,
    }
}

// Move semantics and runtime destruction are independent: a non-Copy record can
// contain only borrowed references/scalars and have no destructor work at all.
pub(crate) fn needs_drop(
    t: &Type,
    structs: &BTreeMap<String, Struct>,
    drops: &BTreeSet<String>,
) -> bool {
    match t {
        Type::Union(_) => true, // Raw unions require explicit active-member elimination.
        Type::Shape(_) => false,
        Type::Unique(_) | Type::Shared(_) => true,
        Type::Named(name) => {
            drops.contains(name)
                || structs.get(name).is_some_and(|record| {
                    record
                        .runtime_fields()
                        .any(|(_, ty)| needs_drop(ty, structs, drops))
                })
        }
        Type::Array(inner, _) => needs_drop(inner, structs, drops),
        _ => false,
    }
}
