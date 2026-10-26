//! Structural ownership classification used by the checker and both backends.

use crate::syntax::{Struct, Type};
use std::collections::{BTreeMap, BTreeSet};

pub(crate) fn is_affine(
    t: &Type,
    structs: &BTreeMap<String, Struct>,
    drops: &BTreeSet<String>,
) -> bool {
    match t {
        Type::Plane(_) => true,
        Type::Named(n) => {
            drops.contains(n)
                || structs.get(n).is_none_or(|s| {
                    !s.copy
                        || s.affine
                        || s.fields.iter().any(|(_, t)| is_affine(t, structs, drops))
                })
        }
        Type::Array(t, _) => is_affine(t, structs, drops),
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
        Type::Plane(_) => true,
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
