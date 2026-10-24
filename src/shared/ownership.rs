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
                || structs.get(n).is_some_and(|s| {
                    s.affine || s.fields.iter().any(|(_, t)| is_affine(t, structs, drops))
                })
        }
        Type::Array(t, _) => is_affine(t, structs, drops),
        _ => false,
    }
}
