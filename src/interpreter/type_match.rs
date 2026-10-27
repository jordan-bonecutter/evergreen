//! Erased dependent extents have no runtime binding. The verified call checks
//! them; reference execution still checks pointer roles, element types, literal
//! extents, and actual storage bounds independently.

use super::*;

// Bounds on a pointee do not change the pointer header. Inline bounds do
// change storage; without a closed extent, retain no speculative identity.
pub(super) fn same_storage_type(actual: &Type, expected: &Type) -> bool {
    match (actual, expected) {
        (Type::Ref(_), Type::Ref(_))
        | (Type::Unique(_), Type::Unique(_))
        | (Type::Shared(_), Type::Shared(_)) => true,
        (Type::Shape(a), Type::Shape(b)) => same_storage_type(a, b),
        (Type::Array(a, n), Type::Array(b, m)) => {
            same_storage_type(a, b)
                && match (
                    crate::compiler::layout::array_length(n),
                    crate::compiler::layout::array_length(m),
                ) {
                    (Ok(n), Ok(m)) => n == m,
                    _ => false,
                }
        }
        (Type::Union(a), Type::Union(b)) => same_union_storage(a, b),
        _ => actual == expected,
    }
}

pub(super) fn same_union_storage(a: &[Type], b: &[Type]) -> bool {
    a.len() == b.len()
        && a.iter().all(|a| b.iter().any(|b| same_storage_type(a, b)))
        && b.iter().all(|b| a.iter().any(|a| same_storage_type(a, b)))
}

pub(super) fn same_runtime_type(actual: &Type, expected: &Type) -> Result<bool> {
    Ok(match (actual, expected) {
        (Type::Unique(a), Type::Unique(b))
        | (Type::Shared(a), Type::Shared(b))
        | (Type::Ref(a), Type::Ref(b))
        | (Type::Shape(a), Type::Shape(b)) => same_runtime_type(a, b)?,
        (Type::Array(a, n), Type::Array(b, m)) => {
            same_runtime_type(a, b)?
                && (!crate::syntax::constant_extent(n)
                    || !crate::syntax::constant_extent(m)
                    || crate::compiler::layout::array_length(n)?
                        == crate::compiler::layout::array_length(m)?)
        }
        _ => actual == expected,
    })
}
