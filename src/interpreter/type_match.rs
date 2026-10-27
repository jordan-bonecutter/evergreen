//! Erased dependent extents have no runtime binding. The verified call checks
//! them; reference execution still checks pointer roles, element types, literal
//! extents, and actual storage bounds independently.

use super::*;

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
