//! Proof checking, certificates, layouts, and native code generation.
//! Execution of checked programs belongs to the separate interpreter module.

pub mod certificate;
mod copy;
mod declarations;
mod effects;
mod field_sugar;
mod generics;
pub mod kernel;
pub mod layout;
mod methods;
pub mod native;
mod scalar_types;
mod sources;
pub(crate) use crate::shared::target;
pub mod verify;

/// Whether this bootstrap embeds a standard-library package with this name.
pub fn is_bundled_module(name: &str) -> bool {
    sources::is_bundled_module(name)
}
