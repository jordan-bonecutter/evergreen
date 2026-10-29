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
mod refinements;
mod scalar_types;
mod sources;
pub(crate) use crate::shared::target;
pub use crate::shared::target::TargetKind;
pub mod verify;
pub mod wasm;

/// Whether this bootstrap embeds a standard-library package with this name.
pub fn is_bundled_module(name: &str) -> bool {
    sources::is_bundled_module(name)
}

/// Read the embedded source named by a bundled-library diagnostic.
pub fn bundled_source(path: &str) -> Option<&'static str> {
    sources::bundled_source(path)
}
