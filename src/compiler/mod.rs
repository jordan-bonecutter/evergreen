//! Proof checking, certificates, layouts, and native code generation.
//! Execution of checked programs belongs to the separate interpreter module.

pub mod certificate;
mod declarations;
mod effects;
mod field_sugar;
pub mod kernel;
pub mod layout;
pub mod lean;
pub mod native;
mod scalar_types;
mod sources;
mod target;
pub mod verify;
