//! Proof checking, certificates, layouts, and native code generation.
//! Execution of checked programs belongs to the separate interpreter module.

pub mod certificate;
mod effects;
pub mod kernel;
pub mod layout;
pub mod lean;
pub mod native;
mod target;
pub mod verify;
