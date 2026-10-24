//! Evergreen frontends, proof-oriented compiler, and reference interpreter.
pub mod compiler;
pub mod interpreter;
pub mod shared;
pub mod syntax;

// Keep the existing library entry points while giving implementations explicit homes.
pub use compiler::lean::emit;
pub use compiler::{certificate, kernel, layout, native, verify};
pub use interpreter as runtime;
pub use shared::planes as memory;
