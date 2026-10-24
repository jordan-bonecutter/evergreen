//! Convenience methods retained for callers of the original library API.

use super::{Result, Value};
use crate::compiler::verify::VerifiedProgram;

impl VerifiedProgram {
    pub fn run(&self) -> Result<Value> {
        super::run(self)
    }

    pub fn run_with_events(&self) -> Result<(Value, Vec<String>)> {
        super::run_with_events(self)
    }
}
