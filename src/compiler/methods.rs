//! Inherent methods are ordinary checked functions with an explicit receiver
//! after elaboration. No ownership/effect permissions are inferred from a name.

use crate::syntax::Program;

type Result<T> = std::result::Result<T, String>;

pub(super) fn validate(program: &Program) -> Result<()> {
    for function in &program.functions {
        let Some(target) = &function.impl_target else {
            continue;
        };
        let record = program
            .structs
            .iter()
            .find(|record| &record.name == target)
            .ok_or_else(|| {
                format!(
                    "line {}: inherent impl requires a declared record type {target}",
                    function.line
                )
            })?;
        if function.module != record.module {
            return Err(format!(
                "line {}: inherent impl must be defined in the type's module",
                function.line
            ));
        }
    }
    Ok(())
}
