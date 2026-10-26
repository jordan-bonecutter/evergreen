//! Explicit Copy declarations. Copy is structural permission to duplicate a
//! value; it cannot hide ownership, affine proof resources, or destructor work.

use crate::syntax::{Program, Struct};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

pub(super) fn configure(program: &mut Program) -> Result<()> {
    for implementation in &program.copy_impls {
        let record = program
            .structs
            .iter_mut()
            .find(|record| record.name == implementation.target)
            .ok_or_else(|| {
                format!(
                    "line {}: Copy requires a declared record type {}",
                    implementation.line, implementation.target
                )
            })?;
        if record.module != implementation.module {
            return Err(format!(
                "line {}: Copy must be implemented in the type's defining module",
                implementation.line
            ));
        }
        if record.copy {
            return Err(format!(
                "line {}: duplicate Copy implementation for {}",
                implementation.line, record.name
            ));
        }
        record.copy = true;
    }
    Ok(())
}

pub(super) fn validate(
    record: &Struct,
    prior: &BTreeMap<String, Struct>,
    drops: &BTreeSet<String>,
) -> Result<()> {
    if !record.copy {
        return Ok(());
    }
    if record.affine || drops.contains(&record.name) {
        return Err(format!(
            "line {}: Copy cannot be implemented for affine or Drop type {}",
            record.line, record.name
        ));
    }
    for (field, ty) in &record.fields {
        if crate::shared::ownership::is_affine(ty, prior, drops) {
            return Err(format!(
                "line {}: Copy requires Copy field {}.{field}",
                record.line, record.name
            ));
        }
    }
    Ok(())
}
