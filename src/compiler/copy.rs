//! Explicit Copy declarations. Copy is structural permission to duplicate a
//! value; move-only resources and custom destruction cannot be duplicated.
//! Shared-pointer copies additionally check census effects in the verifier.

use crate::syntax::{Program, Struct};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

pub(super) fn configure(program: &mut Program) -> Result<()> {
    let mut primitive_copies = BTreeSet::new();
    for implementation in &program.copy_impls {
        if let Some(primitive) = program.scalar_types.iter().find(|primitive| {
            primitive.module.as_ref().map_or_else(
                || primitive.name.clone(),
                |module| format!("{module}::{}", primitive.name),
            ) == implementation.target
        }) {
            primitive.validate()?;
            if primitive.module != implementation.module {
                return Err(format!(
                    "line {}: Copy must be implemented in the type's defining module",
                    implementation.line
                ));
            }
            if !primitive_copies.insert(implementation.target.clone()) {
                return Err(format!(
                    "line {}: duplicate Copy implementation for {}",
                    implementation.line, implementation.target
                ));
            }
            continue;
        }
        let record = program
            .structs
            .iter_mut()
            .find(|record| record.name == implementation.target)
            .ok_or_else(|| {
                format!(
                    "line {}: Copy requires a declared record or primitive type {}",
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
    target: crate::compiler::TargetKind,
) -> Result<()> {
    if !record.copy {
        return Ok(());
    }
    if drops.contains(&record.name) {
        return Err(format!(
            "line {}: Copy cannot be implemented for Drop type {}",
            record.line, record.name
        ));
    }
    for (field, ty) in &record.fields {
        if crate::shared::ownership::is_move_only_for(ty, prior, drops, target) {
            return Err(format!(
                "line {}: Copy requires Copy field {}.{field}",
                record.line, record.name
            ));
        }
    }
    Ok(())
}
