//! Small Linux x86-64 backend. Source verification is required before emission.
//! This backend is trusted code, not a machine-checked compiler-correctness proof.

use crate::{
    compiler::layout,
    compiler::verify::VerifiedProgram,
    syntax::{Expr, External, Function, Kind, MachineInt, Statement, Struct, Type},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

mod aggregates;
mod allocation;
mod assignments;
mod atomic;
mod blocks;
mod calls;
mod cleanup;
mod elf;
mod expressions;
mod frame;
mod liveness;
mod order;
mod places;
mod program;
mod scalars;
mod statements;
mod storage;
mod syscall;
mod typing;
mod unions;

const STACK: usize = 65536;
const MAX_CODE: usize = 8 * 1024 * 1024;
const RECURSION_LIMIT: usize = 128;

fn scalar(t: &Type) -> Result<()> {
    if matches!(t, Type::Machine(_) | Type::Bool | Type::Unit) {
        Ok(())
    } else {
        Err("native main must return a machine integer, Boolean, or unit value".into())
    }
}

fn machine() -> Type {
    Type::Machine(MachineInt::parse("isize").expect("isize"))
}

fn patch(code: &mut [u8], displacement: usize, target: usize) -> Result<()> {
    let relative = i32::try_from(target as i64 - (displacement + 4) as i64)
        .map_err(|_| "native branch displacement overflow")?;
    code.get_mut(displacement..displacement + 4)
        .ok_or("invalid native relocation")?
        .copy_from_slice(&relative.to_le_bytes());
    Ok(())
}

#[derive(Clone)]
struct Compiled {
    offset: usize,
    stack: usize,
}

#[derive(Clone, Copy)]
enum ReadMode {
    Place,
    Value,
    Storage,
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(test), allow(dead_code))]
enum TraceMode {
    Value,
    Count,
    Order,
}

#[derive(Clone)]
struct Local {
    offset: i32,
    ty: Type,
    drop_flag: Option<i32>,
}

struct Emitter<'a> {
    code: &'a mut Vec<u8>,
    known: &'a BTreeMap<String, Compiled>,
    functions: &'a BTreeMap<String, &'a Function>,
    slots: BTreeMap<String, Local>,
    frame: usize,
    structs: &'a BTreeMap<String, Struct>,
    temporary: usize,
    peak: usize,
    drops: &'a BTreeSet<String>,
    alive: BTreeSet<String>,
    temporaries: Vec<(i32, Type)>,
    trace: TraceMode,
    drop_ids: &'a BTreeMap<String, u32>,
}

/// Emit a standalone Linux x86-64 executable. Its scalar main result is the
/// process exit status (low eight bits). External declarations provide runtime I/O.
pub fn emit(program: &VerifiedProgram) -> Result<Vec<u8>> {
    if program.target != crate::compiler::TargetKind::X86_64 {
        return Err("native emission requires a program checked for X86_64".into());
    }
    emit_mode(program, TraceMode::Value)
}

fn emit_mode(program: &VerifiedProgram, trace: TraceMode) -> Result<Vec<u8>> {
    program::emit(program, trace)
}

#[cfg(test)]
mod tests;
