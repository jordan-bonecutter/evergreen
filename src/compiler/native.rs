//! Small Linux x86-64 backend. Source verification is required before emission.
//! This backend is trusted code, not a machine-checked compiler-correctness proof.

use crate::{
    compiler::layout,
    compiler::verify::VerifiedProgram,
    syntax::{Expr, Function, Kind, MachineInt, Statement, Struct, Type},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

mod elf;
mod program;
mod storage;

const STACK: usize = 65536;
const MAX_CODE: usize = 8 * 1024 * 1024;
const RECURSION_LIMIT: usize = 128;
const HEAP_LIMIT: u32 = 16 * 1024 * 1024;

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

// A stored read may avoid a value copy only when computing the path cannot
// change its contents. Calls are kept on the snapshot path, including helpers.
fn no_calls(e: &Expr) -> bool {
    match &e.kind {
        Kind::Call(..) => false,
        Kind::Unary(_, x) | Kind::Field(x, _) | Kind::FactAt(x, _) => no_calls(x),
        Kind::Binary(_, a, b) | Kind::Index(a, b) => no_calls(a) && no_calls(b),
        Kind::If(c, a, b) => no_calls(c) && no_calls(a) && no_calls(b),
        Kind::Array(items) => items.iter().all(no_calls),
        Kind::Record(_, fields) => fields.iter().all(|(_, e)| no_calls(e)),
        _ => true,
    }
}

fn stored(e: &Expr) -> bool {
    match &e.kind {
        Kind::Name(_) => true,
        Kind::Field(base, _) => stored(base),
        Kind::Index(base, index) => stored(base) && no_calls(index),
        Kind::Unary(op, x) if op == "*" => no_calls(x),
        _ => false,
    }
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

struct Emitter<'a> {
    code: &'a mut Vec<u8>,
    known: &'a BTreeMap<String, Compiled>,
    functions: &'a BTreeMap<String, &'a Function>,
    slots: BTreeMap<String, (i32, Type)>,
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

impl Emitter<'_> {
    fn allocate(&mut self, ty: &Type) -> Result<i32> {
        let object = layout::of(ty, self.structs)?;
        self.frame = self
            .frame
            .checked_add(object.size)
            .ok_or("native frame overflow")?
            .next_multiple_of(object.align);
        if self.frame + 16 > STACK {
            return Err("native frame exceeds private stack budget".into());
        }
        Ok(-i32::try_from(self.frame).map_err(|_| "native frame offset overflow")?)
    }

    fn frame_address(&mut self, offset: i32) {
        self.code.extend([0x48, 0x8d, 0x85]);
        self.code.extend(offset.to_le_bytes());
    }

    fn snapshot(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            let offset = self.allocate(ty)?;
            self.copy_frame(offset, ty)?;
            self.frame_address(offset);
        } else {
            self.load_scalar(ty)?;
        }
        Ok(())
    }

    fn slot(&mut self, name: &str, ty: Type) -> Result<()> {
        let offset = self.allocate(&ty)?;
        self.copy_frame(offset, &ty)?;
        self.alive.insert(name.into());
        if self.slots.insert(name.into(), (offset, ty)).is_some() {
            return Err("duplicate native binding".into());
        }
        Ok(())
    }

    fn load(&mut self, name: &str) -> Result<Type> {
        let (offset, ty) = self
            .slots
            .get(name)
            .cloned()
            .ok_or_else(|| format!("missing native binding {name}"))?;
        self.frame_address(offset);
        self.snapshot(&ty)?;
        Ok(ty)
    }

    fn has_drop(&self, ty: &Type) -> bool {
        match ty {
            Type::Plane(_) => true,
            Type::Named(name) => {
                self.drops.contains(name)
                    || self
                        .structs
                        .get(name)
                        .is_some_and(|s| s.runtime_fields().any(|(_, t)| self.has_drop(t)))
            }
            Type::Array(element, _) => self.has_drop(element),
            _ => false,
        }
    }

    fn push_value(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            let size = storage::argument_size(ty, self.structs)?;
            self.code.extend([0x48, 0x81, 0xec]);
            self.code.extend((size as u32).to_le_bytes());
            self.temporary += size;
            self.peak = self.peak.max(self.temporary);
            self.code.extend([0x48, 0x89, 0xe1]); // rcx = argument home
            self.copy_address(ty)?;
        } else {
            self.push();
        }
        Ok(())
    }

    fn invoke(&mut self, name: &str, argument_bytes: usize) -> Result<()> {
        let callee = self
            .known
            .get(name)
            .ok_or_else(|| format!("native callee {name} is recursive or has not been compiled"))?;
        self.peak = self.peak.max(self.temporary + 8 + callee.stack);
        self.code.push(0xe8);
        let displacement = self.code.len();
        self.code.extend([0; 4]);
        patch(self.code, displacement, callee.offset)?;
        if argument_bytes != 0 {
            self.code.extend([0x48, 0x81, 0xc4]);
            self.code.extend(
                u32::try_from(argument_bytes)
                    .map_err(|_| "native argument stack overflow")?
                    .to_le_bytes(),
            );
            self.temporary = self
                .temporary
                .checked_sub(argument_bytes)
                .ok_or("native argument stack underflow")?;
        }
        Ok(())
    }

    fn trace_drop(&mut self, name: &str) -> Result<()> {
        match self.trace {
            TraceMode::Value => {}
            TraceMode::Count => self.code.extend([0x49, 0xff, 0xc7]),
            TraceMode::Order => {
                self.code.extend([0x4d, 0x69, 0xff]);
                self.code.extend(167u32.to_le_bytes());
                self.code.extend([0x49, 0x81, 0xc7]);
                self.code.extend(
                    self.drop_ids
                        .get(name)
                        .ok_or("missing native trace type")?
                        .to_le_bytes(),
                );
            }
        }
        Ok(())
    }

    fn drop_fields(&mut self, ty: &Type, offset: i32) -> Result<()> {
        match ty {
            Type::Named(name) => {
                let fields = self
                    .structs
                    .get(name)
                    .ok_or("unknown native cleanup type")?
                    .runtime_fields()
                    .cloned()
                    .collect::<Vec<_>>();
                let object = layout::of(ty, self.structs)?;
                for (name, ty) in fields {
                    self.drop_frame(&ty, offset + object.fields[&name].offset as i32)?;
                }
            }
            Type::Array(element, count) if self.has_drop(element) => {
                let bytes = layout::of(element, self.structs)?.size;
                for index in 0..layout::array_length(count)? {
                    self.drop_frame(element, offset + (index * bytes) as i32)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn drop_frame(&mut self, ty: &Type, offset: i32) -> Result<()> {
        if !self.has_drop(ty) {
            return Ok(());
        }
        if let Type::Plane(payload) = ty {
            self.frame_address(offset);
            self.code.extend([0x48, 0x8b, 0x00]);
            self.snapshot(payload)?;
            self.drop_value(payload)?;
            self.code.extend([0x48, 0x8b, 0xbd]); // rdi = allocation address
            self.code.extend(offset.to_le_bytes());
            let size = layout::of(payload, self.structs)?.size as u32;
            self.code.push(0xbe); // esi = byte length
            self.code.extend(size.to_le_bytes());
            self.code.extend([0xb8, 11, 0, 0, 0, 0x0f, 0x05]); // munmap
            self.code.extend([0x48, 0x85, 0xc0]);
            self.heap_guard(0x79); // jns success
            self.code.extend([0x49, 0x81, 0xed]); // sub r13, mapped pages
            self.code.extend(size.next_multiple_of(4096).to_le_bytes());
            return Ok(());
        }
        if let Type::Named(name) = ty {
            if self.drops.contains(name) {
                self.trace_drop(name)?;
                self.frame_address(offset);
                self.push_value(ty)?;
                return self.invoke(
                    &format!("evg_drop_{name}"),
                    storage::argument_size(ty, self.structs)?,
                );
            }
        }
        self.drop_fields(ty, offset)
    }

    fn drop_value(&mut self, ty: &Type) -> Result<()> {
        if self.has_drop(ty) {
            let home = self.allocate(ty)?;
            self.copy_frame(home, ty)?;
            self.drop_frame(ty, home)?;
        }
        Ok(())
    }

    fn finish_temporaries(&mut self, start: usize) -> Result<()> {
        for (offset, ty) in self.temporaries.split_off(start).into_iter().rev() {
            self.drop_frame(&ty, offset)?;
        }
        Ok(())
    }

    fn scoped_expr(&mut self, e: &Expr, expected: Option<&Type>) -> Result<Type> {
        let start = self.temporaries.len();
        let ty = self.expr(e, expected)?;
        if self.temporaries.len() != start {
            let home = self.allocate(&ty)?;
            self.copy_frame(home, &ty)?;
            self.finish_temporaries(start)?;
            self.frame_address(home);
            if !layout::aggregate(&ty) {
                self.load_scalar(&ty)?;
            }
        }
        Ok(ty)
    }

    fn storage_value(&mut self, e: &Expr) -> Result<Type> {
        match &e.kind {
            Kind::Name(name) => self.load(name),
            Kind::Field(base, name) => {
                let ty = self.storage_value(base)?;
                let field = self.field(&ty, name)?;
                self.add_offset(field.offset);
                if !layout::aggregate(&field.ty) {
                    self.load_scalar(&field.ty)?;
                }
                Ok(field.ty)
            }
            Kind::Index(base, index) => {
                let ty = self.index_address(base, index, ReadMode::Storage)?;
                if !layout::aggregate(&ty) {
                    self.load_scalar(&ty)?;
                }
                Ok(ty)
            }
            Kind::Unary(op, _) if op == "*" => {
                let ty = self.address(e)?;
                self.snapshot(&ty)?;
                Ok(ty)
            }
            _ => {
                let ty = self.expr(e, None)?;
                if self.has_drop(&ty) {
                    let home = self.allocate(&ty)?;
                    self.copy_frame(home, &ty)?;
                    self.temporaries.push((home, ty.clone()));
                    self.frame_address(home);
                    if !layout::aggregate(&ty) {
                        self.load_scalar(&ty)?;
                    }
                }
                Ok(ty)
            }
        }
    }

    fn field(&self, ty: &Type, name: &str) -> Result<layout::Field> {
        layout::of(ty, self.structs)?
            .fields
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown native field {name}"))
    }

    fn add_offset(&mut self, offset: usize) {
        if offset != 0 {
            self.code.extend([0x48, 0x05]);
            self.code.extend((offset as u32).to_le_bytes());
        }
    }

    fn compatible(a: &Type, b: &Type) -> Result<bool> {
        if a == b {
            return Ok(true);
        }
        match (a, b) {
            // Source verification already checked pointee compatibility. The
            // native reference ABI is one address even for dependent pointees.
            (Type::Ref(_), Type::Ref(_)) => Ok(true),
            (Type::Array(a, al), Type::Array(b, bl)) => {
                Ok(Self::compatible(a, b)?
                    && layout::array_length(al)? == layout::array_length(bl)?)
            }
            _ => Ok(false),
        }
    }

    fn index_address(&mut self, base: &Expr, index: &Expr, mode: ReadMode) -> Result<Type> {
        let ty = match mode {
            ReadMode::Place => self.address(base)?,
            ReadMode::Value => self.expr(base, None)?,
            ReadMode::Storage => self.storage_value(base)?,
        };
        let Type::Array(element, _) = ty else {
            return Err("native index requires an array".into());
        };
        let bytes = layout::of(&element, self.structs)?.size;
        self.push();
        let index_ty = self.expr(index, None)?;
        if !matches!(index_ty, Type::Machine(_)) {
            return Err("native index requires a machine integer".into());
        }
        self.code.extend([0x48, 0x69, 0xc0]);
        self.code.extend((bytes as u32).to_le_bytes());
        self.pop();
        self.code.extend([0x48, 0x01, 0xc8]);
        Ok(*element)
    }

    fn immediate(&mut self, value: u64) {
        self.code.extend([0x48, 0xb8]);
        self.code.extend(value.to_le_bytes());
    }

    fn push(&mut self) {
        self.code.push(0x50);
        self.temporary += 8;
        self.peak = self.peak.max(self.temporary);
    }

    fn pop(&mut self) {
        self.code.push(0x59);
        self.temporary -= 8;
    }

    fn jump(&mut self, conditional: bool) -> usize {
        if conditional {
            self.code.extend([0x0f, 0x84]);
        } else {
            self.code.push(0xe9);
        }
        let position = self.code.len();
        self.code.extend([0; 4]);
        position
    }

    fn hint(&self, e: &Expr) -> Option<Type> {
        match &e.kind {
            Kind::Name(n) => self.slots.get(n).map(|(_, t)| t.clone()),
            Kind::Record(name, _) => Some(Type::Named(name.clone())),
            Kind::Field(base, name) => self.field(&self.hint(base)?, name).ok().map(|f| f.ty),
            Kind::Index(base, _) => match self.hint(base)? {
                Type::Array(element, _) => Some(*element),
                _ => None,
            },
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Constant(t, _) => Some(Type::Machine(*t)),
            Kind::Unary(op, _) if op == "!" => Some(Type::Bool),
            Kind::Unary(op, x) if op == "&" => self.hint(x).map(|t| Type::Ref(Box::new(t))),
            Kind::Unary(op, x) if op == "*" => match self.hint(x)? {
                Type::Ref(inner) | Type::Plane(inner) => Some(*inner),
                _ => None,
            },
            Kind::Unary(_, x) => self.hint(x),
            Kind::Binary(op, _, _)
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "=>"
                ) =>
            {
                Some(Type::Bool)
            }
            Kind::Binary(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::Call(n, args) if n == "alloc" && args.len() == 1 => {
                self.hint(&args[0]).map(|t| Type::Plane(Box::new(t)))
            }
            Kind::Call(n, _) => self.functions.get(n).map(|f| f.ret.clone()),
            Kind::If(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            _ => None,
        }
    }

    fn address(&mut self, e: &Expr) -> Result<Type> {
        match &e.kind {
            Kind::Field(base, name) => {
                let base = self.address(base)?;
                let field = self.field(&base, name)?;
                self.add_offset(field.offset);
                Ok(field.ty)
            }
            Kind::Index(base, index) => self.index_address(base, index, ReadMode::Place),
            Kind::Name(name) => {
                let (offset, ty) = self.slots.get(name).ok_or("unknown native place")?;
                self.code.extend([0x48, 0x8d, 0x85]);
                self.code.extend(offset.to_le_bytes());
                Ok(ty.clone())
            }
            Kind::Unary(op, x) if op == "*" => match self.storage_value(x)? {
                Type::Ref(inner) | Type::Plane(inner) => Ok(*inner),
                _ => Err("native place dereference requires a reference".into()),
            },
            _ => Err("native references require stored places".into()),
        }
    }

    fn expr(&mut self, e: &Expr, expected: Option<&Type>) -> Result<Type> {
        let ty = match &e.kind {
            Kind::Number(n) => {
                self.immediate(*n as u64);
                expected.cloned().unwrap_or_else(machine)
            }
            Kind::Constant(t, n) => {
                self.immediate(*n as u64);
                Type::Machine(*t)
            }
            Kind::Bool(b) => {
                self.immediate(u64::from(*b));
                Type::Bool
            }
            Kind::Unit => {
                self.immediate(0);
                Type::Unit
            }
            Kind::Name(n) => {
                let ty = self.load(n)?;
                if crate::shared::ownership::is_affine(&ty, self.structs, self.drops) {
                    self.alive.remove(n);
                }
                ty
            }
            Kind::Record(name, entries) => {
                let ty = Type::Named(name.clone());
                let object = self.allocate(&ty)?;
                if self.structs[name].runtime_fields().next().is_none() {
                    self.immediate(0);
                    self.copy_frame(object, &Type::Unit)?;
                }
                for (field, expression) in entries {
                    if self.structs[name].ideal_fields.contains(field) {
                        continue;
                    }
                    let field = self.field(&ty, field)?;
                    self.expr(expression, Some(&field.ty))?;
                    self.copy_frame(object + field.offset as i32, &field.ty)?;
                }
                self.frame_address(object);
                ty
            }
            Kind::Field(..) => self.storage_value(e)?,
            Kind::Array(items) => {
                let ty = if let Some(Type::Array(..)) = expected {
                    expected.unwrap().clone()
                } else {
                    let first = items.first().ok_or("native empty array needs a type")?;
                    Type::Array(
                        Box::new(self.hint(first).unwrap_or_else(machine)),
                        Box::new(Expr {
                            kind: Kind::Number(items.len() as i128),
                            line: e.line,
                        }),
                    )
                };
                let Type::Array(element, count) = &ty else {
                    unreachable!()
                };
                if layout::array_length(count)? != items.len() {
                    return Err("native array literal length mismatch".into());
                }
                let bytes = layout::of(element, self.structs)?.size;
                let object = self.allocate(&ty)?;
                if items.is_empty() {
                    self.immediate(0);
                    self.copy_frame(object, &Type::Unit)?;
                }
                for (index, item) in items.iter().enumerate() {
                    self.expr(item, Some(element))?;
                    self.copy_frame(object + (index * bytes) as i32, element)?;
                }
                self.frame_address(object);
                ty
            }
            Kind::Index(base, index) => {
                let borrowed = stored(base) && no_calls(index);
                let ty = self.index_address(
                    base,
                    index,
                    if borrowed {
                        ReadMode::Place
                    } else {
                        ReadMode::Value
                    },
                )?;
                if layout::aggregate(&ty) && borrowed {
                    self.snapshot(&ty)?;
                } else if !layout::aggregate(&ty) {
                    self.load_scalar(&ty)?;
                }
                ty
            }
            Kind::Unary(op, x) if op == "&" => Type::Ref(Box::new(self.address(x)?)),
            Kind::Unary(op, x) if op == "*" => {
                let inner = match self.storage_value(x)? {
                    Type::Ref(inner) | Type::Plane(inner) => inner,
                    _ => {
                        return Err("native dereference requires a reference or owned plane".into())
                    }
                };
                self.snapshot(&inner)?;
                *inner
            }
            Kind::Unary(op, x) if op == "!" => {
                self.expr(x, Some(&Type::Bool))?;
                self.code.extend([0x83, 0xf0, 1]);
                Type::Bool
            }
            Kind::Unary(op, x) if op == "-" => {
                let ty = expected
                    .cloned()
                    .or_else(|| self.hint(x))
                    .unwrap_or_else(machine);
                if !matches!(ty, Type::Machine(_)) {
                    return Err("native negation requires a machine integer".into());
                }
                self.expr(x, Some(&ty))?;
                self.code.extend([0x48, 0xf7, 0xd8]);
                ty
            }
            Kind::Binary(op, a, b) => {
                let arithmetic = matches!(op.as_str(), "+" | "-" | "*");
                let logical = matches!(op.as_str(), "&&" | "||" | "=>");
                let operand = if logical {
                    Type::Bool
                } else {
                    (if arithmetic { expected.cloned() } else { None })
                        .or_else(|| self.hint(a))
                        .or_else(|| self.hint(b))
                        .unwrap_or_else(machine)
                };
                self.expr(a, Some(&operand))?;
                self.push();
                self.expr(b, Some(&operand))?;
                self.pop();
                match op.as_str() {
                    "+" => self.code.extend([0x48, 0x01, 0xc8]),
                    "-" => self.code.extend([0x48, 0x29, 0xc1, 0x48, 0x89, 0xc8]),
                    "*" => self.code.extend([0x48, 0x0f, 0xaf, 0xc1]),
                    "&&" => self.code.extend([0x48, 0x21, 0xc8]),
                    "||" => self.code.extend([0x48, 0x09, 0xc8]),
                    "=>" => self.code.extend([0x48, 0x83, 0xf1, 1, 0x48, 0x09, 0xc8]),
                    _ => {
                        self.code.extend([0x48, 0x39, 0xc1]);
                        let signed =
                            matches!(operand, Type::Machine(MachineInt { signed: true, .. }));
                        let condition = match op.as_str() {
                            "==" => 0x94,
                            "!=" => 0x95,
                            "<" => {
                                if signed {
                                    0x9c
                                } else {
                                    0x92
                                }
                            }
                            "<=" => {
                                if signed {
                                    0x9e
                                } else {
                                    0x96
                                }
                            }
                            ">" => {
                                if signed {
                                    0x9f
                                } else {
                                    0x97
                                }
                            }
                            ">=" => {
                                if signed {
                                    0x9d
                                } else {
                                    0x93
                                }
                            }
                            _ => return Err("unsupported native operator".into()),
                        };
                        self.code.extend([0x0f, condition, 0xc0, 0x0f, 0xb6, 0xc0]);
                    }
                }
                if arithmetic {
                    operand
                } else {
                    Type::Bool
                }
            }
            Kind::If(condition, yes, no) => {
                self.scoped_expr(condition, Some(&Type::Bool))?;
                let base_alive = self.alive.clone();
                self.code.extend([0x48, 0x85, 0xc0]);
                let alternative = self.jump(true);
                let ty = self.scoped_expr(yes, expected)?;
                let yes_alive = self.alive.clone();
                let end = self.jump(false);
                let target = self.code.len();
                patch(self.code, alternative, target)?;
                self.alive = base_alive;
                self.scoped_expr(no, Some(&ty))?;
                if self.alive != yes_alive {
                    return Err("native conditional ownership states differ".into());
                }
                let target = self.code.len();
                patch(self.code, end, target)?;
                ty
            }
            Kind::Call(name, args) if matches!(name.as_str(), "move" | "drop") => {
                if args.len() != 1 {
                    return Err("invalid native move/drop".into());
                }
                let ty = self.expr(&args[0], None)?;
                if let Kind::Name(binding) = &args[0].kind {
                    self.alive.remove(binding);
                }
                if name == "drop" {
                    self.drop_value(&ty)?;
                    self.immediate(0);
                    Type::Unit
                } else {
                    ty
                }
            }
            Kind::Call(name, args) if name == "alloc" => {
                let hint = match expected {
                    Some(Type::Plane(inner)) => Some(inner.as_ref()),
                    _ => None,
                };
                let payload = self.expr(&args[0], hint)?;
                let saved = self.allocate(&payload)?;
                self.copy_frame(saved, &payload)?;
                let size = layout::of(&payload, self.structs)?.size as u32;
                self.code.extend([0x49, 0x81, 0xc5]); // add r13, mapped bytes
                self.code.extend(size.next_multiple_of(4096).to_le_bytes());
                self.code.extend([0x49, 0x81, 0xfd]); // cmp r13, heap budget
                self.code.extend(HEAP_LIMIT.to_le_bytes());
                self.heap_guard(0x76); // jbe success
                self.code.extend([0x31, 0xff]); // rdi = null address hint
                self.code.push(0xbe);
                self.code.extend(size.to_le_bytes());
                self.code.extend([0xba, 3, 0, 0, 0]); // PROT_READ | PROT_WRITE
                self.code.extend([0x41, 0xba, 0x22, 0, 0, 0]); // MAP_PRIVATE | MAP_ANONYMOUS
                self.code.extend([0x49, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff]); // fd = -1
                self.code.extend([0x45, 0x31, 0xc9]); // offset = 0
                self.code.extend([0xb8, 9, 0, 0, 0, 0x0f, 0x05]); // mmap
                self.code.extend([0x48, 0x85, 0xc0]);
                self.heap_guard(0x79); // jns success
                let home = self.allocate(&Type::Plane(Box::new(payload.clone())))?;
                self.copy_frame(home, &Type::Ref(Box::new(payload.clone())))?;
                self.code.extend([0x48, 0x89, 0xc1]); // destination rcx
                self.frame_address(saved);
                if !layout::aggregate(&payload) {
                    self.load_scalar(&payload)?;
                }
                self.copy_address(&payload)?;
                self.frame_address(home);
                self.code.extend([0x48, 0x8b, 0x00]);
                Type::Plane(Box::new(payload))
            }
            Kind::Call(name, args) => {
                let function = self.functions.get(name).ok_or("unknown native callee")?;
                if function.params.len() != args.len() {
                    return Err("native argument count mismatch".into());
                }
                let saved_temporary = self.temporary;
                for ((parameter, ty), arg) in function.params.iter().zip(args) {
                    if function.ideal_params.contains(parameter) {
                        continue;
                    }
                    self.expr(arg, Some(ty))?;
                    self.push_value(ty)?;
                }
                if layout::aggregate(&function.ret) {
                    let output = self.allocate(&function.ret)?;
                    self.frame_address(output);
                    self.push();
                }
                self.invoke(name, self.temporary - saved_temporary)?;
                function.ret.clone()
            }
            _ => {
                return Err(format!(
                    "line {}: this expression is not supported by the scalar native backend",
                    e.line
                ))
            }
        };
        layout::of(&ty, self.structs)?;
        if let Some(expected) = expected {
            if !Self::compatible(expected, &ty)? {
                return Err(format!("line {}: native type mismatch", e.line));
            }
        }
        if self.code.len() > MAX_CODE {
            return Err("native code exceeds 8 MiB limit".into());
        }
        Ok(ty)
    }

    fn statement(&mut self, statement: &Statement) -> Result<()> {
        let start = self.temporaries.len();
        self.statement_inner(statement)?;
        self.finish_temporaries(start)
    }

    fn statement_inner(&mut self, statement: &Statement) -> Result<()> {
        match statement {
            Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => Ok(()),
            Statement::Let { name, ty, value } => {
                let ty = self.expr(value, ty.as_ref())?;
                self.slot(name, ty)
            }
            Statement::Assign { target, value } => {
                fn root(e: &Expr) -> Option<&str> {
                    match &e.kind {
                        Kind::Name(n) => Some(n),
                        Kind::Field(base, _) | Kind::Index(base, _) => root(base),
                        _ => None,
                    }
                }
                let owner = root(target).map(str::to_owned);
                let ty = self.address(target)?;
                let pointer_ty = Type::Ref(Box::new(ty.clone()));
                let pointer = self.allocate(&pointer_ty)?;
                self.copy_frame(pointer, &pointer_ty)?;
                let old = if self.has_drop(&ty)
                    && owner.as_ref().is_some_and(|n| self.alive.contains(n))
                {
                    let home = self.allocate(&ty)?;
                    if !layout::aggregate(&ty) {
                        self.load_scalar(&ty)?;
                    }
                    self.copy_frame(home, &ty)?;
                    Some(home)
                } else {
                    None
                };
                self.expr(value, Some(&ty))?;
                if self.has_drop(&ty) {
                    let new_value = self.allocate(&ty)?;
                    self.copy_frame(new_value, &ty)?;
                    if let Some(old) = old {
                        if owner.as_ref().is_some_and(|n| self.alive.contains(n)) {
                            self.drop_frame(&ty, old)?;
                        }
                    }
                    self.frame_address(new_value);
                    if !layout::aggregate(&ty) {
                        self.load_scalar(&ty)?;
                    }
                }
                self.code.extend([0x48, 0x8b, 0x8d]);
                self.code.extend(pointer.to_le_bytes());
                self.copy_address(&ty)?;
                if let Kind::Name(name) = &target.kind {
                    self.alive.insert(name.clone());
                }
                Ok(())
            }
            Statement::Destructure {
                record,
                fields,
                value,
            } => {
                let ty = Type::Named(record.clone());
                self.expr(value, Some(&ty))?;
                self.code.extend([0x48, 0x89, 0xc6]);
                for (field, name) in fields {
                    if self.structs[record].ideal_fields.contains(field) {
                        continue;
                    }
                    let field = self.field(&ty, field)?;
                    self.code.extend([0x48, 0x8d, 0x86]);
                    self.code.extend((field.offset as i32).to_le_bytes());
                    if !layout::aggregate(&field.ty) {
                        self.load_scalar(&field.ty)?;
                    }
                    self.slot(name, field.ty)?;
                }
                Ok(())
            }
            Statement::Update { body, .. } => {
                let saved = self.slots.clone();
                let saved_alive = self.alive.clone();
                for statement in body {
                    self.statement(statement)?;
                }
                self.slots = saved;
                self.alive = saved_alive;
                Ok(())
            }
            Statement::Effect(e) => {
                let ty = self.expr(e, None)?;
                self.drop_value(&ty)
            }
        }
    }

    fn heap_guard(&mut self, success: u8) {
        self.code.extend([success, 14]);
        self.code.extend([
            0xbf, 126, 0, 0, 0, 0xb8, 60, 0, 0, 0, 0x0f, 0x05, 0x0f, 0x0b,
        ]);
    }
}

fn compilation_order(program: &VerifiedProgram) -> Result<Vec<&Function>> {
    fn visit<'a>(
        ty: &Type,
        program: &'a VerifiedProgram,
        methods: &BTreeMap<&str, &'a Function>,
        seen: &mut BTreeSet<String>,
        output: &mut Vec<&'a Function>,
    ) -> Result<()> {
        match ty {
            Type::Named(name) if seen.insert(name.clone()) => {
                for (_, field) in program
                    .structs
                    .get(name)
                    .ok_or("unknown native cleanup dependency")?
                    .runtime_fields()
                {
                    visit(field, program, methods, seen, output)?;
                }
                if let Some(method) = methods.get(name.as_str()) {
                    output.push(*method);
                }
            }
            Type::Array(element, _) | Type::Plane(element) => {
                visit(element, program, methods, seen, output)?
            }
            _ => {}
        }
        Ok(())
    }
    let methods = program
        .functions
        .iter()
        .filter_map(|f| f.drop_target.as_deref().map(|name| (name, f)))
        .collect::<BTreeMap<_, _>>();
    // Ownership-free helpers cannot depend on cleanup methods. Compile them
    // first so destructors can call their checked scalar implementations.
    let mut ordered = program
        .functions
        .iter()
        .filter(|f| program.cleanup_helpers.contains(&f.name))
        .collect::<Vec<_>>();
    let mut seen = BTreeSet::new();
    for name in &program.drops {
        visit(
            &Type::Named(name.clone()),
            program,
            &methods,
            &mut seen,
            &mut ordered,
        )?;
    }
    ordered.extend(
        program
            .functions
            .iter()
            .filter(|f| f.drop_target.is_none() && !program.cleanup_helpers.contains(&f.name)),
    );
    Ok(ordered)
}

/// Emit a standalone Linux x86-64 executable. Its scalar main result is the
/// process exit status (low eight bits). It performs no runtime I/O.
pub fn emit(program: &VerifiedProgram) -> Result<Vec<u8>> {
    emit_mode(program, TraceMode::Value)
}

fn emit_mode(program: &VerifiedProgram, trace: TraceMode) -> Result<Vec<u8>> {
    program::emit(program, trace)
}

#[cfg(test)]
mod tests;
