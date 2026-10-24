//! Small Linux x86-64 backend. Source verification is required before emission.
//! This backend is trusted code, not a machine-checked compiler-correctness proof.
use crate::{
    layout,
    syntax::{Expr, Function, Kind, MachineInt, Statement, Struct, Type},
    verify::VerifiedProgram,
};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, String>;
const BASE: u64 = 0x400000;
const HEADER: usize = 64 + 2 * 56;
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
        self.frame = self
            .frame
            .checked_add(layout::of(ty, self.structs)?.size)
            .ok_or("native frame overflow")?;
        if self.frame + 16 > STACK {
            return Err("native frame exceeds private stack budget".into());
        }
        Ok(-i32::try_from(self.frame).map_err(|_| "native frame offset overflow")?)
    }
    fn frame_address(&mut self, offset: i32) {
        self.code.extend([0x48, 0x8d, 0x85]);
        self.code.extend(offset.to_le_bytes());
    }
    fn copy_frame(&mut self, offset: i32, ty: &Type) -> Result<()> {
        if !layout::aggregate(ty) {
            self.code.extend([0x48, 0x89, 0x85]);
            self.code.extend(offset.to_le_bytes());
        } else {
            self.code.extend([0x48, 0x89, 0xc2]); // rdx = source
            for index in (0..layout::of(ty, self.structs)?.size).step_by(8) {
                self.code.extend([0x48, 0x8b, 0x82]);
                self.code.extend((index as i32).to_le_bytes());
                self.code.extend([0x48, 0x89, 0x85]);
                self.code.extend((offset + index as i32).to_le_bytes());
            }
        }
        Ok(())
    }
    fn copy_address(&mut self, ty: &Type) -> Result<()> {
        // Destination is rcx. Aggregate rax values are snapshot addresses.
        if !layout::aggregate(ty) {
            self.code.extend([0x48, 0x89, 0x01]);
        } else {
            self.code.extend([0x48, 0x89, 0xc2]);
            for index in (0..layout::of(ty, self.structs)?.size).step_by(8) {
                self.code.extend([0x48, 0x8b, 0x82]);
                self.code.extend((index as i32).to_le_bytes());
                self.code.extend([0x48, 0x89, 0x81]);
                self.code.extend((index as i32).to_le_bytes());
            }
        }
        Ok(())
    }
    fn snapshot(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            let offset = self.allocate(ty)?;
            self.copy_frame(offset, ty)?;
            self.frame_address(offset);
        } else {
            self.code.extend([0x48, 0x8b, 0x00]);
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
            Type::Named(name) => {
                self.drops.contains(name)
                    || self
                        .structs
                        .get(name)
                        .is_some_and(|s| s.fields.iter().any(|(_, t)| self.has_drop(t)))
            }
            Type::Array(element, _) => self.has_drop(element),
            _ => false,
        }
    }
    fn push_value(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            self.code.extend([0x48, 0x89, 0xc2]);
            for offset in (0..layout::of(ty, self.structs)?.size).step_by(8).rev() {
                self.code.extend([0x48, 0x8b, 0x82]);
                self.code.extend((offset as i32).to_le_bytes());
                self.push();
            }
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
                    .fields
                    .clone();
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
        if let Type::Named(name) = ty {
            if self.drops.contains(name) {
                self.trace_drop(name)?;
                self.frame_address(offset);
                self.push_value(ty)?;
                return self.invoke(
                    &format!("evg_drop_{name}"),
                    layout::of(ty, self.structs)?.size,
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
                self.code.extend([0x48, 0x8b, 0x00]);
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
                    self.code.extend([0x48, 0x8b, 0x00]);
                }
                Ok(field.ty)
            }
            Kind::Index(base, index) => {
                let ty = self.index_address(base, index, ReadMode::Storage)?;
                if !layout::aggregate(&ty) {
                    self.code.extend([0x48, 0x8b, 0x00]);
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
                Type::Ref(inner) => Some(*inner),
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
            Kind::Unary(op, x) if op == "*" => match self.expr(x, None)? {
                Type::Ref(inner) => Ok(*inner),
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
                if crate::verify::is_affine(&ty, self.structs, self.drops) {
                    self.alive.remove(n);
                }
                ty
            }
            Kind::Record(name, entries) => {
                let ty = Type::Named(name.clone());
                let object = self.allocate(&ty)?;
                if entries.is_empty() {
                    self.immediate(0);
                    self.copy_frame(object, &Type::Unit)?;
                }
                for (field, expression) in entries {
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
                    self.code.extend([0x48, 0x8b, 0x00]);
                }
                ty
            }
            Kind::Unary(op, x) if op == "&" => Type::Ref(Box::new(self.address(x)?)),
            Kind::Unary(op, x) if op == "*" => {
                let Type::Ref(inner) = self.expr(x, None)? else {
                    return Err("native dereference requires a reference".into());
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
                    let field = self.field(&ty, field)?;
                    self.code.extend([0x48, 0x8d, 0x86]);
                    self.code.extend((field.offset as i32).to_le_bytes());
                    if !layout::aggregate(&field.ty) {
                        self.code.extend([0x48, 0x8b, 0x00]);
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
                for (_, field) in &program
                    .structs
                    .get(name)
                    .ok_or("unknown native cleanup dependency")?
                    .fields
                {
                    visit(field, program, methods, seen, output)?;
                }
                if let Some(method) = methods.get(name.as_str()) {
                    output.push(*method);
                }
            }
            Type::Array(element, _) => visit(element, program, methods, seen, output)?,
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
    program.check_entry()?;
    let drop_ids = program
        .drops
        .iter()
        .enumerate()
        .map(|(index, name)| {
            Ok((
                name.clone(),
                u32::try_from(index + 1).map_err(|_| "native trace type count overflow")?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>>>()?;
    let functions = program
        .functions
        .iter()
        .map(|f| (f.name.clone(), f))
        .collect::<BTreeMap<_, _>>();
    let mut known = BTreeMap::new();
    let mut code = vec![0x48, 0xbc];
    code.extend([0; 8]); // mov rsp, private stack end
    code.extend([0x45, 0x31, 0xf6]); // reserved r14: recursive activation count
    if trace != TraceMode::Value {
        code.extend([0x4d, 0x31, 0xff]);
    }
    code.push(0xe8);
    let entry_call = code.len();
    code.extend([0; 4]);
    code.extend(if trace == TraceMode::Value {
        [0x48, 0x89, 0xc7]
    } else {
        [0x4c, 0x89, 0xff]
    });
    code.extend([0xb8, 60, 0, 0, 0, 0x0f, 0x05, 0x0f, 0x0b]);
    for function in compilation_order(program)? {
        if function.ideal {
            continue;
        }
        if function.name == "main" {
            scalar(&function.ret)?;
        }
        layout::of(&function.ret, &program.structs)?;
        let output_pointer = usize::from(layout::aggregate(&function.ret)) * 8;
        let params = function
            .params
            .iter()
            .filter(|(n, _)| !function.ideal_params.contains(n))
            .collect::<Vec<_>>();
        let sizes = params
            .iter()
            .map(|(_, ty)| layout::of(ty, &program.structs).map(|l| l.size))
            .collect::<Result<Vec<_>>>()?;
        let offset = code.len();
        let recursive = crate::effects::recursive(function);
        if recursive {
            // The source proves termination; this guard enforces the bootstrap
            // execution budget before another frame can consume stack storage.
            code.extend([0x49, 0x81, 0xfe]); // cmp r14, limit
            code.extend((RECURSION_LIMIT as u32).to_le_bytes());
            code.extend([0x72, 14]); // jb over exit(125), ud2
            code.extend([
                0xbf, 125, 0, 0, 0, 0xb8, 60, 0, 0, 0, 0x0f, 0x05, 0x0f, 0x0b,
            ]);
            code.extend([0x49, 0xff, 0xc6]); // inc r14
                                             // A self edge contributes no callee estimate here. The entire local
                                             // frame and maximum outgoing call cost are multiplied below.
            known.insert(function.name.clone(), Compiled { offset, stack: 0 });
        }
        code.extend([0x55, 0x48, 0x89, 0xe5, 0x48, 0x81, 0xec]);
        let frame_fixup = code.len();
        code.extend([0; 4]);
        let mut emitter = Emitter {
            code: &mut code,
            known: &known,
            functions: &functions,
            slots: BTreeMap::new(),
            frame: 0,
            structs: &program.structs,
            temporary: 0,
            peak: 0,
            drops: &program.drops,
            alive: BTreeSet::new(),
            temporaries: Vec::new(),
            trace,
            drop_ids: &drop_ids,
        };
        let mut incoming_offsets = vec![0usize; sizes.len()];
        let mut incoming_bytes = 16 + output_pointer;
        for index in (0..sizes.len()).rev() {
            incoming_offsets[index] = incoming_bytes;
            incoming_bytes = incoming_bytes
                .checked_add(sizes[index])
                .ok_or("native parameter layout overflow")?;
        }
        for (index, (name, ty)) in params.iter().enumerate() {
            emitter.code.extend(if layout::aggregate(ty) {
                [0x48, 0x8d, 0x85]
            } else {
                [0x48, 0x8b, 0x85]
            });
            let incoming = u32::try_from(incoming_offsets[index])
                .map_err(|_| "native parameter offset overflow")?;
            emitter.code.extend(incoming.to_le_bytes());
            emitter.slot(name, ty.clone())?;
        }
        for statement in &function.body {
            emitter.statement(statement)?;
        }
        emitter.scoped_expr(&function.result, Some(&function.ret))?;
        let saved_result = if program.drops.is_empty() {
            None
        } else {
            let home = emitter.allocate(&function.ret)?;
            emitter.copy_frame(home, &function.ret)?;
            Some(home)
        };
        let names = params
            .iter()
            .map(|(n, _)| n.as_str())
            .chain(function.body.iter().flat_map(Statement::runtime_bindings))
            .collect::<Vec<_>>();
        for name in names.into_iter().rev() {
            if emitter.alive.remove(name) {
                let (offset, ty) = emitter
                    .slots
                    .get(name)
                    .cloned()
                    .ok_or("missing native cleanup binding")?;
                if name == "self" && function.drop_target.is_some() {
                    emitter.drop_fields(&ty, offset)?;
                } else {
                    emitter.drop_frame(&ty, offset)?;
                }
            }
        }
        if let Some(home) = saved_result {
            emitter.frame_address(home);
            if !layout::aggregate(&function.ret) {
                emitter.code.extend([0x48, 0x8b, 0x00]);
            }
        }
        if output_pointer != 0 {
            emitter.code.extend([0x48, 0x8b, 0x8d]);
            emitter.code.extend(16i32.to_le_bytes());
            emitter.copy_address(&function.ret)?;
            emitter.code.extend([0x48, 0x89, 0xc8]);
        }
        if emitter.temporary != 0 {
            return Err("unbalanced native expression stack".into());
        }
        let frame = emitter.frame;
        emitter.code[frame_fixup..frame_fixup + 4].copy_from_slice(&(frame as u32).to_le_bytes());
        let stack = (8 + frame + emitter.peak)
            .checked_mul(if recursive { RECURSION_LIMIT } else { 1 })
            .ok_or("native recursion stack estimate overflow")?;
        if stack + 8 > STACK {
            return Err("native call tree exceeds 64 KiB private stack budget".into());
        }
        if recursive {
            emitter.code.extend([0x49, 0xff, 0xce]); // dec r14
        }
        emitter.code.extend([0x48, 0x89, 0xec, 0x5d, 0xc3]);
        if emitter.code.len() > MAX_CODE {
            return Err("native code exceeds 8 MiB limit".into());
        }
        known.insert(function.name.clone(), Compiled { offset, stack });
    }
    let main = known.get("main").ok_or("missing native main")?;
    patch(&mut code, entry_call, main.offset)?;
    let text_size = HEADER + code.len();
    let data_offset = (text_size + 4095) & !4095;
    let stack_end = BASE + data_offset as u64 + STACK as u64;
    code[2..10].copy_from_slice(&stack_end.to_le_bytes());
    let mut output = vec![0u8; HEADER];
    output[..16].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    output[16..18].copy_from_slice(&2u16.to_le_bytes());
    output[18..20].copy_from_slice(&62u16.to_le_bytes());
    output[20..24].copy_from_slice(&1u32.to_le_bytes());
    output[24..32].copy_from_slice(&(BASE + HEADER as u64).to_le_bytes());
    output[32..40].copy_from_slice(&64u64.to_le_bytes());
    output[52..54].copy_from_slice(&64u16.to_le_bytes());
    output[54..56].copy_from_slice(&56u16.to_le_bytes());
    output[56..58].copy_from_slice(&2u16.to_le_bytes());
    for (index, flags, file_offset, address, file_size, memory_size) in [
        (0usize, 5u32, 0usize, BASE, text_size, text_size),
        (1, 6, data_offset, BASE + data_offset as u64, 1, STACK),
    ] {
        let header = &mut output[64 + index * 56..64 + (index + 1) * 56];
        header[..4].copy_from_slice(&1u32.to_le_bytes());
        header[4..8].copy_from_slice(&flags.to_le_bytes());
        for (offset, value) in [
            (8, file_offset as u64),
            (16, address),
            (24, address),
            (32, file_size as u64),
            (40, memory_size as u64),
            (48, 4096),
        ] {
            header[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        }
    }
    output.extend(code);
    output.resize(data_offset + 1, 0);
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::verify;

    #[test]
    fn native_rejects_unsupported_layouts_and_entry_assumptions() {
        for source in [
            "fn read(n: usize, a: [usize; n]) -> usize {n} fn main() -> usize {0}",
            "type Dynamic struct {len: usize, data: [usize; len]} fn main() -> usize {let d = Dynamic {len: 1, data: [42]}; d.data[0]}",
            "fn main() -> usize where (false) {0}",
            "fn main() -> [usize; 1] {[0]}",
        ] {
            let program = verify(source).unwrap();
            assert!(
                emit(&program).is_err(),
                "accepted unsupported native source: {source}"
            );
        }
    }

    #[test]
    fn native_stack_bound_includes_the_call_tree() {
        let mut source = String::new();
        for index in 0..34 {
            source.push_str(&format!("fn f{index}() -> usize {{"));
            for local in 0..250 {
                source.push_str(&format!("let x{local}: usize = 0;"));
            }
            if index == 0 {
                source.push_str("42}");
            } else {
                source.push_str(&format!("f{}()}}", index - 1));
            }
        }
        source.push_str("fn main() -> usize {f33()}");
        let program = verify(&source).unwrap();
        assert!(emit(&program).unwrap_err().contains("stack budget"));
        let mut source = "fn f0(a: [usize; 512]) -> usize {a[0]}".to_string();
        for index in 1..6 {
            source.push_str(&format!(
                "fn f{index}(a: [usize; 512]) -> usize {{f{}(a)}}",
                index - 1
            ));
        }
        let values = vec!["0"; 512].join(",");
        source.push_str(&format!(
            "fn main() -> usize {{let a: [usize; 512] = [{values}]; f5(a)}}"
        ));
        let program = verify(&source).unwrap();
        assert!(emit(&program).unwrap_err().contains("stack budget"));
        let recursive = "fn recurse(n: usize) -> usize ensures(result == n) decreases(n) {let a: [usize; 128] = [VALUES]; if n == 0 {0} else {recurse(n - 1) + 1}} fn main() -> usize {recurse(1)}".replace("VALUES", &vec!["0"; 128].join(","));
        assert!(emit(&verify(&recursive).unwrap())
            .unwrap_err()
            .contains("stack budget"));
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    fn execute_test_binary(
        path: &std::path::Path,
        binary: &[u8],
        source: &str,
    ) -> std::process::ExitStatus {
        use std::{
            fs,
            os::unix::fs::PermissionsExt,
            process::{Command, Stdio},
            time::{Duration, Instant},
        };
        fs::write(path, binary).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
        let mut child = Command::new(path)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(3);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("native test timed out: {source}");
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        status
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn native_execution_agrees_with_the_interpreter() {
        use std::{
            fs,
            time::{SystemTime, UNIX_EPOCH},
        };
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("evergreen-native-{}-{stamp}", std::process::id()));
        fs::create_dir(&directory).unwrap();
        let mut cases = [
            include_str!("../examples/partial_recursion.evg"),
            include_str!("../examples/ideal_bindings.evg"),
            "type Resource struct {tag: usize} where(tag == 42); impl Drop for Resource {fn drop(self){}} ideal fn observe(r: &Resource) -> nat ensures(result == nat((*r).tag)) {nat((*r).tag)} fn main() -> usize {let r = Resource {tag: 42}; ideal let saved = observe(&r); proof correct: saved == 42; r.tag}",
            include_str!("../examples/erased_resources.evg"),
            "fn answer(ideal expected: nat) -> usize where(expected == 42) ensures(result == 42) {42} fn caller(n: usize) -> usize where(n == 42) ensures(result == 42) {n = 0; answer(nat(old(n)))} fn main() -> usize {caller(42)}",
            "fn answer(ideal data: [usize; 1]) -> usize where(data[0] == 42) ensures(result == 42) {42} fn main() -> usize {answer([42])}",
            include_str!("../examples/opaque_values.evg"),
            "module a {fn get() -> usize ensures(result == 20) {20}} module b {fn get() -> usize ensures(result == 22) {22}} fn main() -> usize {a::get() + b::get()}",
            "module owned {opaque type Resource struct {tag: usize} where(self.tag == 42); impl Drop for Resource {fn drop(self) {proof valid: self.tag == 42;}} fn make() -> Resource {Resource {tag: 42}} fn read(r: &Resource) -> usize ensures(result == (*r).tag) {(*r).tag}} fn main() -> usize {let r = owned::make(); owned::read(&r)}",
            include_str!("../examples/indexed_borrows.evg"),
            include_str!("../examples/weak_invariant.evg"),
            "fn main() -> bool {false => true => false}",
            "fn main() -> bool {true => false}",
            include_str!("../examples/array_borrows.evg"),
            include_str!("../examples/borrow_returns.evg"),
            include_str!("../examples/computed_places.evg"),
            include_str!("../examples/old_places.evg"),
            include_str!("../examples/reference_fields.evg"),
            include_str!("../examples/drop_effects.evg"),
            include_str!("../examples/drop_children.evg"),
            include_str!("../examples/owned_borrows.evg"),
            include_str!("../examples/borrowed_view.evg"),
            include_str!("../examples/borrowed_array.evg"),
            include_str!("../examples/borrowed_array_owners.evg"),
            include_str!("../examples/reference_array_inputs.evg"),
            include_str!("../examples/aliasing_calls.evg"),
            include_str!("../examples/propositional_proofs.evg"),
            "fn main() -> usize where(old(1 + 1) == 2) {42}",
            "type Fixed struct {value: usize} where(value == 42); fn refresh(r: &Fixed) -> &Fixed modifies(&(*r).value) borrows(r) ensures((*r).value == 42 && (*result).value == 42) {(*r).value = 42; r} fn main() -> usize {let fixed = Fixed {value: 42}; let refreshed = refresh(&fixed); (*refreshed).value}",
            include_str!("../examples/recursion.evg"),
            include_str!("../examples/drop.evg"),
            include_str!("../examples/temporary_cleanup.evg"),
            include_str!("../examples/borrowed_temporaries.evg"),
            include_str!("../examples/native.evg"),
            include_str!("../examples/native_aggregates.evg"),
            include_str!("../examples/array_contracts.evg"),
            include_str!("../examples/destructure.evg"),
            include_str!("../examples/affine_values.evg"),
            include_str!("../examples/structs.evg"),
            include_str!("../examples/conditional_records.evg"),
            "fn identity(a: [usize; 2]) -> [usize; 1 + 1] {a} fn main() -> usize {let input: [usize; 2] = [7, 42]; let a: [usize; 2] = identity(input); a[1]}",
            "fn empty() -> [usize; 0] {[]} fn main() -> usize {let a = empty(); 42}",
            "type Pair struct {left: usize, right: usize} fn pick(p: Pair, marker: usize) -> usize ensures (result == p.left) {p.left} fn set(r: &usize) -> usize modifies(r) ensures (*r == 99 && result == 0) {*r = 99; 0} fn main() -> usize ensures (result == 42) {let p = Pair {left: 42, right: 0}; pick(p, set(&p.left))}",
            include_str!("../examples/intermediate_states.evg"),
            include_str!("../examples/conditional_writes.evg"),
            "fn head(ideal n: nat, data: &[usize; n]) -> usize where (n > 0) {(*data)[0]} fn main() -> usize {let a: [usize; 1] = [42]; head(1, &a)}",
            "fn set(r: &usize) -> usize modifies(r) ensures (*r == 99 && result == 0) {*r = 99; 0} fn main() -> usize {let a: [usize; 1] = [42]; a[set(&a[0])]}",
            "type Values struct {first: usize, second: usize} fn set(r: &usize) -> usize modifies(r) ensures (*r == 99 && result == 0) {*r = 99; 0} fn main() -> usize {let n: usize = 42; let v = Values {first: n, second: set(&n)}; v.first}",
            "fn main() -> usize {let a: [usize; (1 - 2) + 2] = [7, 42]; a[1]}",
            "fn main() -> usize {let a: [[usize; 2]; 2] = [[1, 2], [3, 42]]; a[1][1]}",
            "fn main() -> i8 {-128}",
            "fn main() -> u8 {255}",
            "fn main() -> u64 {u64::MAX}",
            "fn main() -> i64 {i64::MIN}",
            "fn main() -> bool {let x: i64 = -1; x < 0}",
            "fn main() -> bool {let x: u64 = u64::MAX; x > 0}",
            "fn main() -> bool {(1 < 2) == !(3 < 2)}",
            "fn main() -> usize {let x: usize = 42; let y = move(x); y}",
            "fn main() -> usize {let x: usize = 1; drop(x); x = 42; x}",
            "fn main() -> usize {let x: usize = 1; let r = &x; *r = 42; x}",
            "fn main() -> usize {let x: usize = 1; let a = &x; let b = &x; *a = 42; *b}",
            "fn main() -> usize {let x: usize = 42; let r = &x; let rr = &r; **rr}",
            "fn main() -> usize {let x: usize = 1; let y: usize = 42; let r = &x; let rr = &r; r = &y; **rr}",
            "fn read(r: &usize) -> usize ensures (result == *r) {*r} fn main() -> usize {let x: usize = 42; read(&x)}",
            "fn flip(r: &bool) modifies(r) ensures (*r == !old(*r)) {*r = !*r;} fn main() -> bool {let x = false; flip(&x); x}",
            "fn main() -> usize {(9 - 2) * 6}",
            "fn main() -> bool {true && (false || true)}",
            "fn main() -> () {()}",
            "type Resource struct {tag: usize} where(tag == 7); impl Drop for Resource {fn drop(self){}} fn consume(r: Resource) -> usize ensures(result == 7) {r.tag} fn recurse(n: usize, r: Resource) -> usize ensures(result == 7) decreases(n) {if n == 0 {consume(r)} else {recurse(n - 1, r)}} fn main() -> usize {let r = Resource {tag: 7}; recurse(5, r)}",
            "fn choose(a: usize, b: usize, flag: bool) -> usize ensures ((flag && result == a) || (!flag && result == b)) {if flag {a} else {b}} fn main() -> usize {choose(7, 42, false)}",
            "fn add(a: usize, b: usize) -> usize where (a <= 10 && b <= 10) ensures (result == a + b) {a + b} fn main() -> usize {add(1, add(2, 3))}",
            "fn sum(a: usize,b: usize,c: usize,d: usize,e: usize,f: usize,g: usize,h: usize) -> usize where (a <= 10 && b <= 10 && c <= 10 && d <= 10 && e <= 10 && f <= 10 && g <= 10 && h <= 10) {a+b+c+d+e+f+g+h} fn main() -> usize {sum(1,2,3,4,5,6,7,8)}",
        ].map(str::to_owned).to_vec();
        cases.push(
            [
                include_str!("../stdlib/array.evg"),
                include_str!("../examples/array_updates.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/array.evg"),
                include_str!("../examples/write_borrows.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/swap.evg"),
                include_str!("../examples/disjoint_writes.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/counter.evg"),
                include_str!("../examples/counter.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/counter.evg"),
                include_str!("../examples/drop_helpers.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/counter.evg"),
                include_str!("../examples/drop_count.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../proofs/rc_protocol.evg"),
                include_str!("../stdlib/counter.evg"),
                include_str!("../proofs/rc_count_refinement.evg"),
                include_str!("../examples/rc_count.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/counter.evg"),
                include_str!("../proofs/count_handles.evg"),
                include_str!("../examples/clone_count.evg"),
            ]
            .join("\n"),
        );
        cases.push(
            [
                include_str!("../stdlib/counter.evg"),
                include_str!("../proofs/count_handles.evg"),
                include_str!("../examples/batch_count.evg"),
            ]
            .join("\n"),
        );
        let deferred = include_str!("../examples/drop_effects.evg")
            .split("fn main")
            .next()
            .unwrap();
        for body in [
            "let count: usize = 0; StoreOnDrop {target: &count, value: 42}; count",
            "let count: usize = 0; let saved = StoreOnDrop {target: &count, value: 42}.value; count",
            "let count: usize = 0; let guard = StoreOnDrop {target: &count, value: 7}; guard = StoreOnDrop {target: &count, value: 42}; drop(guard); count",
            "let count: usize = 0; let guards: [StoreOnDrop; 2] = [StoreOnDrop {target: &count, value: 7}, StoreOnDrop {target: &count, value: 42}]; drop(guards); count",
            "let count: usize = 0; let sum = StoreOnDrop {target: &count, value: 7}.value + StoreOnDrop {target: &count, value: 42}.value; count",
        ] {
            cases.push(format!("{deferred} fn main() -> usize {{{body}}}"));
        }
        cases.push(format!("{deferred} fn array_scope(target: &usize) modifies(target) ensures(*target == 42) {{let guards: [StoreOnDrop; 2] = [StoreOnDrop {{target: target, value: 7}}, StoreOnDrop {{target: target, value: 42}}];}} fn main() -> usize {{let count: usize = 0; array_scope(&count); count}}"));
        for flag in [true, false] {
            cases.push(format!("{deferred} fn choose(target: &usize, flag: bool) -> usize modifies(target) ensures(result == *target) {{if flag {{StoreOnDrop {{target: target, value: 7}}.value}} else {{StoreOnDrop {{target: target, value: 42}}.value}}}} fn main() -> usize {{let count: usize = 0; choose(&count, {flag})}}"));
        }
        // A factory exists only in this test fixture; the shipped credit API
        // intentionally has no public minting operation.
        let credit_test = include_str!("../stdlib/credits.evg").replace(
            "module credits {",
            "module credits {ideal fn issue() -> Credit ensures(result.units == 42) {Credit {units: 42}}",
        );
        cases.push(format!(
            "{credit_test} {} fn main() -> usize {{use_budget(credits::issue(), 42)}}",
            include_str!("../proofs/ideal_credit_bindings.evg")
        ));
        let indexed = include_str!("../examples/indexed_borrows.evg")
            .split("fn main")
            .next()
            .unwrap();
        for i in 0..2 {
            for j in 0..2 {
                cases.push(format!(
                    "{indexed} fn main() -> usize {{may_alias([7, 1], {i}, {j})}}"
                ));
            }
        }
        let swap = include_str!("../stdlib/swap.evg");
        cases.push(format!("{swap} fn change(data: [usize; 2], i: usize, j: usize) -> usize where(i < 2 && j < 2 && i != j) ensures(result == data[j]) {{swap_usize(&data[i], &data[j]); data[i]}} fn main() -> usize {{change([7, 42], 0, 1)}}"));
        cases.push("fn signed(data: &[usize; 2], index: isize) -> &usize where(index >= 0 && index < 2) borrows(&(*data)[index]) {&(*data)[index]} fn main() -> usize {let a: [usize; 2] = [7, 42]; *signed(&a, 1)}".into());
        cases.push("fn change(data: [bool; 2], i: usize, j: usize) -> bool where(i < 2 && j < 2) ensures(i == j => result) {let a = &data[i]; let b = &data[j]; *a = true; *b} fn main() -> bool {change([false, false], 0, 0)}".into());
        let declarations = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self){}} fn make() -> Resource {Resource {tag: 7}} fn consume(r: Resource) -> usize {r.tag}";
        for body in [
            "let r = make(); let s = r; s.tag",
            "let r = make(); r = make(); r.tag",
            "let r = make(); r = move(r); r.tag",
            "Resource {tag: 7}; 7",
            "make().tag",
            "let r = make(); let s = if true {move(r)} else {move(r)}; s.tag",
            "let r = make(); if true {move(r)} else {move(r)}; 7",
            "let r = make(); drop(r); 7",
            "let r = make(); consume(r)",
            "[Resource {tag: 7}]; 7",
            "let a: [Resource; 2] = [make(), make()]; a[0].tag",
            "let a: [Resource; 0] = []; 7",
        ] {
            cases.push(format!("{declarations} fn main() -> usize {{{body}}}"));
        }
        let pair = "type Left struct {} impl Drop for Left {fn drop(self){}} type Right struct {} impl Drop for Right {fn drop(self){}} type Pair struct {left: Left, right: Right} fn take(p: Pair) -> Left {let Pair {left, right} = p; left}";
        for body in [
            "let p = Pair {left: Left {}, right: Right {}}; p.left = Left {}; 42",
            "let p = Pair {left: Left {}, right: Right {}}; p = Pair {left: take(p), right: Right {}}; 42",
        ] {
            cases.push(format!("{pair} fn main() -> usize {{{body}}}"));
        }
        cases.push("type Owner struct {tag: usize} where (tag == 7); impl Drop for Owner {fn drop(self){}} type Holder struct {reference: &usize, tag: usize} where (fact live = *reference == 7; live); impl Drop for Holder {fn drop(self){proof receiver_valid: self::live;}} fn main() -> usize {let owner = Owner {tag: 7}; let value = Holder {reference: &owner.tag, tag: 42}.tag; drop(owner); value}".into());
        for (index, source) in cases.iter().enumerate() {
            let program = verify(source).unwrap_or_else(|error| panic!("{error}: {source}"));
            let (value, events) = program.run_with_events().unwrap();
            let expected = match value {
                crate::runtime::Value::Machine(_, n) => i32::from(n as u8),
                crate::runtime::Value::Bool(b) => i32::from(b),
                crate::runtime::Value::Unit => 0,
                other => panic!("unexpected native value: {other}"),
            };
            let mut modes = vec![(TraceMode::Value, expected)];
            if !program.drops.is_empty() {
                let ids = program
                    .drops
                    .iter()
                    .enumerate()
                    .map(|(i, name)| (format!("drop {name}"), i as u64 + 1))
                    .collect::<BTreeMap<_, _>>();
                let order = events.iter().fold(0u64, |h, event| {
                    h.wrapping_mul(167).wrapping_add(ids[event])
                });
                modes.push((TraceMode::Count, i32::from(events.len() as u8)));
                modes.push((TraceMode::Order, i32::from(order as u8)));
            }
            for (mode_index, (mode, expected)) in modes.into_iter().enumerate() {
                let binary =
                    emit_mode(&program, mode).unwrap_or_else(|error| panic!("{error}: {source}"));
                assert_eq!(binary, emit_mode(&program, mode).unwrap());
                assert_eq!(&binary[..4], b"\x7fELF");
                let path = directory.join(format!("{index}-{mode_index}"));
                let status = execute_test_binary(&path, &binary, source);
                assert_eq!(
                    status.code(),
                    Some(expected),
                    "native/interpreter disagreement: {source}"
                );
            }
        }
        // These exceed the interpreter's separate host-stack budget; execute
        // bounded native images directly and check the exact guard boundary.
        let recursive = "fn count(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {count(n - 1) + 1}}";
        for (n, expected) in [(127, 127), (128, 125), (1000, 125)] {
            let source = format!("{recursive} fn main() -> usize {{count({n})}}");
            let program = verify(&source).unwrap();
            let binary = emit(&program).unwrap();
            let status =
                execute_test_binary(&directory.join(format!("limit-{n}")), &binary, &source);
            assert_eq!(status.code(), Some(expected));
        }
        let spin = "fn spin() -> usize ensures(false) {spin()} fn main() -> usize {spin()}";
        let binary = emit(&verify(spin).unwrap()).unwrap();
        assert_eq!(
            execute_test_binary(&directory.join("divergent"), &binary, spin).code(),
            Some(125)
        );
        let source = format!("{recursive} fn main() -> usize {{count(127) + count(127)}}");
        let binary = emit(&verify(&source).unwrap()).unwrap();
        assert_eq!(
            execute_test_binary(&directory.join("repeated-recursion"), &binary, &source).code(),
            Some(254)
        );
        fs::remove_dir_all(directory).unwrap();
    }
}
