//! Small Linux x86-64 backend. Source verification is required before emission.
//! This backend is trusted code, not a machine-checked compiler-correctness proof.
use crate::{
    layout,
    syntax::{Expr, Function, Kind, MachineInt, Statement, Struct, Type},
    verify::VerifiedProgram,
};
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, String>;
const BASE: u64 = 0x400000;
const HEADER: usize = 64 + 2 * 56;
const STACK: usize = 65536;
const MAX_CODE: usize = 8 * 1024 * 1024;

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
struct Emitter<'a> {
    code: &'a mut Vec<u8>,
    known: &'a BTreeMap<String, Compiled>,
    functions: &'a BTreeMap<String, &'a Function>,
    slots: BTreeMap<String, (i32, Type)>,
    frame: usize,
    structs: &'a BTreeMap<String, Struct>,
    temporary: usize,
    peak: usize,
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
    fn index_address(&mut self, base: &Expr, index: &Expr, place: bool) -> Result<Type> {
        let ty = if place {
            self.address(base)?
        } else {
            self.expr(base, None)?
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
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||"
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
            Kind::Index(base, index) => self.index_address(base, index, true),
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
            Kind::Name(n) => self.load(n)?,
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
            Kind::Field(base, name) => {
                let base = self.expr(base, None)?;
                let field = self.field(&base, name)?;
                self.add_offset(field.offset);
                if !layout::aggregate(&field.ty) {
                    self.code.extend([0x48, 0x8b, 0x00]);
                }
                field.ty
            }
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
                let ty = self.index_address(base, index, borrowed)?;
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
                let logical = matches!(op.as_str(), "&&" | "||");
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
                self.expr(condition, Some(&Type::Bool))?;
                self.code.extend([0x48, 0x85, 0xc0]);
                let alternative = self.jump(true);
                let ty = self.expr(yes, expected)?;
                let end = self.jump(false);
                let target = self.code.len();
                patch(self.code, alternative, target)?;
                self.expr(no, Some(&ty))?;
                let target = self.code.len();
                patch(self.code, end, target)?;
                ty
            }
            Kind::Call(name, args) if matches!(name.as_str(), "move" | "drop") => {
                if args.len() != 1 {
                    return Err("invalid native move/drop".into());
                }
                let ty = self.expr(&args[0], None)?;
                if name == "drop" {
                    self.immediate(0);
                    Type::Unit
                } else {
                    ty
                }
            }
            Kind::Call(name, args) => {
                let function = self.functions.get(name).ok_or("unknown native callee")?;
                let callee = self
                    .known
                    .get(name)
                    .ok_or("native recursion and calls to ideal functions are unsupported")?
                    .clone();
                if function.params.len() != args.len() {
                    return Err("native argument count mismatch".into());
                }
                let saved_temporary = self.temporary;
                for ((parameter, ty), arg) in function.params.iter().zip(args) {
                    if function.ideal_params.contains(parameter) {
                        continue;
                    }
                    self.expr(arg, Some(ty))?;
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
                }
                if layout::aggregate(&function.ret) {
                    let output = self.allocate(&function.ret)?;
                    self.frame_address(output);
                    self.push();
                }
                self.peak = self.peak.max(self.temporary + 8 + callee.stack);
                self.code.push(0xe8);
                let displacement = self.code.len();
                self.code.extend([0; 4]);
                patch(self.code, displacement, callee.offset)?;
                let argument_bytes = self.temporary - saved_temporary;
                if argument_bytes > 0 {
                    self.code.extend([0x48, 0x81, 0xc4]);
                    self.code.extend(
                        u32::try_from(argument_bytes)
                            .map_err(|_| "native argument stack overflow")?
                            .to_le_bytes(),
                    );
                    self.temporary = saved_temporary;
                }
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
        match statement {
            Statement::Fact { .. } | Statement::Proof { .. } => Ok(()),
            Statement::Let { name, ty, value } => {
                let ty = self.expr(value, ty.as_ref())?;
                self.slot(name, ty)
            }
            Statement::Assign { target, value } => {
                let ty = self.address(target)?;
                self.push();
                self.expr(value, Some(&ty))?;
                self.pop();
                self.copy_address(&ty)
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
                for statement in body {
                    self.statement(statement)?;
                }
                self.slots = saved;
                Ok(())
            }
            Statement::Effect(e) => {
                self.expr(e, None)?;
                Ok(())
            }
        }
    }
}

/// Emit a standalone Linux x86-64 executable. Its scalar main result is the
/// process exit status (low eight bits). It performs no runtime I/O.
pub fn emit(program: &VerifiedProgram) -> Result<Vec<u8>> {
    program.check_entry()?;
    if !program.drops.is_empty() {
        return Err("native destructors require checked cleanup lowering; unsupported".into());
    }
    let functions = program
        .functions
        .iter()
        .map(|f| (f.name.clone(), f))
        .collect::<BTreeMap<_, _>>();
    let mut known = BTreeMap::new();
    let mut code = vec![0x48, 0xbc];
    code.extend([0; 8]); // mov rsp, private stack end
    code.push(0xe8);
    let entry_call = code.len();
    code.extend([0; 4]);
    code.extend([0x48, 0x89, 0xc7, 0xb8, 60, 0, 0, 0, 0x0f, 0x05, 0x0f, 0x0b]);
    for function in &program.functions {
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
        emitter.expr(&function.result, Some(&function.ret))?;
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
        let stack = 8 + frame + emitter.peak;
        if stack + 8 > STACK {
            return Err("native call tree exceeds 64 KiB private stack budget".into());
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
    fn native_rejects_unsupported_memory_recursion_and_entry_assumptions() {
        for source in [
            "fn read(n: usize, a: [usize; n]) -> usize {n} fn main() -> usize {0}",
            "type Dynamic struct {len: usize, data: [usize; len]} fn main() -> usize {let d = Dynamic {len: 1, data: [42]}; d.data[0]}",
            include_str!("../examples/drop.evg"),
            include_str!("../examples/recursion.evg"),
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
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn native_execution_agrees_with_the_interpreter() {
        use std::{
            fs,
            os::unix::fs::PermissionsExt,
            process::{Command, Stdio},
            time::{Duration, Instant, SystemTime, UNIX_EPOCH},
        };
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("evergreen-native-{}-{stamp}", std::process::id()));
        fs::create_dir(&directory).unwrap();
        let mut cases = [
            include_str!("../examples/native.evg"),
            include_str!("../examples/native_aggregates.evg"),
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
            "fn choose(a: usize, b: usize, flag: bool) -> usize ensures ((flag && result == a) || (!flag && result == b)) {if flag {a} else {b}} fn main() -> usize {choose(7, 42, false)}",
            "fn add(a: usize, b: usize) -> usize where (a <= 10 && b <= 10) ensures (result == a + b) {a + b} fn main() -> usize {add(1, add(2, 3))}",
            "fn sum(a: usize,b: usize,c: usize,d: usize,e: usize,f: usize,g: usize,h: usize) -> usize where (a <= 10 && b <= 10 && c <= 10 && d <= 10 && e <= 10 && f <= 10 && g <= 10 && h <= 10) {a+b+c+d+e+f+g+h} fn main() -> usize {sum(1,2,3,4,5,6,7,8)}",
        ].map(str::to_owned).to_vec();
        cases.push(
            [
                include_str!("../stdlib/counter.evg"),
                include_str!("../examples/counter.evg"),
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
        for (index, source) in cases.iter().enumerate() {
            let program = verify(source).unwrap_or_else(|error| panic!("{error}: {source}"));
            let expected = match program.run().unwrap() {
                crate::runtime::Value::Machine(_, n) => i32::from(n as u8),
                crate::runtime::Value::Bool(b) => i32::from(b),
                crate::runtime::Value::Unit => 0,
                other => panic!("unexpected native value: {other}"),
            };
            let binary = emit(&program).unwrap();
            assert_eq!(binary, emit(&program).unwrap());
            assert_eq!(&binary[..4], b"\x7fELF");
            let path = directory.join(index.to_string());
            fs::write(&path, binary).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
            let mut child = Command::new(&path)
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
            assert_eq!(
                status.code(),
                Some(expected),
                "native/interpreter disagreement: {source}"
            );
        }
        fs::remove_dir_all(directory).unwrap();
    }
}
