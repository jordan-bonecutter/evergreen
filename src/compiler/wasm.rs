//! Initial WebAssembly backend. Verification always precedes emission.
//!
//! Layout and word-sized integers use targets/wasm.evg.
//! The internal scalar calling convention uses i64 registers; addresses are wasm32. The portable console import is the only
//! host capability; Linux syscalls, owners and raw unions are rejected. Records currently have scalar fields.

use super::{layout, verify::VerifiedProgram};
use crate::syntax::{Expr, External, Function, Kind, Statement, Type};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, String>;
const I64: u8 = 0x7e;
const I32: u8 = 0x7f;
const MEMORY_PAGES: u32 = 64;
const MAX_FRAME: u32 = 64 * 1024;
const MAX_CODE: usize = 8 * 1024 * 1024;

fn unsigned(mut value: u32, out: &mut Vec<u8>) {
    loop {
        let byte = (value & 127) as u8;
        value >>= 7;
        out.push(byte | if value == 0 { 0 } else { 128 });
        if value == 0 {
            break;
        }
    }
}

fn signed(mut value: i64, out: &mut Vec<u8>) {
    loop {
        let byte = (value & 127) as u8;
        value >>= 7;
        let done = (value == 0 && byte & 64 == 0) || (value == -1 && byte & 64 != 0);
        out.push(byte | if done { 0 } else { 128 });
        if done {
            break;
        }
    }
}

fn name(value: &str, out: &mut Vec<u8>) {
    unsigned(value.len() as u32, out);
    out.extend(value.as_bytes());
}

fn section(id: u8, bytes: Vec<u8>, out: &mut Vec<u8>) {
    out.push(id);
    unsigned(bytes.len() as u32, out);
    out.extend(bytes);
}

fn machine() -> Type {
    Type::Machine(
        crate::compiler::TargetKind::Wasm32
            .integer("isize")
            .unwrap(),
    )
}

fn scalar(ty: &Type) -> bool {
    matches!(ty, Type::Machine(_) | Type::Bool | Type::Unit)
}

fn supported(ty: &Type) -> Result<()> {
    match ty {
        Type::Machine(_) | Type::Bool | Type::Unit | Type::Named(_) => Ok(()),
        Type::Ref(inner) => supported(inner),
        Type::Array(inner, _) if scalar(inner) || matches!(inner.as_ref(), Type::Named(_)) => {
            Ok(())
        }
        _ => Err(format!(
            "WebAssembly target does not yet support runtime type {}",
            crate::syntax::display::expression(&Expr {
                kind: Kind::Type(ty.clone()),
                line: 0
            })
        )),
    }
}

#[derive(Clone)]
struct Slot {
    offset: u32,
    ty: Type,
}

struct Emitter<'a> {
    program: &'a VerifiedProgram,
    functions: &'a BTreeMap<String, (&'a Function, u32)>,
    slots: BTreeMap<String, Slot>,
    code: Vec<u8>,
    frame: u32,
    frame_local: u32,
    data: &'a mut Vec<u8>,
}

impl Emitter<'_> {
    fn op(&mut self, opcode: u8, argument: u32) {
        self.code.push(opcode);
        unsigned(argument, &mut self.code);
    }

    fn i32(&mut self, value: u32) {
        self.code.push(0x41);
        signed(value as i32 as i64, &mut self.code);
    }
    fn i64(&mut self, value: i128) {
        self.code.push(0x42);
        signed(value as i64, &mut self.code);
    }

    fn allocate(&mut self, ty: &Type) -> Result<u32> {
        supported(ty)?;
        let object = layout::of_for(self.program.target, ty, &self.program.structs)?;
        self.frame = self.frame.next_multiple_of(object.align as u32);
        let offset = self.frame;
        self.frame = self
            .frame
            .checked_add(object.size.max(1) as u32)
            .ok_or("WebAssembly frame overflow")?;
        if self.frame > MAX_FRAME {
            return Err("WebAssembly function exceeds 64 KiB stack frame limit".into());
        }
        Ok(offset)
    }

    fn address_offset(&mut self, offset: u32) {
        self.op(0x20, self.frame_local);
        self.i32(offset);
        self.code.push(0x6a); // i32.add
    }

    fn size(&self, ty: &Type) -> Result<u32> {
        Ok(layout::of_for(self.program.target, ty, &self.program.structs)?.size as u32)
    }

    fn load(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            let offset = self.allocate(ty)?;
            self.op(0x21, self.frame_local + 1);
            self.address_offset(offset);
            self.op(0x20, self.frame_local + 1);
            self.i32(self.size(ty)?);
            self.code.extend([0xfc, 10, 0, 0]);
            self.address_offset(offset);
            self.code.push(0xad);
            return Ok(());
        }
        if self.size(ty)? == 0 {
            self.code.push(0x1a); // discard address; unit has no stored bytes
            self.i64(0);
            return Ok(());
        }
        let signed = matches!(ty, Type::Machine(integer) if integer.signed);
        self.code.push(match (self.size(ty)?, signed) {
            (1, true) => 0x30,
            (1, false) => 0x31,
            (2, true) => 0x32,
            (2, false) => 0x33,
            (4, true) => 0x34,
            (4, false) => 0x35,
            (8, _) => 0x29,
            _ => return Err("unsupported WebAssembly scalar width".into()),
        });
        self.code.extend([0, 0]); // unaligned access, offset 0
        Ok(())
    }

    // Destination i32 and value i64 are already on the operand stack.
    fn store(&mut self, ty: &Type) -> Result<()> {
        if self.size(ty)? == 0 {
            self.code.extend([0x1a, 0x1a]); // discard value and destination
            return Ok(());
        }
        if layout::aggregate(ty) {
            self.code.push(0xa7); // i32.wrap_i64 source
            self.i32(self.size(ty)?);
            self.code.extend([0xfc, 10, 0, 0]); // memory.copy
        } else {
            self.code.push(match self.size(ty)? {
                1 => 0x3c,
                2 => 0x3d,
                4 => 0x3e,
                8 => 0x37,
                _ => return Err("unsupported WebAssembly scalar width".into()),
            });
            self.code.extend([0, 0]);
        }
        Ok(())
    }

    fn hint(&self, e: &Expr) -> Option<Type> {
        self.hint_in(e, &self.slots)
    }

    fn hint_in(&self, e: &Expr, scope: &BTreeMap<String, Slot>) -> Option<Type> {
        match &e.kind {
            Kind::Bytes(bytes) => Some(Type::bytes(bytes.len(), e.line)),
            Kind::Constant(integer, _) => Some(Type::Machine(*integer)),
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Unit => Some(Type::Unit),
            Kind::Name(n) => scope.get(n).map(|slot| slot.ty.clone()),
            Kind::Record(n, _) => Some(Type::Named(n.clone())),
            Kind::Field(base, field) => {
                let Type::Named(n) = self.hint_in(base, scope)? else {
                    return None;
                };
                self.program
                    .structs
                    .get(&n)?
                    .fields
                    .iter()
                    .find(|(name, _)| name == field)
                    .map(|(_, ty)| ty.clone())
            }
            Kind::Unary(op, x) if op == "&" => {
                self.hint_in(x, scope).map(|ty| Type::Ref(Box::new(ty)))
            }
            Kind::Unary(op, x) if op == "*" => match self.hint_in(x, scope)? {
                Type::Ref(inner) => Some(*inner),
                _ => None,
            },
            Kind::Unary(_, x) => self.hint_in(x, scope),
            Kind::Index(base, _) => match self.hint_in(base, scope)? {
                Type::Array(inner, _) => Some(*inner),
                _ => None,
            },
            Kind::Binary(op, _, _)
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "=>" | "<=>"
                ) =>
            {
                Some(Type::Bool)
            }
            Kind::Binary(_, a, b) => self.hint_in(a, scope).or_else(|| self.hint_in(b, scope)),
            Kind::If(_, a, b) => self.hint_in(a, scope).or_else(|| self.hint_in(b, scope)),
            Kind::Block(body, tail) => {
                let mut scope = scope.clone();
                for statement in body {
                    if let Statement::Let { name, ty, value } = statement {
                        let ty = ty
                            .clone()
                            .or_else(|| self.hint_in(value, &scope))
                            .unwrap_or_else(machine);
                        scope.insert(name.clone(), Slot { offset: 0, ty });
                    }
                }
                self.hint_in(tail, &scope)
            }
            Kind::Call(n, _) if matches!(n.as_str(), "size_of" | "align_of") => {
                Some(Type::Machine(self.program.target.integer("usize").unwrap()))
            }
            Kind::Call(n, _) if self.program.target.integer(n).is_some() => {
                self.program.target.integer(n).map(Type::Machine)
            }
            Kind::Call(n, _) => self
                .functions
                .get(n)
                .map(|(function, _)| function.ret.clone()),
            Kind::Array(items) => Some(Type::Array(
                Box::new(
                    items
                        .first()
                        .and_then(|x| self.hint_in(x, scope))
                        .unwrap_or_else(machine),
                ),
                Box::new(Expr {
                    kind: Kind::Number(items.len() as i128),
                    line: e.line,
                }),
            )),
            _ => None,
        }
    }

    // A place leaves an i32 linear-memory address on the operand stack.
    fn address(&mut self, e: &Expr) -> Result<Type> {
        match &e.kind {
            Kind::Name(n) => {
                let slot = self
                    .slots
                    .get(n)
                    .ok_or_else(|| format!("unknown WebAssembly local {n}"))?
                    .clone();
                self.address_offset(slot.offset);
                Ok(slot.ty)
            }
            Kind::Unary(op, x) if op == "*" => {
                let Type::Ref(inner) = self.expr(x, None)? else {
                    return Err("WebAssembly dereference requires a borrow".into());
                };
                self.code.push(0xa7);
                Ok(*inner)
            }
            Kind::Index(base, index) => {
                let ty = if base.stored_place() {
                    self.address(base)?
                } else {
                    let ty = self.expr(base, None)?;
                    self.code.push(0xa7);
                    ty
                };
                let Type::Array(inner, _) = ty else {
                    return Err("WebAssembly indexing requires an array".into());
                };
                self.expr(index, None)?;
                self.i64(self.size(&inner)? as i128);
                self.code.extend([0x7e, 0xa7, 0x6a]); // multiply, wrap, add
                Ok(*inner)
            }
            Kind::Field(base, field) => {
                let ty = if base.stored_place() {
                    self.address(base)?
                } else {
                    let ty = self.expr(base, None)?;
                    self.code.push(0xa7);
                    ty
                };
                let object = layout::of_for(self.program.target, &ty, &self.program.structs)?;
                let member = object
                    .fields
                    .get(field)
                    .ok_or("unknown Wasm record field")?;
                self.i32(member.offset as u32);
                self.code.push(0x6a);
                Ok(member.ty.clone())
            }
            Kind::Bytes(_) | Kind::Array(_) => {
                let ty = self.expr(e, None)?;
                self.code.push(0xa7);
                Ok(ty)
            }
            _ => Err(format!("line {}: unsupported WebAssembly place", e.line)),
        }
    }

    fn tick(&mut self) {
        self.op(0x23, 1); // global fuel
        self.code.extend([0x45, 0x04, 0x40, 0x00, 0x0b]); // trap if zero
        self.op(0x23, 1);
        self.i32(1);
        self.code.push(0x6b);
        self.op(0x24, 1);
    }

    fn statement(&mut self, statement: &Statement) -> Result<()> {
        match statement {
            Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => {}
            Statement::Let { name, ty, value } => {
                let ty = ty
                    .clone()
                    .or_else(|| self.hint(value))
                    .unwrap_or_else(machine);
                let offset = self.allocate(&ty)?;
                self.address_offset(offset);
                self.expr(value, Some(&ty))?;
                self.store(&ty)?;
                self.slots.insert(name.clone(), Slot { offset, ty });
            }
            Statement::Assign {
                target,
                value,
                starts,
            } => {
                if !starts.is_empty() {
                    return Err(
                        "WebAssembly target does not yet support assignment ownership starts"
                            .into(),
                    );
                }
                let ty = self.address(target)?;
                self.expr(value, Some(&ty))?;
                self.store(&ty)?;
            }
            Statement::Effect(value) => {
                self.expr(value, None)?;
                self.code.push(0x1a);
            }
            Statement::While {
                condition, body, ..
            } => {
                let saved = self.slots.clone();
                self.code.extend([0x02, 0x40, 0x03, 0x40]); // block, loop
                self.tick();
                self.expr(condition, Some(&Type::Bool))?;
                self.code.push(0x50); // i64.eqz
                self.op(0x0d, 1); // br_if exit
                for statement in body {
                    self.statement(statement)?;
                }
                self.op(0x0c, 0);
                self.code.extend([0x0b, 0x0b]);
                self.slots = saved;
            }
            Statement::Update { body, .. } => {
                let saved = self.slots.clone();
                for statement in body {
                    self.statement(statement)?;
                }
                self.slots = saved;
            }
            _ => return Err("WebAssembly target does not yet support record destructuring".into()),
        }
        Ok(())
    }

    fn expr(&mut self, e: &Expr, expected: Option<&Type>) -> Result<Type> {
        let ty = match &e.kind {
            Kind::Number(value) => {
                self.i64(*value);
                expected.cloned().unwrap_or_else(machine)
            }
            Kind::Constant(integer, value) => {
                self.i64(*value);
                Type::Machine(*integer)
            }
            Kind::Bool(value) => {
                self.i64(*value as i128);
                Type::Bool
            }
            Kind::Unit => {
                self.i64(0);
                Type::Unit
            }
            Kind::Name(_) | Kind::Index(_, _) | Kind::Field(_, _) => {
                let ty = self.address(e)?;
                self.load(&ty)?;
                ty
            }
            Kind::Bytes(bytes) => {
                let ty = Type::bytes(bytes.len(), e.line);
                let destination = self.allocate(&ty)?;
                let source = 16 + self.data.len() as u32;
                self.data.extend(bytes);
                self.address_offset(destination);
                self.i32(source);
                self.i32(bytes.len() as u32);
                self.code.extend([0xfc, 10, 0, 0]);
                self.address_offset(destination);
                self.code.push(0xad);
                ty
            }
            Kind::Record(name, fields) => {
                let ty = Type::Named(name.clone());
                let offset = self.allocate(&ty)?;
                let object = layout::of_for(self.program.target, &ty, &self.program.structs)?;
                for (name, value) in fields {
                    let Some(field) = object.fields.get(name) else {
                        continue;
                    };
                    self.address_offset(offset + field.offset as u32);
                    self.expr(value, Some(&field.ty))?;
                    self.store(&field.ty)?;
                }
                self.address_offset(offset);
                self.code.push(0xad);
                ty
            }
            Kind::Array(items) => {
                let ty = expected
                    .cloned()
                    .or_else(|| self.hint(e))
                    .ok_or("missing array type")?;
                let Type::Array(element, extent) = &ty else {
                    return Err("WebAssembly array literal type mismatch".into());
                };
                if layout::array_length(extent)? != items.len() {
                    return Err("WebAssembly array extent mismatch".into());
                }
                let offset = self.allocate(&ty)?;
                let size = self.size(element)?;
                for (index, item) in items.iter().enumerate() {
                    self.address_offset(offset + index as u32 * size);
                    self.expr(item, Some(element))?;
                    self.store(element)?;
                }
                self.address_offset(offset);
                self.code.push(0xad);
                ty
            }
            Kind::Unary(op, x) if op == "&" => {
                let inner = self.address(x)?;
                self.code.push(0xad);
                Type::Ref(Box::new(inner))
            }
            Kind::Unary(op, _) if op == "*" => {
                let ty = self.address(e)?;
                self.load(&ty)?;
                ty
            }
            Kind::Unary(op, x) if op == "!" => {
                self.expr(x, Some(&Type::Bool))?;
                self.code.extend([0x50, 0xad]);
                Type::Bool
            }
            Kind::Unary(op, x) if op == "-" => {
                let ty = expected
                    .cloned()
                    .or_else(|| self.hint(x))
                    .unwrap_or_else(machine);
                self.i64(0);
                self.expr(x, Some(&ty))?;
                self.code.push(0x7d);
                ty
            }
            Kind::Binary(op, a, b) => {
                let arithmetic = matches!(op.as_str(), "+" | "-" | "*");
                let logical = matches!(op.as_str(), "&&" | "||" | "=>" | "<=>");
                let operand = if logical {
                    Type::Bool
                } else {
                    (if arithmetic { expected.cloned() } else { None })
                        .or_else(|| self.hint(a))
                        .or_else(|| self.hint(b))
                        .unwrap_or_else(machine)
                };
                self.expr(a, Some(&operand))?;
                self.expr(b, Some(&operand))?;
                let signed = matches!(operand, Type::Machine(integer) if integer.signed);
                self.code.push(match op.as_str() {
                    "+" => 0x7c,
                    "-" => 0x7d,
                    "*" => 0x7e,
                    "&&" => 0x83,
                    "||" => 0x84,
                    "==" | "<=>" => 0x51,
                    "!=" => 0x52,
                    "<" => {
                        if signed {
                            0x53
                        } else {
                            0x54
                        }
                    }
                    ">" => {
                        if signed {
                            0x55
                        } else {
                            0x56
                        }
                    }
                    "<=" => {
                        if signed {
                            0x57
                        } else {
                            0x58
                        }
                    }
                    ">=" => {
                        if signed {
                            0x59
                        } else {
                            0x5a
                        }
                    }
                    _ => {
                        return Err(format!(
                            "line {}: unsupported WebAssembly operator {op}",
                            e.line
                        ))
                    }
                });
                if (!arithmetic && !logical) || op == "<=>" {
                    self.code.push(0xad);
                }
                if arithmetic {
                    operand
                } else {
                    Type::Bool
                }
            }
            Kind::If(condition, yes, no) => {
                let saved = self.slots.clone();
                let ty = expected
                    .cloned()
                    .or_else(|| self.hint(yes))
                    .or_else(|| self.hint(no))
                    .unwrap_or_else(machine);
                self.expr(condition, Some(&Type::Bool))?;
                self.code.extend([0x50, 0x45, 0x04, I64]); // truth value, if (result i64)
                self.expr(yes, Some(&ty))?;
                self.slots = saved.clone();
                self.code.push(0x05);
                self.expr(no, Some(&ty))?;
                self.code.push(0x0b);
                self.slots = saved;
                ty
            }
            Kind::Block(body, tail) => {
                let saved = self.slots.clone();
                for statement in body {
                    self.statement(statement)?;
                }
                let ty = self.expr(tail, expected)?;
                self.slots = saved;
                ty
            }
            Kind::Call(n, args) if self.program.target.integer(n).is_some() => {
                let ty = Type::Machine(self.program.target.integer(n).unwrap());
                self.expr(&args[0], Some(&ty))?;
                ty
            }
            Kind::Call(n, args) if matches!(n.as_str(), "size_of" | "align_of") => {
                let value =
                    layout::query::value_for(self.program.target, n, args, &self.program.structs)?;
                self.i64(value as i128);
                Type::Machine(self.program.target.integer("usize").unwrap())
            }
            Kind::Call(n, args) => {
                let (function, index) = *self
                    .functions
                    .get(n)
                    .ok_or_else(|| format!("WebAssembly target does not support operation {n}"))?;
                let supplied = function.supplied_parameters(args.len())?;
                for ((parameter, ty), argument) in supplied.into_iter().zip(args) {
                    if !function.ideal_params.contains(parameter) {
                        self.expr(argument, Some(ty))?;
                    }
                }
                self.op(0x10, index);
                if layout::aggregate(&function.ret) {
                    self.code.push(0xa7);
                    self.load(&function.ret)?;
                }
                function.ret.clone()
            }
            _ => {
                return Err(format!(
                    "line {}: expression is not supported by the initial WebAssembly target",
                    e.line
                ))
            }
        };
        supported(&ty)?;
        // Values stay normalized even when no store/reload narrows them.
        if let Type::Machine(integer) = &ty {
            if integer.bits < 64 {
                if integer.signed {
                    self.code.push(match integer.bits {
                        8 => 0xc2,
                        16 => 0xc3,
                        32 => 0xc4,
                        _ => return Err("unsupported signed WebAssembly integer width".into()),
                    });
                } else {
                    self.i64((1i128 << integer.bits) - 1);
                    self.code.push(0x83); // i64.and
                }
            }
        }
        if self.code.len() > MAX_CODE {
            return Err("WebAssembly code limit exceeded".into());
        }
        Ok(ty)
    }
}

/// Emit a standalone WebAssembly module exporting `main` and `memory`.
/// Imports `evergreen.console_write(length: i64, pointer: i64) -> i64` when used.
/// All functions/loop iterations share a 100,000-step budget and 128-call limit.
pub fn emit(program: &VerifiedProgram) -> Result<Vec<u8>> {
    if program.target != crate::compiler::TargetKind::Wasm32 {
        return Err("wasm emission requires a program checked for Wasm32".into());
    }
    program.check_entry()?;
    crate::shared::worker::run("evergreen-wasm-emitter", || emit_inner(program))
}

fn emit_inner(program: &VerifiedProgram) -> Result<Vec<u8>> {
    for record in program.structs.values().filter(|record| !record.ideal) {
        if program.drops.contains(&record.name)
            || record.runtime_fields().any(|(_, ty)| !scalar(ty))
        {
            return Err(
                "WebAssembly records currently require scalar fields and no destructor".into(),
            );
        }
    }
    let functions = program
        .functions
        .iter()
        .filter(|f| !f.ideal)
        .collect::<Vec<_>>();
    let mut ordered = Vec::new();
    ordered.extend(functions.iter().copied().filter(|f| f.external.is_some()));
    let imports = ordered.len();
    ordered.extend(functions.iter().copied().filter(|f| f.external.is_none()));
    let known = ordered
        .iter()
        .enumerate()
        .map(|(i, f)| (f.name.clone(), (*f, i as u32)))
        .collect::<BTreeMap<_, _>>();
    for function in &ordered {
        if function.name == "main" && !scalar(&function.ret) {
            return Err("WebAssembly main requires a scalar result".into());
        }
        if function
            .external
            .is_some_and(|external| external != External::ConsoleWrite)
        {
            return Err(format!("WebAssembly target does not support external operation in {}; use console::print or console::println for output", function.name));
        }
        if !scalar(&function.ret) && !matches!(function.ret, Type::Named(_)) {
            return Err(format!(
                "WebAssembly target currently requires scalar or scalar-field record results: {}",
                function.name
            ));
        }
        for (_, ty) in function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
        {
            supported(ty)?;
            if layout::aggregate(ty) && !matches!(ty, Type::Named(_)) {
                return Err(
                    "WebAssembly target currently requires arrays to be passed by reference".into(),
                );
            }
        }
    }
    let mut types = Vec::new();
    unsigned(ordered.len() as u32, &mut types);
    for function in &ordered {
        types.push(0x60);
        let count = function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .count();
        unsigned(count as u32, &mut types);
        types.extend(std::iter::repeat_n(I64, count));
        types.extend([1, I64]);
    }
    let mut import_section = Vec::new();
    unsigned(imports as u32, &mut import_section);
    for index in 0..imports {
        name("evergreen", &mut import_section);
        name("console_write", &mut import_section);
        import_section.push(0);
        unsigned(index as u32, &mut import_section);
    }
    let mut declarations = Vec::new();
    unsigned((ordered.len() - imports) as u32, &mut declarations);
    for index in imports..ordered.len() {
        unsigned(index as u32, &mut declarations);
    }
    let mut data = Vec::new();
    let mut bodies = Vec::new();
    unsigned((ordered.len() - imports) as u32, &mut bodies);
    for function in &ordered[imports..] {
        let parameters = function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .collect::<Vec<_>>();
        let mut emitter = Emitter {
            program,
            functions: &known,
            slots: BTreeMap::new(),
            code: Vec::new(),
            frame: 0,
            frame_local: parameters.len() as u32,
            data: &mut data,
        };
        for (index, (name, ty)) in parameters.iter().enumerate() {
            let offset = emitter.allocate(ty)?;
            emitter.address_offset(offset);
            emitter.op(0x20, index as u32);
            emitter.store(ty)?;
            emitter.slots.insert(
                name.to_string(),
                Slot {
                    offset,
                    ty: ty.clone(),
                },
            );
        }
        emitter.tick();
        for statement in &function.body {
            emitter.statement(statement)?;
        }
        emitter.expr(&function.result, Some(&function.ret))?;
        emitter.op(0x20, emitter.frame_local);
        emitter.op(0x24, 0); // restore stack pointer, retaining result
        emitter.op(0x23, 2);
        emitter.i32(1);
        emitter.code.push(0x6b);
        emitter.op(0x24, 2);
        emitter.code.push(0x0b);
        let mut body = vec![1, 2, I32]; // one frame-pointer local
        body.extend([0x23, 2, 0x41, 0x01, 0x6a, 0x24, 2, 0x23, 2, 0x41]);
        signed(128, &mut body);
        body.extend([0x4b, 0x04, 0x40, 0x00, 0x0b]); // trap beyond 128 calls
        body.extend([0x23, 0, 0x22]);
        unsigned(emitter.frame_local, &mut body);
        body.push(0x41);
        signed(emitter.frame.next_multiple_of(8) as i64, &mut body);
        body.extend([0x6a, 0x24, 0]); // reserve frame
        body.extend(emitter.code);
        unsigned(body.len() as u32, &mut bodies);
        bodies.extend(body);
    }
    let mut memory = vec![1, 1]; // one memory, min and max
    unsigned(MEMORY_PAGES, &mut memory);
    unsigned(MEMORY_PAGES, &mut memory);
    if data.len() > 1024 * 1024 {
        return Err("WebAssembly literal data exceeds 1 MiB".into());
    }
    let mut globals = vec![3, I32, 1, 0x41];
    signed((16 + data.len()).next_multiple_of(8) as i64, &mut globals);
    globals.extend([0x0b, I32, 1, 0x41]);
    signed(100_000, &mut globals);
    globals.extend([0x0b, I32, 1, 0x41, 0, 0x0b]);
    let mut exports = vec![2];
    name("main", &mut exports);
    exports.push(0);
    unsigned(known.get("main").ok_or("missing main")?.1, &mut exports);
    name("memory", &mut exports);
    exports.extend([2, 0]);
    let mut data_section = vec![1, 0, 0x41, 16, 0x0b];
    unsigned(data.len() as u32, &mut data_section);
    data_section.extend(data);
    let mut module = b"\0asm\x01\0\0\0".to_vec();
    for (id, payload) in [
        (1, types),
        (2, import_section),
        (3, declarations),
        (5, memory),
        (6, globals),
        (7, exports),
        (10, bodies),
        (11, data_section),
    ] {
        section(id, payload, &mut module);
    }
    if module.len() > MAX_CODE {
        return Err("WebAssembly module exceeds 8 MiB limit".into());
    }
    Ok(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn verify(source: &str) -> Result<VerifiedProgram> {
        crate::compiler::verify::verify_for_target(source, crate::compiler::TargetKind::Wasm32)
    }

    #[test]
    fn emits_wasm_and_rejects_unproved_entry_or_unsupported_runtime() {
        let bytes = emit(&verify(include_str!("../../examples/console.evg")).unwrap()).unwrap();
        assert_eq!(&bytes[..8], b"\0asm\x01\0\0\0");
        for source in [
            "fn main() -> usize where(false) {0}",
            "fn main() -> usize {let p: unique(usize) = alloc(42); let n = *p; drop(p); n}",
            include_str!("../../examples/hello.evg"),
        ] {
            assert!(
                verify(source).and_then(|program| emit(&program)).is_err(),
                "accepted {source}"
            );
        }
    }
}
