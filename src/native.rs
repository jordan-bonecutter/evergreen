//! Small Linux x86-64 backend. Source verification is required before emission.
//! This backend is trusted code, not a machine-checked compiler-correctness proof.
use crate::{
    syntax::{Expr, Function, Kind, MachineInt, Statement, Type},
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
        Err("native backend currently requires scalar runtime values; arrays, records, and references are unsupported".into())
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
struct Emitter<'a> {
    code: &'a mut Vec<u8>,
    known: &'a BTreeMap<String, Compiled>,
    functions: &'a BTreeMap<String, &'a Function>,
    slots: BTreeMap<String, (i32, Type)>,
    next_slot: usize,
    temporary: usize,
    peak: usize,
}
impl Emitter<'_> {
    fn slot(&mut self, name: &str, ty: Type) -> Result<()> {
        scalar(&ty)?;
        self.next_slot += 1;
        let offset = i32::try_from(self.next_slot * 8).map_err(|_| "native frame overflow")?;
        if self.slots.insert(name.into(), (-offset, ty)).is_some() {
            return Err("duplicate native binding".into());
        }
        self.code.extend([0x48, 0x89, 0x85]);
        self.code.extend((-offset).to_le_bytes());
        Ok(())
    }
    fn load(&mut self, name: &str) -> Result<Type> {
        let (offset, ty) = self
            .slots
            .get(name)
            .ok_or_else(|| format!("missing native binding {name}"))?;
        self.code.extend([0x48, 0x8b, 0x85]);
        self.code.extend(offset.to_le_bytes());
        Ok(ty.clone())
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
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Constant(t, _) => Some(Type::Machine(*t)),
            Kind::Unary(op, _) if op == "!" => Some(Type::Bool),
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
                let mut count = 0usize;
                for ((parameter, ty), arg) in function.params.iter().zip(args) {
                    if function.ideal_params.contains(parameter) {
                        continue;
                    }
                    self.expr(arg, Some(ty))?;
                    self.push();
                    count += 1;
                }
                self.peak = self.peak.max(self.temporary + 8 + callee.stack);
                self.code.push(0xe8);
                let displacement = self.code.len();
                self.code.extend([0; 4]);
                patch(self.code, displacement, callee.offset)?;
                if count > 0 {
                    self.code.extend([0x48, 0x81, 0xc4]);
                    self.code.extend(
                        u32::try_from(count * 8)
                            .map_err(|_| "native argument stack overflow")?
                            .to_le_bytes(),
                    );
                    self.temporary -= count * 8;
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
        scalar(&ty)?;
        if expected.is_some_and(|t| t != &ty) {
            return Err(format!("line {}: native type mismatch", e.line));
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
                let Kind::Name(name) = &target.kind else {
                    return Err("native field/reference assignments are unsupported".into());
                };
                let (offset, ty) = self
                    .slots
                    .get(name)
                    .cloned()
                    .ok_or("unknown native assignment")?;
                self.expr(value, Some(&ty))?;
                self.code.extend([0x48, 0x89, 0x85]);
                self.code.extend(offset.to_le_bytes());
                Ok(())
            }
            Statement::Effect(e) => {
                self.expr(e, None)?;
                Ok(())
            }
            _ => Err("native patterns and invariant updates are unsupported".into()),
        }
    }
}

/// Emit a standalone Linux x86-64 executable. Its scalar main result is the
/// process exit status (low eight bits). It performs no runtime I/O.
pub fn emit(program: &VerifiedProgram) -> Result<Vec<u8>> {
    program.check_entry()?;
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
        scalar(&function.ret)?;
        let params = function
            .params
            .iter()
            .filter(|(n, _)| !function.ideal_params.contains(n))
            .collect::<Vec<_>>();
        for (_, ty) in &params {
            scalar(ty)?;
        }
        let locals = function
            .body
            .iter()
            .filter(|s| matches!(s, Statement::Let { .. }))
            .count();
        let frame = (params.len() + locals)
            .checked_mul(8)
            .ok_or("native frame overflow")?;
        if frame + 16 > STACK {
            return Err("native frame exceeds private stack budget".into());
        }
        let offset = code.len();
        code.extend([0x55, 0x48, 0x89, 0xe5, 0x48, 0x81, 0xec]);
        code.extend((frame as u32).to_le_bytes());
        let mut emitter = Emitter {
            code: &mut code,
            known: &known,
            functions: &functions,
            slots: BTreeMap::new(),
            next_slot: 0,
            temporary: 0,
            peak: 0,
        };
        for (index, (name, ty)) in params.iter().enumerate() {
            emitter.code.extend([0x48, 0x8b, 0x85]);
            let incoming = u32::try_from(16 + (params.len() - index - 1) * 8)
                .map_err(|_| "native parameter offset overflow")?;
            emitter.code.extend(incoming.to_le_bytes());
            emitter.slot(name, ty.clone())?;
        }
        for statement in &function.body {
            emitter.statement(statement)?;
        }
        emitter.expr(&function.result, Some(&function.ret))?;
        if emitter.temporary != 0 {
            return Err("unbalanced native expression stack".into());
        }
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
            "fn main() -> usize {let x: usize = 1; let r = &x; *r}",
            "fn main() -> usize {let a: [usize; 1] = [1]; a[0]}",
            include_str!("../examples/destructure.evg"),
            include_str!("../examples/recursion.evg"),
            "fn main() -> usize where (false) {0}",
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
        let cases = [
            include_str!("../examples/native.evg"),
            "fn main() -> i8 {-128}",
            "fn main() -> u8 {255}",
            "fn main() -> u64 {u64::MAX}",
            "fn main() -> i64 {i64::MIN}",
            "fn main() -> bool {let x: i64 = -1; x < 0}",
            "fn main() -> bool {let x: u64 = u64::MAX; x > 0}",
            "fn main() -> bool {(1 < 2) == !(3 < 2)}",
            "fn main() -> usize {let x: usize = 42; let y = move(x); y}",
            "fn main() -> usize {let x: usize = 1; drop(x); x = 42; x}",
            "fn main() -> usize {(9 - 2) * 6}",
            "fn main() -> bool {true && (false || true)}",
            "fn main() -> () {()}",
            "fn choose(a: usize, b: usize, flag: bool) -> usize ensures ((flag && result == a) || (!flag && result == b)) {if flag {a} else {b}} fn main() -> usize {choose(7, 42, false)}",
            "fn add(a: usize, b: usize) -> usize where (a <= 10 && b <= 10) ensures (result == a + b) {a + b} fn main() -> usize {add(1, add(2, 3))}",
            "fn sum(a: usize,b: usize,c: usize,d: usize,e: usize,f: usize,g: usize,h: usize) -> usize where (a <= 10 && b <= 10 && c <= 10 && d <= 10 && e <= 10 && f <= 10 && g <= 10 && h <= 10) {a+b+c+d+e+f+g+h} fn main() -> usize {sum(1,2,3,4,5,6,7,8)}",
        ];
        for (index, source) in cases.iter().enumerate() {
            let program = verify(source).unwrap();
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
