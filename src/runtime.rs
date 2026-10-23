//! Bounded reference evaluator; construction requires a verified program.
use crate::{
    syntax::{Expr, Function, Kind, Struct, Type},
    verify::VerifiedProgram,
};
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i128),
    Nat(i128),
    Bool(bool),
    Array(Vec<Value>),
    Record(String, BTreeMap<String, Value>),
}
impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(n) | Self::Nat(n) => write!(f, "{n}"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Array(items) => {
                write!(f, "[")?;
                for (i, x) in items.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, "]")
            }
            Self::Record(n, fields) => write!(f, "{n} {fields:?}"),
        }
    }
}
impl Value {
    fn number(&self) -> Result<i128> {
        match self {
            Self::Int(n) | Self::Nat(n) => Ok(*n),
            _ => Err("expected integer".into()),
        }
    }
    fn boolean(&self) -> Result<bool> {
        if let Self::Bool(b) = self {
            Ok(*b)
        } else {
            Err("expected boolean".into())
        }
    }
    fn hint(&self) -> Option<Type> {
        match self {
            Self::Int(_) => Some(Type::Int),
            Self::Nat(_) => Some(Type::Nat),
            Self::Bool(_) => Some(Type::Bool),
            Self::Record(n, _) => Some(Type::Named(n.clone())),
            _ => None,
        }
    }
}
struct Evaluator<'a> {
    functions: &'a [Function],
    structs: &'a BTreeMap<String, Struct>,
    fuel: usize,
    depth: usize,
}
impl Evaluator<'_> {
    fn hint(&self, e: &Expr, env: &BTreeMap<String, Value>) -> Option<Type> {
        match &e.kind {
            Kind::Name(n) => env.get(n).and_then(Value::hint),
            Kind::Unary(_, x) => self.hint(x, env),
            Kind::Field(base, field) => {
                if let Kind::Name(n) = &base.kind {
                    if let Some(Value::Record(_, fields)) = env.get(n) {
                        return fields.get(field).and_then(Value::hint);
                    }
                }
                None
            }
            Kind::Binary(_, a, b) => self.hint(a, env).or_else(|| self.hint(b, env)),
            Kind::Call(n, _) => self
                .functions
                .iter()
                .find(|f| f.name == *n)
                .map(|f| f.ret.clone()),
            _ => None,
        }
    }
    fn call(&mut self, name: &str, actuals: Vec<Value>) -> Result<Value> {
        if self.depth >= 128 {
            return Err("execution call depth limit reached".into());
        }
        let f = self
            .functions
            .iter()
            .find(|f| f.name == name)
            .cloned()
            .ok_or("unknown function")?;
        if f.params.len() != actuals.len() {
            return Err("argument count mismatch".into());
        }
        let mut env: BTreeMap<String, Value> = f
            .params
            .iter()
            .map(|(n, _)| n.clone())
            .zip(actuals)
            .collect();
        self.depth += 1;
        if let Some(pre) = &f.pre {
            if !self.expr(pre, &env, Some(&Type::Bool))?.boolean()? {
                return Err(format!("entry precondition of {name} is false"));
            }
        }
        for statement in &f.body {
            if let Some(target) = &statement.target {
                fn path(e: &Expr, fields: &mut Vec<String>) -> Result<String> {
                    match &e.kind {
                        Kind::Name(n) => Ok(n.clone()),
                        Kind::Field(b, n) => {
                            let root = path(b, fields)?;
                            fields.push(n.clone());
                            Ok(root)
                        }
                        _ => Err("invalid assignment".into()),
                    }
                }
                fn replace(root: &mut Value, fields: &[String], value: Value) -> Result<()> {
                    if fields.is_empty() {
                        *root = value;
                        return Ok(());
                    }
                    let Value::Record(_, members) = root else {
                        return Err("invalid field assignment".into());
                    };
                    replace(
                        members.get_mut(&fields[0]).ok_or("unknown field")?,
                        &fields[1..],
                        value,
                    )
                }
                let old = self.expr(target, &env, None)?;
                let new = self.expr(&statement.value, &env, old.hint().as_ref())?;
                let mut fields = Vec::new();
                let root = path(target, &mut fields)?;
                replace(
                    env.get_mut(&root).ok_or("unknown assignment target")?,
                    &fields,
                    new,
                )?;
                continue;
            }
            if statement.effect {
                self.expr(&statement.value, &env, None)?;
                continue;
            }
            if !statement.fact {
                let value = self.expr(&statement.value, &env, statement.ty.as_ref())?;
                env.insert(statement.name.clone(), value);
            }
        }
        let value = self.expr(&f.result, &env, Some(&f.ret))?;
        self.depth -= 1;
        Ok(value)
    }
    fn expr(
        &mut self,
        e: &Expr,
        env: &BTreeMap<String, Value>,
        expected: Option<&Type>,
    ) -> Result<Value> {
        if self.fuel == 0 {
            return Err("execution step limit reached (100000)".into());
        }
        self.fuel -= 1;
        self.inner(e, env, expected).map_err(|s| {
            if s.starts_with("line ") {
                s
            } else {
                format!("line {}: {s}", e.line)
            }
        })
    }
    fn inner(
        &mut self,
        e: &Expr,
        env: &BTreeMap<String, Value>,
        expected: Option<&Type>,
    ) -> Result<Value> {
        match &e.kind {
            Kind::Number(n) => Ok(if matches!(expected, Some(Type::Nat)) {
                Value::Nat(*n)
            } else {
                Value::Int(*n)
            }),
            Kind::Bool(b) => Ok(Value::Bool(*b)),
            Kind::Name(n) => env
                .get(n)
                .cloned()
                .ok_or_else(|| format!("unknown value {n}")),
            Kind::Field(base, field) => {
                let Value::Record(_, fields) = self.expr(base, env, None)? else {
                    return Err("expected struct".into());
                };
                fields
                    .get(field)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {field}"))
            }
            Kind::Record(name, entries) => {
                let def = self.structs.get(name).cloned().ok_or("unknown struct")?;
                let mut fields = BTreeMap::new();
                for (n, e) in entries {
                    let t = def
                        .fields
                        .iter()
                        .find(|(field, _)| field == n)
                        .map(|(_, t)| t)
                        .ok_or("unknown field")?;
                    fields.insert(n.clone(), self.expr(e, env, Some(t))?);
                }
                Ok(Value::Record(name.clone(), fields))
            }
            Kind::Unary(op, x) => {
                if op == "!" {
                    Ok(Value::Bool(
                        !self.expr(x, env, Some(&Type::Bool))?.boolean()?,
                    ))
                } else {
                    Ok(Value::Int(
                        self.expr(x, env, Some(&Type::Int))?
                            .number()?
                            .checked_neg()
                            .ok_or("bootstrap evaluator integer overflow")?,
                    ))
                }
            }
            Kind::Binary(op, a, b) if op == "&&" || op == "||" => {
                let a = self.expr(a, env, Some(&Type::Bool))?.boolean()?;
                let b = self.expr(b, env, Some(&Type::Bool))?.boolean()?;
                Ok(Value::Bool(if op == "&&" { a && b } else { a || b }))
            }
            Kind::Binary(op, a, b) => {
                let ty = if matches!(op.as_str(), "+" | "-" | "*") {
                    expected.cloned()
                } else {
                    None
                }
                .or_else(|| self.hint(a, env))
                .or_else(|| self.hint(b, env))
                .unwrap_or(Type::Int);
                let a = self.expr(a, env, Some(&ty))?.number()?;
                let b = self.expr(b, env, Some(&ty))?.number()?;
                let number = match op.as_str() {
                    "+" => a.checked_add(b),
                    "-" if ty == Type::Nat => Some(if a < b { 0 } else { a - b }),
                    "-" => a.checked_sub(b),
                    "*" => a.checked_mul(b),
                    "==" => return Ok(Value::Bool(a == b)),
                    "!=" => return Ok(Value::Bool(a != b)),
                    "<" => return Ok(Value::Bool(a < b)),
                    "<=" => return Ok(Value::Bool(a <= b)),
                    ">" => return Ok(Value::Bool(a > b)),
                    ">=" => return Ok(Value::Bool(a >= b)),
                    _ => return Err("unsupported binary expression".into()),
                }
                .ok_or("bootstrap evaluator integer overflow")?;
                Ok(if ty == Type::Nat {
                    Value::Nat(number)
                } else {
                    Value::Int(number)
                })
            }
            Kind::Array(items) => {
                let element = if let Some(Type::Array(t, _)) = expected {
                    Some((**t).clone())
                } else {
                    items
                        .first()
                        .and_then(|x| self.hint(x, env))
                        .or(Some(Type::Int))
                };
                items
                    .iter()
                    .map(|x| self.expr(x, env, element.as_ref()))
                    .collect::<Result<Vec<_>>>()
                    .map(Value::Array)
            }
            Kind::Index(array, index) => {
                let array = self.expr(array, env, None)?;
                let index = self.expr(index, env, Some(&Type::Nat))?.number()?;
                let Value::Array(items) = array else {
                    return Err("expected array".into());
                };
                let i = usize::try_from(index).map_err(|_| "index exceeds evaluator limit")?;
                items.get(i).cloned().ok_or_else(|| {
                    "verified index out of bounds: compiler/runtime disagreement".into()
                })
            }
            Kind::Call(name, args) => {
                let types = self
                    .functions
                    .iter()
                    .find(|f| f.name == *name)
                    .ok_or("unknown function")?
                    .params
                    .iter()
                    .map(|(_, t)| t.clone())
                    .collect::<Vec<_>>();
                let values = args
                    .iter()
                    .zip(&types)
                    .map(|(x, t)| self.expr(x, env, Some(t)))
                    .collect::<Result<Vec<_>>>()?;
                self.call(name, values)
            }
            Kind::If(condition, yes, no) => {
                if self.expr(condition, env, Some(&Type::Bool))?.boolean()? {
                    self.expr(yes, env, expected)
                } else {
                    self.expr(no, env, expected)
                }
            }
        }
    }
}

impl VerifiedProgram {
    pub fn run(&self) -> Result<Value> {
        let mut evaluator = Evaluator {
            functions: &self.functions,
            structs: &self.structs,
            fuel: 100_000,
            depth: 0,
        };
        evaluator.call("main", vec![])
    }
}

#[cfg(test)]
mod tests {
    use crate::verify::verify;
    #[test]
    fn executes_verified_calls_arrays_and_branches() {
        let s = "fn abs(n: isize) -> isize ensures (result >= 0) { if n >= 0 { n } else { -n } } fn main() -> isize { let a: [isize; 2] = [-4, 8]; abs(a[0]) }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "4");
        assert_eq!(
            verify(include_str!("../examples/contracts.evg"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
    }
    #[test]
    fn false_entry_precondition_cannot_execute() {
        assert!(verify("fn main() -> usize where (false) { 1 }")
            .unwrap()
            .run()
            .is_err());
    }
    #[test]
    fn reports_evaluator_overflow_without_panicking() {
        let source = format!(
            "fn double(n: isize) -> isize {{ n + n }} fn main() -> isize {{ double({}) }}",
            i128::MAX
        );
        assert!(verify(&source).unwrap().run().is_err());
    }
}
