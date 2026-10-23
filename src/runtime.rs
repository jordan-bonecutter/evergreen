//! Bounded reference evaluator; construction requires a verified program.
use crate::{
    memory::{Memory, PlaneId, Projection, Reference},
    syntax::{Expr, Function, Kind, MachineInt, Statement, Struct, Type},
    verify::VerifiedProgram,
};
use std::collections::{BTreeMap, BTreeSet};
type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i128),
    Nat(i128),
    Bool(bool),
    Array(Vec<Value>),
    Record(String, BTreeMap<String, Value>),
    Unit,
    Ref(Box<Type>, Reference, Vec<Projection>),
    Machine(MachineInt, i128),
}
impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(n) | Self::Nat(n) | Self::Machine(_, n) => write!(f, "{n}"),
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
            Self::Unit => write!(f, "()"),
            Self::Ref(_, _, _) => write!(f, "<reference>"),
        }
    }
}
impl Value {
    fn number(&self) -> Result<i128> {
        match self {
            Self::Int(n) | Self::Nat(n) | Self::Machine(_, n) => Ok(*n),
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
            Self::Ref(t, _, _) => Some(Type::Ref(t.clone())),
            Self::Unit => Some(Type::Unit),
            Self::Machine(t, _) => Some(Type::Machine(*t)),
            Self::Array(items) => Some(Type::Array(
                Box::new(items.first().and_then(Value::hint).unwrap_or(Type::Int)),
                Box::new(Expr {
                    kind: Kind::Number(items.len() as i128),
                    line: 0,
                }),
            )),
        }
    }
}
struct Evaluator<'a> {
    functions: &'a [Function],
    structs: &'a BTreeMap<String, Struct>,
    fuel: usize,
    depth: usize,
    memory: Memory<Value>,
    roots: BTreeMap<String, PlaneId>,
    drops: &'a BTreeSet<String>,
    events: Vec<String>,
}
impl Evaluator<'_> {
    fn hint(&self, e: &Expr, env: &BTreeMap<String, Value>) -> Option<Type> {
        match &e.kind {
            Kind::Constant(t, _) => Some(Type::Machine(*t)),
            Kind::Name(n) => env.get(n).and_then(Value::hint),
            Kind::Unary(op, x) if op == "*" => {
                if let Some(Type::Ref(t)) = self.hint(x, env) {
                    Some(*t)
                } else {
                    None
                }
            }
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
        let saved_roots = std::mem::take(&mut self.roots);
        self.depth += 1;
        if let Some(pre) = &f.pre {
            if !self.expr(pre, &env, Some(&Type::Bool))?.boolean()? {
                return Err(format!("entry precondition of {name} is false"));
            }
        }
        for statement in &f.body {
            match statement {
                Statement::Assign { target, value } => self.assign(target, value, &mut env)?,
                Statement::Update { body, .. } => {
                    let mut locals = Vec::new();
                    for update in body {
                        match update {
                            Statement::Assign { target, value } => {
                                self.assign(target, value, &mut env)?
                            }
                            Statement::Let { name, ty, value } => {
                                let value = self.expr(value, &env, ty.as_ref())?;
                                env.insert(name.clone(), value);
                                locals.push(name.clone());
                            }
                            Statement::Fact { .. } => {}
                            _ => return Err("unverified operation in update".into()),
                        }
                    }
                    for name in locals.into_iter().rev() {
                        if let Some(id) = self.roots.remove(&name) {
                            self.memory.take(id)?;
                        }
                        env.remove(&name);
                    }
                }
                Statement::Effect(e) => {
                    self.expr(e, &env, None)?;
                }
                Statement::Fact { .. } => {}
                Statement::Let { name, ty, value } => {
                    let v = self.expr(value, &env, ty.as_ref())?;
                    env.insert(name.clone(), v);
                }
            }
        }
        let value = self.expr(&f.result, &env, Some(&f.ret))?;
        let mut names = f.params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>();
        names.extend(f.body.iter().filter_map(|s| {
            if let Statement::Let { name, .. } = s {
                Some(name.clone())
            } else {
                None
            }
        }));
        for name in names.into_iter().rev() {
            let live = if let Some(id) = self.roots.get(&name) {
                if self.memory.get(*id).is_err() {
                    continue;
                }
                self.memory.take(*id)?
            } else {
                env.get(&name).cloned().ok_or("unknown cleanup binding")?
            };
            if name == "self" && f.drop_target.is_some() {
                self.drop_fields(live)?;
            } else {
                self.drop_value(live)?;
            }
        }
        self.roots = saved_roots;
        self.depth -= 1;
        Ok(value)
    }

    fn value_needs_drop(&self, value: &Value) -> bool {
        match value {
            Value::Record(n, _) => {
                crate::verify::needs_drop(&Type::Named(n.clone()), self.structs, self.drops)
            }
            Value::Array(xs) => xs.iter().any(|v| self.value_needs_drop(v)),
            _ => false,
        }
    }
    fn drop_value(&mut self, value: Value) -> Result<()> {
        if let Value::Record(name, _) = &value {
            if self.drops.contains(name) {
                let method = format!("evg_drop_{name}");
                self.events.push(format!("drop {name}"));
                self.call(&method, vec![value])?;
                return Ok(());
            }
        }
        self.drop_fields(value)
    }
    fn drop_fields(&mut self, value: Value) -> Result<()> {
        match value {
            Value::Record(name, mut fields) => {
                let order = self
                    .structs
                    .get(&name)
                    .ok_or("unknown drop layout")?
                    .fields
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect::<Vec<_>>();
                for field in order {
                    if let Some(value) = fields.remove(&field) {
                        self.drop_value(value)?;
                    }
                }
            }
            Value::Array(items) => {
                for value in items {
                    self.drop_value(value)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn assign(
        &mut self,
        target: &Expr,
        value: &Expr,
        env: &mut BTreeMap<String, Value>,
    ) -> Result<()> {
        if matches!(&target.kind, Kind::Unary(op, _) if op == "*") {
            let (r, path) = self.location(target, env)?;
            let old = project(self.memory.read(r)?, &path)?.clone();
            let new = self.expr(value, env, old.hint().as_ref())?;
            let id = self.memory.plane(r)?;
            let mut root = self.memory.read(r)?.clone();
            replace_projection(&mut root, &path, new)?;
            let replace_plane = !same_layout(&old, project(&root, &path)?);
            self.memory.write(id, root.clone(), replace_plane)?;
            for (n, p) in &self.roots {
                if *p == id {
                    env.insert(n.clone(), root.clone());
                }
            }
            return Ok(());
        }
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
        let old = if let Kind::Name(n) = &target.kind {
            env.get(n).cloned().ok_or("unknown assignment target")?
        } else {
            self.storage(target, env)?
        };
        let new = self.expr(value, env, old.hint().as_ref())?;
        let old_live = self
            .roots
            .get(&root_name(target)?)
            .is_none_or(|id| self.memory.get(*id).is_ok());
        if old_live && self.value_needs_drop(&old) {
            self.drop_value(old.clone())?;
        }
        let replace_plane = !same_layout(&old, &new);
        let mut fields = Vec::new();
        let root = path(target, &mut fields)?;
        replace(
            env.get_mut(&root).ok_or("unknown assignment target")?,
            &fields,
            new,
        )?;
        if let Some(id) = self.roots.get(&root) {
            self.memory.write(
                *id,
                env.get(&root).cloned().ok_or("unknown assignment root")?,
                replace_plane,
            )?;
        }

        Ok(())
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
            Kind::Unit => Ok(Value::Unit),
            Kind::Constant(t, n) => Ok(Value::Machine(*t, *n)),
            Kind::Number(n) => Ok(match expected {
                Some(Type::Nat) => Value::Nat(*n),
                Some(Type::Machine(t)) => Value::Machine(*t, *n),
                _ => Value::Int(*n),
            }),
            Kind::Bool(b) => Ok(Value::Bool(*b)),
            Kind::Name(n) => {
                let value = if let Some(id) = self.roots.get(n) {
                    self.memory.get(*id).cloned()
                } else {
                    env.get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown value {n}"))
                }?;
                if self.value_needs_drop(&value) {
                    let (r, _) = self.location(e, env)?;
                    let id = self.memory.plane(r)?;
                    self.memory.take(id)?;
                }
                Ok(value)
            }
            Kind::Field(base, field) => {
                let Value::Record(_, fields) = self.storage(base, env)? else {
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
                if op == "&" {
                    let (r, path) = self.location(x, env)?;
                    let ty = project(self.memory.read(r)?, &path)?
                        .hint()
                        .unwrap_or(Type::Unit);
                    Ok(Value::Ref(Box::new(ty), r, path))
                } else if op == "*" {
                    let (r, path) = self.location(e, env)?;
                    project(self.memory.read(r)?, &path).cloned()
                } else if op == "!" {
                    Ok(Value::Bool(
                        !self.expr(x, env, Some(&Type::Bool))?.boolean()?,
                    ))
                } else {
                    let ty = expected
                        .cloned()
                        .or_else(|| self.hint(x, env))
                        .filter(|t| matches!(t, Type::Machine(_)))
                        .unwrap_or(Type::Int);
                    let n = self
                        .expr(x, env, Some(&ty))?
                        .number()?
                        .checked_neg()
                        .ok_or("bootstrap evaluator integer overflow")?;
                    Ok(if let Type::Machine(t) = ty {
                        Value::Machine(t, n)
                    } else {
                        Value::Int(n)
                    })
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
                Ok(match ty {
                    Type::Nat => Value::Nat(number),
                    Type::Machine(t) => {
                        let (lo, hi) = t.bounds();
                        if number < lo || number > hi {
                            return Err(
                                "verified machine overflow: compiler/runtime disagreement".into()
                            );
                        }
                        Value::Machine(t, number)
                    }
                    _ => Value::Int(number),
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
                if name == "move" || name == "drop" {
                    let (r, path) = self.location(&args[0], env)?;
                    if !path.is_empty() {
                        return Err("cannot move partial plane".into());
                    }
                    let id = self.memory.plane(r)?;
                    let value = self.memory.take(id)?;
                    return if name == "drop" {
                        self.drop_value(value)?;
                        Ok(Value::Unit)
                    } else {
                        Ok(value)
                    };
                }
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

    fn location(
        &mut self,
        e: &Expr,
        env: &BTreeMap<String, Value>,
    ) -> Result<(Reference, Vec<Projection>)> {
        match &e.kind {
            Kind::Name(n) => {
                let id = if let Some(id) = self.roots.get(n) {
                    *id
                } else {
                    let v = env.get(n).cloned().ok_or("unknown place")?;
                    let id = self.memory.allocate(v)?;
                    self.roots.insert(n.clone(), id);
                    id
                };
                Ok((self.memory.borrow(id)?, vec![]))
            }
            Kind::Field(base, n) => {
                let (r, mut p) = self.location(base, env)?;
                p.push(Projection::Field(n.clone()));
                project(self.memory.read(r)?, &p)?;
                Ok((r, p))
            }
            Kind::Index(base, i) => {
                let (r, mut p) = self.location(base, env)?;
                let index = usize::try_from(self.expr(i, env, Some(&Type::Nat))?.number()?)
                    .map_err(|_| "invalid index")?;
                p.push(Projection::Index(index));
                project(self.memory.read(r)?, &p)?;
                Ok((r, p))
            }
            Kind::Unary(op, x) if op == "*" => {
                let Value::Ref(_, r, p) = self.expr(x, env, None)? else {
                    return Err("expected reference".into());
                };
                self.memory.read(r)?;
                Ok((r, p))
            }
            _ => Err("expected referenceable place".into()),
        }
    }

    fn storage(&mut self, e: &Expr, env: &BTreeMap<String, Value>) -> Result<Value> {
        match &e.kind {
            Kind::Name(n) => {
                if let Some(id) = self.roots.get(n) {
                    self.memory.get(*id).cloned()
                } else {
                    env.get(n).cloned().ok_or("unknown storage place".into())
                }
            }
            Kind::Field(base, field) => {
                let Value::Record(_, fields) = self.storage(base, env)? else {
                    return Err("expected struct storage".into());
                };
                fields
                    .get(field)
                    .cloned()
                    .ok_or("unknown storage field".into())
            }
            Kind::Unary(op, _) if op == "*" => {
                let (r, path) = self.location(e, env)?;
                project(self.memory.read(r)?, &path).cloned()
            }
            Kind::Index(base, index) => {
                let Value::Array(items) = self.storage(base, env)? else {
                    return Err("expected array storage".into());
                };
                let index = usize::try_from(self.expr(index, env, Some(&Type::Nat))?.number()?)
                    .map_err(|_| "invalid storage index")?;
                items
                    .get(index)
                    .cloned()
                    .ok_or("storage index out of bounds".into())
            }
            _ => self.expr(e, env, None),
        }
    }
}

fn root_name(e: &Expr) -> Result<String> {
    match &e.kind {
        Kind::Name(n) => Ok(n.clone()),
        Kind::Field(b, _) => root_name(b),
        _ => Err("not a local place".into()),
    }
}

fn same_layout(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Record(an, a), Value::Record(bn, b)) => {
            an == bn
                && a.len() == b.len()
                && a.iter()
                    .all(|(n, v)| b.get(n).is_some_and(|w| same_layout(v, w)))
        }
        (Value::Array(a), Value::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(v, w)| same_layout(v, w))
        }
        (Value::Int(_), Value::Int(_))
        | (Value::Nat(_), Value::Nat(_))
        | (Value::Bool(_), Value::Bool(_))
        | (Value::Ref(..), Value::Ref(..))
        | (Value::Unit, Value::Unit) => true,
        (Value::Machine(a, _), Value::Machine(b, _)) => a == b,
        _ => false,
    }
}

fn project<'a>(value: &'a Value, path: &[Projection]) -> Result<&'a Value> {
    if path.is_empty() {
        return Ok(value);
    }
    let value = match (&path[0], value) {
        (Projection::Field(n), Value::Record(_, fields)) => fields.get(n).ok_or("unknown field")?,
        (Projection::Index(i), Value::Array(items)) => {
            items.get(*i).ok_or("index out of bounds")?
        }
        _ => return Err("invalid reference projection".into()),
    };
    project(value, &path[1..])
}
fn replace_projection(value: &mut Value, path: &[Projection], new: Value) -> Result<()> {
    if path.is_empty() {
        *value = new;
        return Ok(());
    }
    let value = match (&path[0], value) {
        (Projection::Field(n), Value::Record(_, fields)) => {
            fields.get_mut(n).ok_or("unknown field")?
        }
        (Projection::Index(i), Value::Array(items)) => {
            items.get_mut(*i).ok_or("index out of bounds")?
        }
        _ => return Err("invalid reference projection".into()),
    };
    replace_projection(value, &path[1..], new)
}

impl VerifiedProgram {
    pub fn run(&self) -> Result<Value> {
        self.run_with_events().map(|(value, _)| value)
    }
    /// Returns a detached result snapshot and an execution trace for debugging.
    pub fn run_with_events(&self) -> Result<(Value, Vec<String>)> {
        let mut evaluator = Evaluator {
            functions: &self.functions,
            structs: &self.structs,
            fuel: 100_000,
            depth: 0,
            memory: Memory::default(),
            roots: BTreeMap::new(),
            drops: &self.drops,
            events: Vec::new(),
        };
        let value = evaluator.call("main", vec![])?;
        evaluator.drop_value(value.clone())?;
        Ok((value, evaluator.events))
    }
}

#[cfg(test)]
mod tests {
    use crate::verify::verify;
    #[test]
    fn executes_verified_calls_arrays_and_branches() {
        let s = "fn abs(n: int) -> int ensures (result >= 0) { if n >= 0 { n } else { -n } } fn main() -> int { let a: [int; 2] = [-4, 8]; abs(a[0]) }";
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
        assert!(verify("fn main() -> nat where (false) { 1 }")
            .unwrap()
            .run()
            .is_err());
    }
    #[test]
    fn reports_evaluator_overflow_without_panicking() {
        let source = format!(
            "fn double(n: int) -> int {{ n + n }} fn main() -> int {{ double({}) }}",
            i128::MAX
        );
        assert!(verify(&source).unwrap().run().is_err());
    }

    #[test]
    fn updates_do_not_drop_the_parent_or_its_owned_fields() {
        let (value, events) = verify(include_str!("../examples/drop.evg"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events, ["drop Pair", "drop Resource"]);
    }

    #[test]
    fn moves_and_reassignment_drop_each_resource_once() {
        let prefix = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self) {fact valid = self.tag == 7;}} ";
        for body in [
            "let a = Resource {tag: 7}; let b = a; a = Resource {tag: 7}; drop(b); 0",
            "let a = Resource {tag: 7}; a = Resource {tag: 7}; 0",
        ] {
            let (_, events) = verify(&format!("{prefix} fn main() -> usize {{ {body} }}"))
                .unwrap()
                .run_with_events()
                .unwrap();
            assert_eq!(events, ["drop Resource", "drop Resource"]);
        }
        let source = format!("{prefix} fn make() -> Resource {{Resource {{tag: 7}}}} fn consume(r: Resource) -> usize {{r.tag}} fn main() -> usize {{let r = make(); consume(r)}}");
        let (value, events) = verify(&source).unwrap().run_with_events().unwrap();
        assert_eq!(value.to_string(), "7");
        assert_eq!(events, ["drop Resource"]);
    }

    #[test]
    fn scope_cleanup_runs_in_reverse_binding_order() {
        let source = "type First struct {} impl Drop for First {fn drop(self){}} type Second struct {} impl Drop for Second {fn drop(self){}} fn main() -> usize {let a = First {}; let b = Second {}; 0}";
        let (_, events) = verify(source).unwrap().run_with_events().unwrap();
        assert_eq!(events, ["drop Second", "drop First"]);
    }
}
