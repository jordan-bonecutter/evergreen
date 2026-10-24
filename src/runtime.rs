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
    Plane(Box<Type>, Reference),
    Machine(MachineInt, i128),
}
// Charge aggregate snapshots before cloning their expanded representation.
// Handles do not recursively copy the plane they point to.
fn charge_value(value: &Value, fuel: &mut usize) -> Result<()> {
    let mut pending = vec![value];
    let mut cost = 0usize;
    while let Some(value) = pending.pop() {
        cost += 1;
        if cost > *fuel {
            return Err("execution value-work limit reached (100000 steps and nodes)".into());
        }
        match value {
            Value::Array(items) => pending.extend(items),
            Value::Record(_, fields) => pending.extend(fields.values()),
            _ => {}
        }
    }
    *fuel -= cost;
    Ok(())
}
fn copy_value(value: &Value, fuel: &mut usize) -> Result<Value> {
    charge_value(value, fuel)?;
    Ok(value.clone())
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
            Self::Plane(_, _) => write!(f, "<owned plane>"),
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
            Self::Plane(t, _) => Some(Type::Plane(t.clone())),
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
    expression_depth: usize,
    memory: Memory<Value>,
    roots: BTreeMap<String, PlaneId>,
    drops: &'a BTreeSet<String>,
    events: Vec<String>,
    temporaries: Vec<Value>,
}
impl Evaluator<'_> {
    fn finish_temporaries(&mut self, start: usize) -> Result<()> {
        let values = self.temporaries.split_off(start);
        for value in values.into_iter().rev() {
            self.drop_value(value)?;
        }
        Ok(())
    }
    fn scoped_expr(
        &mut self,
        e: &Expr,
        env: &BTreeMap<String, Value>,
        expected: Option<&Type>,
    ) -> Result<Value> {
        let start = self.temporaries.len();
        let value = self.expr(e, env, expected)?;
        self.finish_temporaries(start)?;
        Ok(value)
    }
    fn hint(&self, e: &Expr, env: &BTreeMap<String, Value>) -> Option<Type> {
        match &e.kind {
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Constant(t, _) => Some(Type::Machine(*t)),
            Kind::Name(n) => env.get(n).and_then(Value::hint),
            Kind::Record(n, _) => Some(Type::Named(n.clone())),
            Kind::Unary(op, x) if op == "&" => self.hint(x, env).map(|t| Type::Ref(Box::new(t))),
            Kind::Unary(op, x) if op == "*" => {
                if let Some(Type::Ref(t) | Type::Plane(t)) = self.hint(x, env) {
                    Some(*t)
                } else {
                    None
                }
            }
            Kind::Unary(_, x) => self.hint(x, env),
            Kind::Call(name, args) if name == "alloc" && args.len() == 1 => {
                self.hint(&args[0], env).map(|t| Type::Plane(Box::new(t)))
            }
            Kind::Index(base, _) => match self.hint(base, env)? {
                Type::Array(element, _) => Some(*element),
                _ => None,
            },
            Kind::Field(base, field) => {
                fn stored<'a>(e: &Expr, env: &'a BTreeMap<String, Value>) -> Option<&'a Value> {
                    match &e.kind {
                        Kind::Name(n) => env.get(n),
                        Kind::Field(base, field) => match stored(base, env)? {
                            Value::Record(_, fields) => fields.get(field),
                            _ => None,
                        },
                        _ => None,
                    }
                }
                if let Some(Value::Record(_, fields)) = stored(base, env) {
                    return fields.get(field).and_then(Value::hint);
                }
                let Type::Named(name) = self.hint(base, env)? else {
                    return None;
                };
                self.structs
                    .get(&name)?
                    .fields
                    .iter()
                    .find(|(n, _)| n == field)
                    .map(|(_, t)| t.clone())
            }
            Kind::Binary(op, _, _)
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "=>"
                ) =>
            {
                Some(Type::Bool)
            }
            Kind::Binary(_, a, b) => self.hint(a, env).or_else(|| self.hint(b, env)),
            Kind::If(_, a, b) => self.hint(a, env).or_else(|| self.hint(b, env)),
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
            .ok_or("unknown function")?;
        if f.ideal {
            return Err("ideal functions have no runtime body".into());
        }
        if f.params
            .iter()
            .filter(|(n, _)| !f.ideal_params.contains(n))
            .count()
            != actuals.len()
        {
            return Err("argument count mismatch".into());
        }
        let mut env: BTreeMap<String, Value> = f
            .params
            .iter()
            .filter(|(n, _)| !f.ideal_params.contains(n))
            .map(|(n, _)| n.clone())
            .zip(actuals)
            .collect();
        let saved_roots = std::mem::take(&mut self.roots);
        let saved_temporaries = std::mem::take(&mut self.temporaries);
        self.depth += 1;
        // Contracts were discharged by the verifier and are erased here.
        for statement in &f.body {
            match statement {
                Statement::Destructure {
                    record,
                    fields,
                    value,
                } => {
                    let Value::Record(_, mut values) =
                        self.expr(value, &env, Some(&Type::Named(record.clone())))?
                    else {
                        return Err("record pattern requires a record".into());
                    };
                    for (field, name) in fields {
                        if self.structs[record].ideal_fields.contains(field) {
                            continue;
                        }
                        env.insert(
                            name.clone(),
                            values.remove(field).ok_or("missing pattern field")?,
                        );
                    }
                }
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
                            Statement::Ideal(_)
                            | Statement::Fact { .. }
                            | Statement::Proof { .. } => {}
                            Statement::Effect(expression) => {
                                let value = self.expr(expression, &env, None)?;
                                self.drop_value(value)?;
                            }
                            _ => return Err("unverified operation in update".into()),
                        }
                        self.finish_temporaries(0)?;
                    }
                    for name in locals.into_iter().rev() {
                        if let Some(id) = self.roots.remove(&name) {
                            self.memory.take(id)?;
                        }
                        env.remove(&name);
                    }
                }
                Statement::Effect(e) => {
                    let value = self.expr(e, &env, None)?;
                    self.drop_value(value)?;
                }
                Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => {}
                Statement::Let { name, ty, value } => {
                    let v = self.expr(value, &env, ty.as_ref())?;
                    env.insert(name.clone(), v);
                }
            }
            self.finish_temporaries(0)?;
        }
        let value = self.scoped_expr(&f.result, &env, Some(&f.ret))?;
        let mut names = f
            .params
            .iter()
            .filter(|(n, _)| !f.ideal_params.contains(n))
            .map(|(n, _)| n.clone())
            .collect::<Vec<_>>();
        names.extend(f.body.iter().flat_map(|s| {
            s.runtime_bindings(self.structs)
                .into_iter()
                .map(str::to_owned)
        }));
        for name in names.into_iter().rev() {
            let live = if let Some(id) = self.roots.get(&name) {
                if self.memory.get(*id).is_err() {
                    continue;
                }
                self.memory.take(*id)?
            } else {
                copy_value(
                    env.get(&name).ok_or("unknown cleanup binding")?,
                    &mut self.fuel,
                )?
            };
            if name == "self" && f.drop_target.is_some() {
                self.drop_fields(live)?;
            } else {
                self.drop_value(live)?;
            }
        }
        self.roots = saved_roots;
        self.temporaries = saved_temporaries;
        self.depth -= 1;
        Ok(value)
    }

    fn value_is_affine(&self, value: &Value) -> bool {
        match value {
            Value::Plane(..) => true,
            Value::Record(n, _) => {
                crate::verify::is_affine(&Type::Named(n.clone()), self.structs, self.drops)
            }
            Value::Array(xs) => xs.iter().any(|v| self.value_is_affine(v)),
            _ => false,
        }
    }
    fn drop_value(&mut self, value: Value) -> Result<()> {
        self.fuel = self
            .fuel
            .checked_sub(1)
            .ok_or("execution value-work limit reached during cleanup")?;
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
            Value::Plane(_, reference) => {
                let plane = self.memory.plane(reference)?;
                let payload = self.memory.take(plane)?;
                self.drop_value(payload)?;
            }
            Value::Record(name, mut fields) => {
                let order = self
                    .structs
                    .get(&name)
                    .ok_or("unknown drop layout")?
                    .runtime_fields()
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
        if target.indirect_place() {
            let (r, path) = self.location(target, env)?;
            let old = copy_value(project(self.memory.read(r)?, &path)?, &mut self.fuel)?;
            let new = self.expr(value, env, old.hint().as_ref())?;
            let id = self.memory.plane(r)?;
            let mut root = copy_value(self.memory.read(r)?, &mut self.fuel)?;
            replace_projection(&mut root, &path, new)?;
            let replace_plane = !same_layout(&old, project(&root, &path)?);
            self.memory
                .write(id, copy_value(&root, &mut self.fuel)?, replace_plane)?;
            for (n, p) in &self.roots {
                if *p == id {
                    env.insert(n.clone(), copy_value(&root, &mut self.fuel)?);
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
            let value = self
                .roots
                .get(n)
                .and_then(|id| self.memory.get(*id).ok())
                .or_else(|| env.get(n))
                .ok_or("unknown assignment target")?;
            copy_value(value, &mut self.fuel)?
        } else {
            self.storage(target, env)?
        };
        let new = self.expr(value, env, old.hint().as_ref())?;
        let old_live = self
            .roots
            .get(&root_name(target)?)
            .is_none_or(|id| self.memory.get(*id).is_ok());
        if old_live && self.value_is_affine(&old) {
            let old_copy = copy_value(&old, &mut self.fuel)?;
            self.drop_value(old_copy)?;
        }
        let replace_plane = !same_layout(&old, &new);
        let mut fields = Vec::new();
        let root = path(target, &mut fields)?;
        if !fields.is_empty() && !old_live {
            return Err("field assignment cannot restore a consumed owner's shape".into());
        }
        if let Some(live) = self
            .roots
            .get(&root)
            .and_then(|id| self.memory.get(*id).ok())
        {
            let live = copy_value(live, &mut self.fuel)?;
            env.insert(root.clone(), live);
        }
        replace(
            env.get_mut(&root).ok_or("unknown assignment target")?,
            &fields,
            new,
        )?;
        if let Some(id) = self.roots.get(&root) {
            self.memory.write(
                *id,
                copy_value(
                    env.get(&root).ok_or("unknown assignment root")?,
                    &mut self.fuel,
                )?,
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
        if self.expression_depth >= 256 {
            return Err("execution expression depth limit reached (256)".into());
        }
        self.fuel -= 1;
        self.expression_depth += 1;
        let result = self.inner(e, env, expected).and_then(|value| {
            charge_value(&value, &mut self.fuel)?;
            Ok(value)
        });
        self.expression_depth -= 1;
        result.map_err(|s| {
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
            Kind::FactAt(..) => Err("type facts are erased propositions".into()),
            Kind::Unit => Ok(Value::Unit),
            Kind::Constant(t, n) => Ok(Value::Machine(*t, *n)),
            Kind::Number(n) => Ok(match expected {
                Some(Type::Nat) => Value::Nat(*n),
                Some(Type::Machine(t)) => Value::Machine(*t, *n),
                _ => Value::Machine(MachineInt::parse("isize").expect("isize type"), *n),
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
                if self.value_is_affine(&value) {
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
                let def = self.structs.get(name).ok_or("unknown struct")?;
                let mut fields = BTreeMap::new();
                for (n, e) in entries {
                    if def.ideal_fields.contains(n) {
                        continue;
                    }
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
                        .unwrap_or(Type::Machine(
                            MachineInt::parse("isize").expect("isize type"),
                        ));
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
            Kind::Binary(op, a, b) if matches!(op.as_str(), "&&" | "||" | "=>") => {
                let a = self.expr(a, env, Some(&Type::Bool))?.boolean()?;
                let b = self.expr(b, env, Some(&Type::Bool))?.boolean()?;
                Ok(Value::Bool(match op.as_str() {
                    "&&" => a && b,
                    "=>" => !a || b,
                    _ => a || b,
                }))
            }
            Kind::Binary(op, a, b) => {
                let ty = if matches!(op.as_str(), "+" | "-" | "*") {
                    expected.cloned()
                } else {
                    None
                }
                .or_else(|| self.hint(a, env))
                .or_else(|| self.hint(b, env))
                .unwrap_or(Type::Machine(
                    MachineInt::parse("isize").expect("isize type"),
                ));
                if matches!(ty, Type::Ref(_)) && matches!(op.as_str(), "==" | "!=") {
                    let Value::Ref(_, a, a_path) = self.expr(a, env, Some(&ty))? else {
                        return Err("reference equality requires reference operands".into());
                    };
                    let Value::Ref(_, b, b_path) = self.expr(b, env, Some(&ty))? else {
                        return Err("reference equality requires reference operands".into());
                    };
                    project(self.memory.read(a)?, &a_path)?;
                    project(self.memory.read(b)?, &b_path)?;
                    let same = a == b && a_path == b_path;
                    return Ok(Value::Bool(if op == "==" { same } else { !same }));
                }
                if ty == Type::Bool && matches!(op.as_str(), "==" | "!=") {
                    let a = self.expr(a, env, Some(&Type::Bool))?.boolean()?;
                    let b = self.expr(b, env, Some(&Type::Bool))?.boolean()?;
                    return Ok(Value::Bool(if op == "==" { a == b } else { a != b }));
                }
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
                        .or(Some(Type::Machine(
                            MachineInt::parse("isize").expect("isize type"),
                        )))
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
                if name == "alloc" {
                    let hint = match expected {
                        Some(Type::Plane(inner)) => Some(inner.as_ref()),
                        _ => None,
                    };
                    let value = self.expr(&args[0], env, hint)?;
                    let ty = hint
                        .cloned()
                        .or_else(|| value.hint())
                        .ok_or("missing allocation payload type")?;
                    let plane = self.memory.allocate(value)?;
                    return Ok(Value::Plane(Box::new(ty), self.memory.borrow(plane)?));
                }
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
                let function = self
                    .functions
                    .iter()
                    .find(|f| f.name == *name)
                    .ok_or("unknown function")?;
                let values = args
                    .iter()
                    .zip(&function.params)
                    .filter(|(_, (name, _))| !function.ideal_params.contains(name))
                    .map(|(x, (_, t))| self.expr(x, env, Some(t)))
                    .collect::<Result<Vec<_>>>()?;
                self.call(name, values)
            }
            Kind::If(condition, yes, no) => {
                if self
                    .scoped_expr(condition, env, Some(&Type::Bool))?
                    .boolean()?
                {
                    self.scoped_expr(yes, env, expected)
                } else {
                    self.scoped_expr(no, env, expected)
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
                    let v = copy_value(env.get(n).ok_or("unknown place")?, &mut self.fuel)?;
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
                let (r, p) = match self.storage(x, env)? {
                    Value::Ref(_, r, p) => (r, p),
                    Value::Plane(_, r) => (r, Vec::new()),
                    _ => return Err("expected reference or owned plane".into()),
                };
                self.memory.read(r)?;
                Ok((r, p))
            }
            _ => Err("expected referenceable place".into()),
        }
    }

    fn storage(&mut self, e: &Expr, env: &BTreeMap<String, Value>) -> Result<Value> {
        let value = self.storage_inner(e, env)?;
        charge_value(&value, &mut self.fuel)?;
        Ok(value)
    }
    fn storage_inner(&mut self, e: &Expr, env: &BTreeMap<String, Value>) -> Result<Value> {
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
            _ => {
                let value = self.expr(e, env, None)?;
                if self.value_is_affine(&value) {
                    self.temporaries.push(copy_value(&value, &mut self.fuel)?);
                }
                Ok(value)
            }
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
        | (Value::Plane(..), Value::Plane(..))
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
        self.check_entry()?;
        crate::bounded::run("evergreen-evaluator", || self.evaluate())
    }

    fn evaluate(&self) -> Result<(Value, Vec<String>)> {
        let mut evaluator = Evaluator {
            functions: &self.functions,
            structs: &self.structs,
            fuel: 100_000,
            depth: 0,
            expression_depth: 0,
            memory: Memory::default(),
            roots: BTreeMap::new(),
            drops: &self.drops,
            events: Vec::new(),
            temporaries: Vec::new(),
        };
        let value = evaluator.call("main", vec![])?;
        let snapshot = copy_value(&value, &mut evaluator.fuel)?;
        evaluator.drop_value(snapshot)?;
        Ok((value, evaluator.events))
    }
}

#[cfg(test)]
mod tests {
    use super::{copy_value, Value};
    #[test]
    fn aggregate_copy_work_is_charged_before_cloning() {
        let value = Value::Array(vec![Value::Bool(true); 64]);
        let mut fuel = 64;
        assert!(copy_value(&value, &mut fuel)
            .unwrap_err()
            .contains("value-work"));
        assert_eq!(fuel, 64);
        fuel = 65;
        assert_eq!(copy_value(&value, &mut fuel).unwrap(), value);
        assert_eq!(fuel, 0);
        let values = vec!["1"; 2048].join(",");
        let source = format!("fn repeat(n: usize, data: [usize; 2048]) -> usize where(data[0] == 1) ensures(result == 1) decreases(n) {{if n == 0 {{data[0]}} else {{repeat(n - 1, data)}}}} fn main() -> usize {{let data: [usize; 2048] = [{values}]; repeat(40, data)}}");
        let program = verify(&source).unwrap();
        let error = program.run().unwrap_err();
        assert!(error.contains("value-work"), "{error}");
    }

    #[test]
    fn unused_owned_temporaries_are_dropped_at_the_statement() {
        let declarations = include_str!("../examples/borrowed_temporaries.evg")
            .split("fn main()")
            .next()
            .unwrap();
        let proof_only = format!("{declarations}\nfn main() -> usize {{fact unused_false = first().tag == 0; proof erased: First {{tag: 1}}.tag == 1; 42}}");
        let (_, events) = verify(&proof_only).unwrap().run_with_events().unwrap();
        assert!(events.is_empty());
        let (value, events) = verify(include_str!("../examples/borrowed_temporaries.evg"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(value.to_string(), "6");
        assert_eq!(
            events,
            [
                "drop Second",
                "drop First",
                "drop First",
                "drop Second",
                "drop First",
                "drop Third"
            ]
        );
        let (_, events) = verify(include_str!("../examples/temporary_cleanup.evg"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(events, ["drop Second", "drop First", "drop First"]);
        let declarations = "type Resource struct {} impl Drop for Resource {fn drop(self){}} fn make() -> Resource {Resource {}}";
        for body in [
            "Resource {}; 0",
            "[Resource {}]; 0",
            "make(); 0",
            "let r = Resource {}; move(r); 0",
            "let r = Resource {}; drop(r); 0",
            "let r = Resource {}; if true {move(r)} else {move(r)}; 0",
        ] {
            let (_, events) = verify(&format!("{declarations}\nfn main() -> usize {{{body}}}"))
                .unwrap()
                .run_with_events()
                .unwrap();
            assert_eq!(events, ["drop Resource"], "{body}");
        }
        let declarations = "type First struct {} impl Drop for First {fn drop(self){}} type Second struct {} impl Drop for Second {fn drop(self){}}";
        let (_, events) = verify(&format!(
            "{declarations}\nfn main() -> usize {{let later = Second {{}}; First {{}}; 0}}"
        ))
        .unwrap()
        .run_with_events()
        .unwrap();
        assert_eq!(events, ["drop First", "drop Second"]);
    }

    use crate::verify::verify;
    #[test]
    fn executes_verified_calls_arrays_and_branches() {
        let s = "fn abs(n: isize) -> isize where (n > isize::MIN) ensures (result >= 0) { if n >= 0 { n } else { -n } } fn main() -> isize { let a: [isize; 2] = [-4, 8]; abs(a[0]) }";
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
    fn recursive_execution_fails_before_exhausting_the_host_stack() {
        let source = "fn count(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {count(n - 1) + 1}} fn main() -> usize {count(1000)}";
        let error = verify(source).unwrap().run().unwrap_err();
        assert!(
            error.contains("execution expression depth limit")
                || error.contains("execution call depth limit"),
            "{error}"
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
    fn ideal_math_is_never_executed_by_the_runtime() {
        let source = format!(
            "ideal fn double(n: int) -> int {{ n + n }} ideal fn main() -> int {{ double({}) }}",
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
        let prefix = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self) {proof valid: self.tag == 7;}} ";
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

    #[test]
    fn destructured_owned_fields_are_cleaned_up_once() {
        let source = "type First struct {} impl Drop for First {fn drop(self){}} type Second struct {} impl Drop for Second {fn drop(self){}} type Pair struct {left: First, right: Second} fn main() -> usize {let p = Pair {left: First {}, right: Second {}}; let Pair {left, right} = p; 0}";
        let (_, events) = verify(source).unwrap().run_with_events().unwrap();
        assert_eq!(events, ["drop Second", "drop First"]);
        let source = source.replace(
            "let Pair {left, right} = p;",
            "let Pair {left, right} = p; drop(left);",
        );
        let (_, events) = verify(&source).unwrap().run_with_events().unwrap();
        assert_eq!(events, ["drop First", "drop Second"]);
    }
}
