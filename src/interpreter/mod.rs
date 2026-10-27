//! Bounded reference evaluator; construction requires a verified program.

use crate::{
    compiler::verify::VerifiedProgram,
    shared::planes::{Memory, PlaneId, Projection, Reference},
    syntax::{Expr, External, Function, Kind, MachineInt, Statement, Struct, Type},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

mod atomic;
mod blocks;
mod compat;
mod ownership;
mod type_match;

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Union(Vec<Type>, Box<Value>),
    Shape(Box<Type>),
    Int(i128),
    Nat(i128),
    Bool(bool),
    // Shared evaluator metadata preserves empty-array types without making
    // snapshots copy type trees. Native arrays have no metadata header.
    Array(Arc<Type>, Vec<Value>),
    Record(String, BTreeMap<String, Value>),
    Unit,
    Ref(Box<Type>, Reference, Vec<Projection>),
    Unique(Box<Type>, Reference),
    Shared(Box<Type>, crate::shared::planes::OwnedReference),
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
            Value::Union(_, value) => pending.push(value),
            Value::Array(_, items) => pending.extend(items),
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
            Self::Union(_, value) => value.fmt(f),
            Self::Shape(_) => write!(f, "<shape>"),
            Self::Int(n) | Self::Nat(n) | Self::Machine(_, n) => write!(f, "{n}"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Array(_, items) => {
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
            Self::Unique(_, _) => write!(f, "<owned plane>"),
            Self::Shared(_, _) => write!(f, "<owning reference>"),
        }
    }
}

impl Value {
    fn matches_type(&self, expected: &Type) -> Result<bool> {
        match (self, expected) {
            (Self::Array(actual, items), Type::Array(element, count)) => {
                if crate::syntax::constant_extent(count)
                    && items.len() != crate::compiler::layout::array_length(count)?
                    || !type_match::same_runtime_type(actual, element)?
                {
                    return Ok(false);
                }
                items
                    .iter()
                    .try_fold(true, |same, value| Ok(same && value.matches_type(element)?))
            }
            (Self::Unique(actual, _), Type::Unique(expected))
            | (Self::Shared(actual, _), Type::Shared(expected))
            | (Self::Ref(actual, _, _), Type::Ref(expected))
            | (Self::Shape(actual), Type::Shape(expected)) => {
                type_match::same_runtime_type(actual, expected)
            }
            _ => Ok(self.hint().as_ref() == Some(expected)),
        }
    }
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
            Self::Union(members, _) => Some(Type::Union(members.clone())),
            Self::Shape(inner) => Some(Type::Shape(inner.clone())),
            Self::Int(_) => Some(Type::Int),
            Self::Nat(_) => Some(Type::Nat),
            Self::Bool(_) => Some(Type::Bool),
            Self::Record(n, _) => Some(Type::Named(n.clone())),
            Self::Ref(t, _, _) => Some(Type::Ref(t.clone())),
            Self::Unique(t, _) => Some(Type::Unique(t.clone())),
            Self::Shared(t, _) => Some(Type::Shared(t.clone())),
            Self::Unit => Some(Type::Unit),
            Self::Machine(t, _) => Some(Type::Machine(*t)),
            Self::Array(element, items) => Some(Type::Array(
                Box::new((**element).clone()),
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
            Kind::Type(_) | Kind::Generic { .. } => None,
            Kind::Bytes(bytes) => Some(Type::bytes(bytes.len(), e.line)),
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Constant(t, _) => Some(Type::Machine(*t)),
            Kind::Name(n) => env.get(n).and_then(Value::hint),
            Kind::Record(n, _) => Some(Type::Named(n.clone())),
            Kind::Unary(op, x) if op == "&" => self.hint(x, env).map(|t| Type::Ref(Box::new(t))),
            Kind::Unary(op, x) if op == "*" => match self.hint(x, env)?.pointer_member()? {
                Type::Ref(t) | Type::Unique(t) | Type::Shared(t) => Some(*t.clone()),
                _ => None,
            },
            Kind::Unary(_, x) => self.hint(x, env),
            Kind::Call(name, _) if MachineInt::parse(name).is_some() => {
                MachineInt::parse(name).map(Type::Machine)
            }
            Kind::Call(name, args) if name == "shape" && args.len() == 1 => {
                args[0].literal_type().map(|ty| Type::Shape(Box::new(ty)))
            }
            Kind::Call(name, args) if name == "alloc" && args.len() == 1 => {
                self.hint(&args[0], env).map(|t| Type::Unique(Box::new(t)))
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
            Kind::Block(_, tail) => self.hint(tail, env),
            Kind::Call(n, _) => self
                .functions
                .iter()
                .find(|f| f.name == *n)
                .map(|f| f.ret.clone()),
            _ => None,
        }
    }

    fn statement(
        &mut self,
        statement: &Statement,
        env: &mut BTreeMap<String, Value>,
    ) -> Result<()> {
        let start = self.temporaries.len();
        match statement {
            Statement::While {
                condition, body, ..
            } => {
                let names = body
                    .iter()
                    .flat_map(|s| s.runtime_bindings(self.structs))
                    .map(str::to_owned)
                    .collect::<Vec<_>>();
                while self
                    .scoped_expr(condition, env, Some(&Type::Bool))?
                    .boolean()?
                {
                    for item in body {
                        self.statement(item, env)?;
                    }
                    for name in names.iter().rev() {
                        let value = if let Some(plane) = self.roots.remove(name) {
                            self.memory.take(plane).ok()
                        } else {
                            env.get(name)
                                .map(|value| copy_value(value, &mut self.fuel))
                                .transpose()?
                        };
                        if let Some(value) = value {
                            self.drop_value(value)?;
                        }
                        env.remove(name);
                    }
                }
            }
            Statement::Destructure {
                record,
                fields,
                value,
            } => {
                let Value::Record(_, mut values) =
                    self.expr(value, env, Some(&Type::Named(record.clone())))?
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
            Statement::Assign { target, value } => self.assign(target, value, env)?,
            Statement::Update { body, .. } => {
                let mut locals = Vec::new();
                for update in body {
                    match update {
                        Statement::Assign { target, value } => self.assign(target, value, env)?,
                        Statement::Let { name, ty, value } => {
                            let value = self.expr(value, env, ty.as_ref())?;
                            env.insert(name.clone(), value);
                            locals.push(name.clone());
                        }
                        Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => {}
                        Statement::Effect(expression) => {
                            let value = self.expr(expression, env, None)?;
                            self.drop_value(value)?;
                        }
                        _ => return Err("unverified operation in update".into()),
                    }
                    self.finish_temporaries(start)?;
                }
                for name in locals.into_iter().rev() {
                    if let Some(id) = self.roots.remove(&name) {
                        self.memory.take(id)?;
                    }
                    env.remove(&name);
                }
            }
            Statement::Effect(e) => {
                let value = self.expr(e, env, None)?;
                self.drop_value(value)?;
            }
            Statement::Ideal(_) | Statement::Fact { .. } | Statement::Proof { .. } => {}
            Statement::Let { name, ty, value } => {
                let v = self.expr(value, env, ty.as_ref())?;
                env.insert(name.clone(), v);
            }
        }
        self.finish_temporaries(start)
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
        match f.external {
            Some(External::Syscall(_)) => {
                return Err("external syscalls require a native executable; use build".into())
            }
            Some(External::CompareExchange64) => return self.compare_exchange64(actuals),
            None => {}
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
            self.statement(statement, &mut env)?;
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

    fn value_is_move_only(&self, value: &Value) -> bool {
        match value {
            Value::Union(_, _) | Value::Shape(_) => true,
            Value::Unique(..) => true,
            Value::Shared(..) => !crate::shared::target::native()
                .is_ok_and(|target| target.is_copy(&Type::Shared(Box::new(Type::Unit)))),
            Value::Record(n, _) => crate::shared::ownership::is_move_only(
                &Type::Named(n.clone()),
                self.structs,
                self.drops,
            ),
            Value::Array(element, _) => {
                crate::shared::ownership::is_move_only(element, self.structs, self.drops)
            }
            Value::Machine(_, _) | Value::Bool(_) | Value::Unit | Value::Ref(..) => {
                value.hint().is_some_and(|ty| {
                    crate::shared::ownership::is_move_only(&ty, self.structs, self.drops)
                })
            }
            _ => false,
        }
    }

    fn drop_value(&mut self, value: Value) -> Result<()> {
        if matches!(value, Value::Union(_, _)) {
            return Err("uneliminated raw union reached runtime cleanup".into());
        }
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
            Value::Shared(_, owner) => {
                self.memory.release_owner(owner)?;
            }
            Value::Unique(_, reference) => {
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
            Value::Array(_, items) => {
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
        // Lexical expression scopes share stored outer bindings. Materialize
        // only an assigned root so its update is visible outside a local env.
        let assigned_root = root_name(target)?;
        if !self.roots.contains_key(&assigned_root) {
            let value = copy_value(
                env.get(&assigned_root).ok_or("unknown assignment target")?,
                &mut self.fuel,
            )?;
            let plane = self.memory.allocate(value)?;
            self.roots.insert(assigned_root, plane);
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
        let old = if old_live {
            self.storage(target, env)?
        } else {
            old
        };
        if old_live && (self.value_is_move_only(&old) || Self::contains_shared(&old)) {
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
            let value = self.coerce_pointer(value, expected)?;
            let value = match (value, expected) {
                (Value::Union(_, value), Some(expected)) if !matches!(expected, Type::Union(_)) => {
                    if !value.matches_type(expected)? {
                        return Err(
                            "inactive raw union member: compiler/runtime disagreement".into()
                        );
                    }
                    *value
                }
                (value, Some(Type::Union(members))) if !matches!(value, Value::Union(_, _)) => {
                    Value::Union(members.clone(), Box::new(value))
                }
                (value, _) => value,
            };
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
            Kind::Type(_) | Kind::Generic { .. } => {
                Err("ideal type or generic template reached runtime execution".into())
            }
            Kind::Bytes(bytes) => {
                let element = MachineInt {
                    signed: false,
                    bits: 8,
                };
                Ok(Value::Array(
                    Arc::new(Type::Machine(element)),
                    bytes
                        .iter()
                        .map(|&byte| Value::Machine(element, i128::from(byte)))
                        .collect(),
                ))
            }
            Kind::FactAt(..) => Err("type facts are erased propositions".into()),
            Kind::Unit => Ok(Value::Unit),
            Kind::Constant(t, n) => Ok(Value::Machine(*t, *n)),
            Kind::Number(n) => Ok(match expected.and_then(Type::literal_numeric_member) {
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
                if self.value_is_move_only(&value) {
                    let (r, _) = self.location(e, env)?;
                    let id = self.memory.plane(r)?;
                    self.memory.take(id)?;
                }
                if self.value_is_move_only(&value) {
                    Ok(value)
                } else {
                    self.copy_pointer_read(value)
                }
            }
            Kind::Field(base, field) => {
                let Value::Record(_, fields) = self.storage(base, env)? else {
                    return Err("expected struct".into());
                };
                let value = fields
                    .get(field)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {field}"))?;
                self.copy_pointer_read(value)
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
                    let value = project(self.memory.read(r)?, &path)?.clone();
                    self.copy_pointer_read(value)
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
                let expected = expected
                    .and_then(|ty| crate::compiler::layout::literal_array_member(ty, items.len()));
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
                    .map(|items| Value::Array(Arc::new(element.unwrap_or(Type::Int)), items))
            }
            Kind::Index(..) => {
                let value = self.storage(e, env)?;
                self.copy_pointer_read(value)
            }
            Kind::Call(name, args) => {
                if name == "shape" {
                    let ty = args[0].literal_type().ok_or("shape requires a type")?;
                    return Ok(Value::Shape(Box::new(ty)));
                }
                if let Some(target) = MachineInt::parse(name) {
                    let [argument] = args.as_slice() else {
                        return Err("integer conversion requires one argument".into());
                    };
                    let source = self.hint(argument, env).unwrap_or(Type::Machine(target));
                    let value = self.expr(argument, env, Some(&source))?.number()?;
                    let (low, high) = target.bounds();
                    if !(low..=high).contains(&value) {
                        return Err("integer conversion outside its proved range".into());
                    }
                    return Ok(Value::Machine(target, value));
                }
                if name == "alloc" && args.len() == 2 {
                    let count_type = Type::Machine(MachineInt::parse("usize").unwrap());
                    let count =
                        usize::try_from(self.expr(&args[0], env, Some(&count_type))?.number()?)
                            .map_err(|_| "invalid allocation count")?;
                    let hint = match expected {
                        Some(Type::Unique(inner) | Type::Shared(inner)) => match inner.as_ref() {
                            Type::Array(element, _) => Some(element.as_ref()),
                            _ => None,
                        },
                        _ => None,
                    };
                    let initial = self.expr(&args[1], env, hint)?;
                    let element = hint
                        .cloned()
                        .or_else(|| initial.hint())
                        .ok_or("missing allocation element type")?;
                    let size = crate::compiler::layout::of(&element, self.structs)?.size;
                    if count as u128 * size as u128
                        > crate::compiler::layout::MAX_ALLOCATION_BYTES as u128
                    {
                        return Err("allocation exceeds target addressable object range".into());
                    }
                    // The evaluator materializes cells; reject before reserving
                    // host memory if even the minimum work exceeds its fuel.
                    if count > self.fuel {
                        return Err("execution value-work limit reached before allocation".into());
                    }
                    let mut items = Vec::new();
                    items
                        .try_reserve_exact(count)
                        .map_err(|_| "interpreter allocation failed")?;
                    for _ in 0..count {
                        items.push(copy_value(&initial, &mut self.fuel)?);
                    }
                    let ty = Type::Array(
                        Box::new(element.clone()),
                        Box::new(Expr {
                            kind: Kind::Number(count as i128),
                            line: e.line,
                        }),
                    );
                    let plane = self
                        .memory
                        .allocate(Value::Array(Arc::new(element), items))?;
                    return Ok(Value::Unique(Box::new(ty), self.memory.borrow(plane)?));
                }
                if name == "alloc" {
                    let hint = match expected {
                        Some(Type::Unique(inner) | Type::Shared(inner)) => Some(inner.as_ref()),
                        _ => None,
                    };
                    let value = self.expr(&args[0], env, hint)?;
                    let ty = hint
                        .cloned()
                        .or_else(|| value.hint())
                        .ok_or("missing allocation payload type")?;
                    let plane = self.memory.allocate(value)?;
                    return Ok(Value::Unique(Box::new(ty), self.memory.borrow(plane)?));
                }
                if matches!(name.as_str(), "move" | "drop" | "leak") {
                    let (r, path) = self.location(&args[0], env)?;
                    if !path.is_empty() {
                        return Err("cannot move partial plane".into());
                    }
                    let id = self.memory.plane(r)?;
                    let value = self.memory.take(id)?;
                    if name == "leak" {
                        self.leak_value(value)?;
                        return Ok(Value::Unit);
                    }
                    return if name == "drop" {
                        if matches!(value, Value::Shared(..)) {
                            return Err(
                                "drop requires unique(T); promote the shared pointer or leak it"
                                    .into(),
                            );
                        }
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
                let supplied = function.supplied_parameters(args.len())?;
                let values = args
                    .iter()
                    .zip(supplied)
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
            Kind::Block(body, tail) => self.block_value(body, tail, env, expected),
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
                let pointer = match self.storage(x, env)? {
                    Value::Union(_, payload) => *payload,
                    value => value,
                };
                let (r, p) = match pointer {
                    Value::Ref(_, r, p) => (r, p),
                    Value::Unique(_, r) => (r, Vec::new()),
                    Value::Shared(_, owner) => (self.memory.borrow_owned(owner)?, Vec::new()),
                    _ => return Err("expected reference or owned plane".into()),
                };
                self.memory.read(r)?;
                Ok((r, p))
            }
            Kind::Bytes(_) | Kind::Record(..) | Kind::Call(..) | Kind::If(..) | Kind::Block(..) => {
                let value = self.expr(e, env, None)?;
                if !matches!(value, Value::Record(..)) && !matches!(e.kind, Kind::Bytes(_)) {
                    return Err("temporary borrows require a record value".into());
                }
                let ty = value.hint().ok_or("temporary has no type")?;
                let plane = self.memory.allocate(value)?;
                let reference = self.memory.borrow(plane)?;
                self.temporaries
                    .push(Value::Unique(Box::new(ty), reference));
                Ok((reference, Vec::new()))
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
                let Value::Array(_, items) = self.storage(base, env)? else {
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
                if self.value_is_move_only(&value) || Self::contains_shared(&value) {
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
        (Value::Array(at, a), Value::Array(bt, b)) => {
            crate::compiler::layout::same_type(at, bt).unwrap_or(false)
                && a.len() == b.len()
                && a.iter().zip(b).all(|(v, w)| same_layout(v, w))
        }
        (Value::Int(_), Value::Int(_))
        | (Value::Nat(_), Value::Nat(_))
        | (Value::Bool(_), Value::Bool(_))
        | (Value::Ref(..), Value::Ref(..))
        | (Value::Unique(..), Value::Unique(..))
        | (Value::Shared(..), Value::Shared(..))
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
        (Projection::Index(i), Value::Array(_, items)) => {
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
        (Projection::Index(i), Value::Array(_, items)) => {
            items.get_mut(*i).ok_or("index out of bounds")?
        }
        _ => return Err("invalid reference projection".into()),
    };
    replace_projection(value, &path[1..], new)
}

/// Execute the checked program's main function with bounded interpretation.
pub fn run(program: &VerifiedProgram) -> Result<Value> {
    run_with_events(program).map(|(value, _)| value)
}

/// Return a detached result snapshot and cleanup trace for debugging.
pub fn run_with_events(program: &VerifiedProgram) -> Result<(Value, Vec<String>)> {
    program.check_entry()?;
    crate::shared::worker::run("evergreen-evaluator", || evaluate(program))
}

fn evaluate(program: &VerifiedProgram) -> Result<(Value, Vec<String>)> {
    let mut evaluator = Evaluator {
        functions: &program.functions,
        structs: &program.structs,
        fuel: 100_000,
        depth: 0,
        expression_depth: 0,
        memory: Memory::default(),
        roots: BTreeMap::new(),
        drops: &program.drops,
        events: Vec::new(),
        temporaries: Vec::new(),
    };
    let value = evaluator.call("main", vec![])?;
    let snapshot = copy_value(&value, &mut evaluator.fuel)?;
    evaluator.drop_value(snapshot)?;
    Ok((value, evaluator.events))
}

#[cfg(test)]
mod tests;
