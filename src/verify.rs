//! Internal elaboration and verification-condition generation.
use crate::{
    kernel::{self, Linear},
    memory::{Memory, PlaneId, Projection, Reference},
    syntax::{self, Expr, Function, Kind, MachineInt, Struct, Type},
};
use std::collections::BTreeMap;

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
enum Formula {
    True,
    False,
    Ge(Linear),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
}
impl Formula {
    fn and(self, other: Self) -> Self {
        Self::And(Box::new(self), Box::new(other))
    }
    fn or(self, other: Self) -> Self {
        Self::Or(Box::new(self), Box::new(other))
    }
    fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
}

#[derive(Clone, Debug)]
enum Ty {
    Int,
    Nat,
    Bool,
    Unit,
    Ref(Box<Ty>),
    Machine(MachineInt),
    Array(Box<Ty>, Linear),
    Record(String),
}
#[derive(Clone, Debug)]
enum Symbol {
    Number(Ty, Linear),
    Bool(Formula),
    Array {
        element: Box<Ty>,
        len: Linear,
        items: Option<Vec<Symbol>>,
        identity: String,
    },
    Record(String, BTreeMap<String, Symbol>),
    Unit,
    Ref(Box<Ty>, Reference, Vec<Projection>),
}
impl Symbol {
    fn ty(&self) -> Ty {
        match self {
            Self::Number(t, _) => t.clone(),
            Self::Bool(_) => Ty::Bool,
            Self::Array { element, len, .. } => Ty::Array(element.clone(), len.clone()),
            Self::Record(name, _) => Ty::Record(name.clone()),
            Self::Unit => Ty::Unit,
            Self::Ref(t, _, _) => Ty::Ref(t.clone()),
        }
    }
    fn number(&self) -> Result<Linear> {
        if let Self::Number(_, n) = self {
            Ok(n.clone())
        } else {
            Err("expected an integer expression".into())
        }
    }
    fn proposition(&self) -> Result<Formula> {
        if let Self::Bool(p) = self {
            Ok(p.clone())
        } else {
            Err("expected a proposition or boolean".into())
        }
    }
}

fn project<'a>(value: &'a Symbol, path: &[Projection]) -> Result<&'a Symbol> {
    if path.is_empty() {
        return Ok(value);
    }
    let value = match (&path[0], value) {
        (Projection::Field(n), Symbol::Record(_, fields)) => {
            fields.get(n).ok_or("unknown reference field")?
        }
        (
            Projection::Index(i),
            Symbol::Array {
                items: Some(items), ..
            },
        ) => items.get(*i).ok_or("reference index out of bounds")?,
        _ => {
            return Err(
                "reference projection requires a known struct field or array element".into(),
            )
        }
    };
    project(value, &path[1..])
}
fn replace_projection(value: &mut Symbol, path: &[Projection], new: Symbol) -> Result<()> {
    if path.is_empty() {
        *value = new;
        return Ok(());
    }
    let value = match (&path[0], value) {
        (Projection::Field(n), Symbol::Record(_, fields)) => {
            fields.get_mut(n).ok_or("unknown reference field")?
        }
        (
            Projection::Index(i),
            Symbol::Array {
                items: Some(items), ..
            },
        ) => items.get_mut(*i).ok_or("reference index out of bounds")?,
        _ => return Err("invalid reference projection".into()),
    };
    replace_projection(value, &path[1..], new)
}

fn type_has_reference(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Ref(_) => true,
        Type::Array(t, _) => type_has_reference(t, structs),
        Type::Named(n) => structs
            .get(n)
            .is_some_and(|s| s.fields.iter().any(|(_, t)| type_has_reference(t, structs))),
        _ => false,
    }
}

/// Each path is a conjunction of inequalities. The path list is a disjunction.
fn extend(paths: &[Vec<Linear>], formula: &Formula, negated: bool) -> Result<Vec<Vec<Linear>>> {
    let result = match formula {
        Formula::True => {
            if negated {
                vec![]
            } else {
                paths.to_vec()
            }
        }
        Formula::False => {
            if negated {
                paths.to_vec()
            } else {
                vec![]
            }
        }
        Formula::Ge(value) => {
            let row = if negated {
                value.scale(-1)?.add(&Linear::number(-1))?
            } else {
                value.clone()
            };
            paths
                .iter()
                .map(|p| {
                    let mut p = p.clone();
                    p.push(row.clone());
                    p
                })
                .collect()
        }
        Formula::Not(p) => return extend(paths, p, !negated),
        Formula::And(a, b) | Formula::Or(a, b) => {
            let conjunction = matches!(formula, Formula::And(..)) != negated;
            if conjunction {
                extend(&extend(paths, a, negated)?, b, negated)?
            } else {
                let mut left = extend(paths, a, negated)?;
                left.extend(extend(paths, b, negated)?);
                left
            }
        }
    };
    if result.len() > 64 {
        return Err("verification path limit reached (64)".into());
    }
    Ok(result)
}

fn equal(a: &Linear, b: &Linear) -> Result<Formula> {
    Ok(Formula::Ge(a.sub(b)?).and(Formula::Ge(b.sub(a)?)))
}

struct Context<'a> {
    functions: &'a BTreeMap<String, Function>,
    structs: &'a BTreeMap<String, Struct>,
    env: BTreeMap<String, Symbol>,
    facts: BTreeMap<String, Formula>,
    paths: Vec<Vec<Linear>>,
    fresh: usize,
    obligations: usize,
    memory: Memory<Symbol>,
    roots: BTreeMap<String, PlaneId>,
    specification: bool,
    current: Option<String>,
    measure: Option<Linear>,
}

impl<'a> Context<'a> {
    fn new(
        functions: &'a BTreeMap<String, Function>,
        structs: &'a BTreeMap<String, Struct>,
    ) -> Self {
        Self {
            functions,
            structs,
            env: BTreeMap::new(),
            facts: BTreeMap::new(),
            paths: vec![vec![]],
            fresh: 0,
            obligations: 0,
            memory: Memory::default(),
            roots: BTreeMap::new(),
            specification: false,
            current: None,
            measure: None,
        }
    }
    fn fresh_name(&mut self) -> String {
        self.fresh += 1;
        format!("evg_{}", self.fresh)
    }
    fn assume(&mut self, p: &Formula) -> Result<()> {
        self.paths = extend(&self.paths, p, false)?;
        Ok(())
    }
    fn proposition(&mut self, e: &Expr) -> Result<Formula> {
        let saved = self.specification;
        self.specification = true;
        let result = self.eval(e, Some(&Ty::Bool)).and_then(|v| v.proposition());
        self.specification = saved;
        result
    }
    fn nonnegative(&mut self, e: &Expr, label: &str) -> Result<Linear> {
        let ty = self.hint(e).unwrap_or(Ty::Nat);
        if !matches!(ty, Ty::Int | Ty::Nat | Ty::Machine(_)) {
            return Err(format!("line {}: {label} must be an integer", e.line));
        }
        let n = self.eval(e, Some(&ty))?.number()?;
        self.prove(&Formula::Ge(n.clone()), label, e.line)?;
        Ok(n)
    }
    fn prove(&mut self, p: &Formula, label: &str, line: usize) -> Result<()> {
        self.obligations += 1;
        for path in extend(&self.paths, p, true)? {
            let certificate = kernel::solve(&path)
                .map_err(|e| format!("line {line}: cannot prove {label}: {e}"))?;
            kernel::check(&path, &certificate)?;
        }
        Ok(())
    }
    fn resolve(&mut self, t: &Type) -> Result<Ty> {
        match t {
            Type::Int => Ok(Ty::Int),
            Type::Nat => Ok(Ty::Nat),
            Type::Bool => Ok(Ty::Bool),
            Type::Machine(t) => Ok(Ty::Machine(*t)),
            Type::Unit => Ok(Ty::Unit),
            Type::Ref(t) => Ok(Ty::Ref(Box::new(self.resolve(t)?))),
            Type::Named(n) => {
                if !self.structs.contains_key(n) {
                    return Err(format!(
                        "unknown struct {n}; recursive types are not supported yet"
                    ));
                }
                Ok(Ty::Record(n.clone()))
            }
            Type::Array(element, len) => {
                let element = self.resolve(element)?;
                let saved_spec = self.specification;
                self.specification = true;
                let n = self.nonnegative(len, "nonnegative array length")?;
                self.specification = saved_spec;
                Ok(Ty::Array(Box::new(element), n))
            }
        }
    }
    fn compatible(&mut self, got: &Ty, expected: &Ty, line: usize) -> Result<()> {
        match (got, expected) {
            (Ty::Int, Ty::Int)
            | (Ty::Nat, Ty::Nat)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Unit, Ty::Unit) => Ok(()),
            (Ty::Ref(a), Ty::Ref(b)) => self.compatible(a, b, line),
            (Ty::Machine(a), Ty::Machine(b)) if a == b => Ok(()),
            (Ty::Record(a), Ty::Record(b)) if a == b => Ok(()),
            (Ty::Array(a, n), Ty::Array(b, m)) => {
                self.compatible(a, b, line)?;
                self.prove(&equal(n, m)?, "array length equality", line)
            }
            _ => Err(format!(
                "line {line}: type mismatch: expected {expected:?}, got {got:?}"
            )),
        }
    }
    fn arbitrary(&mut self, t: &Ty) -> Result<Symbol> {
        let name = self.fresh_name();
        match t {
            Ty::Machine(t) => {
                let n = Linear::variable(name);
                let (lo, hi) = t.bounds();
                self.assume(&Formula::Ge(n.sub(&Linear::number(lo))?))?;
                self.assume(&Formula::Ge(Linear::number(hi).sub(&n)?))?;
                Ok(Symbol::Number(Ty::Machine(*t), n))
            }
            Ty::Unit => Ok(Symbol::Unit),
            Ty::Ref(t) => {
                let v = self.arbitrary(t)?;
                let id = self.memory.allocate(v)?;
                Ok(Symbol::Ref(t.clone(), self.memory.borrow(id)?, vec![]))
            }
            Ty::Int => Ok(Symbol::Number(Ty::Int, Linear::variable(name))),
            Ty::Nat => {
                let n = Linear::variable(name);
                self.assume(&Formula::Ge(n.clone()))?;
                Ok(Symbol::Number(Ty::Nat, n))
            }
            Ty::Bool => {
                let n = Linear::variable(name);
                self.assume(&Formula::Ge(n.clone()))?;
                self.assume(&Formula::Ge(Linear::number(1).sub(&n)?))?;
                Ok(Symbol::Bool(equal(&n, &Linear::number(1))?))
            }
            Ty::Array(element, len) => Ok(Symbol::Array {
                element: element.clone(),
                len: len.clone(),
                items: None,
                identity: name,
            }),
            Ty::Record(name) => {
                let def = self.structs.get(name).cloned().ok_or("unknown struct")?;
                let saved = self.env.clone();
                let saved_roots = self.roots.clone();
                self.roots.clear();
                self.env.clear();
                let mut fields = BTreeMap::new();
                for (n, t) in &def.fields {
                    let t = self.resolve(t)?;
                    let v = self.arbitrary(&t)?;
                    fields.insert(n.clone(), v.clone());
                    self.env.insert(n.clone(), v);
                }
                let value = Symbol::Record(name.clone(), fields);
                self.env.insert("self".into(), value.clone());
                if let Some(p) = &def.invariant {
                    let p = self.proposition(p)?;
                    self.assume(&p)?;
                }
                self.env = saved;
                self.roots = saved_roots;
                Ok(value)
            }
        }
    }

    fn record_valid(&mut self, value: &Symbol, line: usize) -> Result<()> {
        let Symbol::Record(name, fields) = value else {
            return Ok(());
        };
        let def = self.structs.get(name).cloned().ok_or("unknown struct")?;
        if def.fields.len() != fields.len() {
            return Err(format!("line {line}: wrong fields for {name}"));
        }
        let saved = self.env.clone();
        let saved_roots = self.roots.clone();
        self.roots.clear();
        self.env.clear();
        for (n, t) in &def.fields {
            let v = fields
                .get(n)
                .ok_or_else(|| format!("line {line}: missing field {n}"))?;
            self.record_valid(v, line)?;
            let t = self.resolve(t)?;
            self.compatible(&v.ty(), &t, line)?;
            self.env.insert(n.clone(), v.clone());
        }
        self.env.insert("self".into(), value.clone());
        if let Some(p) = &def.invariant {
            let p = self.proposition(p)?;
            self.prove(&p, &format!("invariant of {name}"), line)?;
        }
        self.env = saved;
        self.roots = saved_roots;
        Ok(())
    }

    fn assign(&mut self, place: &Expr, value: &Expr) -> Result<()> {
        if matches!(&place.kind, Kind::Unary(op, _) if op == "*") {
            let (reference, fields) = self.location(place)?;
            let id = self.memory.plane(reference)?;
            if !self.roots.values().any(|p| *p == id) {
                return Err(format!("line {}: writes through reference parameters need an effect contract; unsupported", place.line));
            }
            let old = project(self.memory.read(reference)?, &fields)?.clone();
            let new = self.eval(value, Some(&old.ty()))?;
            let replace_plane = !self.same_layout(&old, &new);
            let mut root = self.memory.read(reference)?.clone();
            replace_projection(&mut root, &fields, new)?;
            self.record_valid(&root, place.line)?;
            self.memory.write(id, root.clone(), replace_plane)?;
            for (n, plane) in &self.roots {
                if *plane == id {
                    self.env.insert(n.clone(), root.clone());
                }
            }
            return Ok(());
        }
        fn path(e: &Expr, fields: &mut Vec<String>) -> Result<String> {
            match &e.kind {
                Kind::Name(n) => Ok(n.clone()),
                Kind::Field(base, n) => {
                    let root = path(base, fields)?;
                    fields.push(n.clone());
                    Ok(root)
                }
                _ => Err(format!(
                    "line {}: assignment requires a variable or struct field",
                    e.line
                )),
            }
        }
        fn replace(root: &mut Symbol, fields: &[String], value: Symbol) -> Result<()> {
            if fields.is_empty() {
                *root = value;
                return Ok(());
            }
            let Symbol::Record(_, members) = root else {
                return Err("field assignment requires a struct".into());
            };
            let member = members.get_mut(&fields[0]).ok_or("unknown field")?;
            replace(member, &fields[1..], value)
        }
        let mut fields = Vec::new();
        let name = path(place, &mut fields)?;
        let old = if let Kind::Name(n) = &place.kind {
            self.env
                .get(n)
                .cloned()
                .ok_or("unknown assignment target")?
        } else {
            self.eval(place, None)?
        };
        let new = self.eval(value, Some(&old.ty()))?;
        let replace_plane = !self.same_layout(&old, &new);
        let mut root = self
            .env
            .get(&name)
            .cloned()
            .ok_or("unknown assignment target")?;
        replace(&mut root, &fields, new)?;
        self.record_valid(&root, place.line)?;
        if let Some(id) = self.roots.get(&name) {
            self.memory.write(*id, root.clone(), replace_plane)?;
        }
        self.env.insert(name, root);
        Ok(())
    }

    fn same_layout(&mut self, a: &Symbol, b: &Symbol) -> bool {
        match (a, b) {
            (Symbol::Record(an, a), Symbol::Record(bn, b)) => {
                an == bn
                    && a.len() == b.len()
                    && a.iter()
                        .all(|(n, v)| b.get(n).is_some_and(|w| self.same_layout(v, w)))
            }
            (
                Symbol::Array {
                    len: a,
                    items: av,
                    element,
                    identity: ai,
                },
                Symbol::Array {
                    len: b,
                    items: bv,
                    identity: bi,
                    ..
                },
            ) => {
                let length = equal(a, b)
                    .is_ok_and(|p| self.prove(&p, "stable array storage length", 0).is_ok());
                length
                    && match (av, bv) {
                        (Some(a), Some(b)) => a.iter().zip(b).all(|(v, w)| self.same_layout(v, w)),
                        _ => {
                            ai == bi
                                || matches!(
                                    **element,
                                    Ty::Int
                                        | Ty::Nat
                                        | Ty::Machine(_)
                                        | Ty::Bool
                                        | Ty::Ref(_)
                                        | Ty::Unit
                                )
                        }
                    }
            }
            (Symbol::Number(_, _), Symbol::Number(_, _))
            | (Symbol::Bool(_), Symbol::Bool(_))
            | (Symbol::Ref(..), Symbol::Ref(..))
            | (Symbol::Unit, Symbol::Unit) => true,
            _ => false,
        }
    }

    fn location(&mut self, e: &Expr) -> Result<(Reference, Vec<Projection>)> {
        match &e.kind {
            Kind::Name(n) => {
                let id = if let Some(id) = self.roots.get(n) {
                    *id
                } else {
                    let v = self
                        .env
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown place {n}"))?;
                    let id = self.memory.allocate(v)?;
                    self.roots.insert(n.clone(), id);
                    id
                };
                Ok((self.memory.borrow(id)?, vec![]))
            }
            Kind::Field(base, n) => {
                let (r, mut path) = self.location(base)?;
                path.push(Projection::Field(n.clone()));
                project(self.memory.read(r)?, &path)?;
                Ok((r, path))
            }
            Kind::Index(base, i) => {
                let (r, mut path) = self.location(base)?;
                let index = self.nonnegative(i, "nonnegative reference index")?;
                if !index.terms.is_empty() {
                    return Err(
                        "reference projections currently need a statically known index".into(),
                    );
                }
                let index =
                    usize::try_from(index.constant).map_err(|_| "invalid reference index")?;
                path.push(Projection::Index(index));
                project(self.memory.read(r)?, &path)?;
                Ok((r, path))
            }
            Kind::Unary(op, x) if op == "*" => {
                let Symbol::Ref(_, r, path) = self.eval(x, None)? else {
                    return Err("dereference requires a reference".into());
                };
                self.memory.read(r)?;
                Ok((r, path))
            }
            _ => Err(format!("line {}: expected a referenceable place", e.line)),
        }
    }
    fn hint(&self, e: &Expr) -> Option<Ty> {
        match &e.kind {
            Kind::Constant(t, _) => Some(Ty::Machine(*t)),
            Kind::Name(n) => self.env.get(n).map(Symbol::ty),
            Kind::Unary(op, x) if op == "*" => {
                if let Some(Ty::Ref(t)) = self.hint(x) {
                    Some(*t)
                } else {
                    None
                }
            }
            Kind::Unary(_, x) => self.hint(x),
            Kind::Field(base, field) => {
                if let Kind::Name(n) = &base.kind {
                    if let Some(Symbol::Record(_, fields)) = self.env.get(n) {
                        return fields.get(field).map(Symbol::ty);
                    }
                }
                None
            }
            Kind::Binary(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::Call(n, _) => self.functions.get(n).and_then(|f| match f.ret {
                Type::Int => Some(Ty::Int),
                Type::Nat => Some(Ty::Nat),
                Type::Bool => Some(Ty::Bool),
                Type::Machine(t) => Some(Ty::Machine(t)),
                _ => None,
            }),
            _ => None,
        }
    }
    fn proof_names(&self, steps: &[String], line: usize) -> Result<()> {
        for step in steps {
            if let Some(n) = step.strip_prefix("exact ") {
                if !self.facts.contains_key(n) {
                    return Err(format!("line {line}: exact {n} is not a proven local fact"));
                }
            }
        }
        Ok(())
    }
    fn eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let value = self.eval_inner(e, expected).map_err(|s| {
            if s.starts_with("line ") {
                s
            } else {
                format!("line {}: {s}", e.line)
            }
        })?;
        if let Some(t) = expected {
            self.compatible(&value.ty(), t, e.line)?;
        }
        if let Symbol::Number(Ty::Machine(t), n) = &value {
            let (lo, hi) = t.bounds();
            self.prove(
                &Formula::Ge(n.sub(&Linear::number(lo))?),
                "machine integer lower bound",
                e.line,
            )?;
            self.prove(
                &Formula::Ge(Linear::number(hi).sub(n)?),
                "machine integer upper bound (no overflow)",
                e.line,
            )?;
        }
        Ok(value)
    }
    fn eval_inner(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        match &e.kind {
            Kind::Unit => Ok(Symbol::Unit),
            Kind::Constant(t, n) => Ok(Symbol::Number(Ty::Machine(*t), Linear::number(*n))),
            Kind::Number(n) => Ok(Symbol::Number(
                match expected {
                    Some(Ty::Nat) => Ty::Nat,
                    Some(Ty::Machine(t)) => Ty::Machine(*t),
                    _ => Ty::Int,
                },
                Linear::number(*n),
            )),
            Kind::Bool(b) => Ok(Symbol::Bool(if *b {
                Formula::True
            } else {
                Formula::False
            })),
            Kind::Name(n) => {
                if let Some(id) = self.roots.get(n) {
                    self.memory.get(*id).cloned()
                } else {
                    self.env
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown value {n}"))
                }
            }
            Kind::Field(base, name) => {
                let Symbol::Record(_, fields) = self.eval(base, None)? else {
                    return Err("field access requires a struct".into());
                };
                fields
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {name}"))
            }
            Kind::Record(name, entries) => {
                let def = self
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown struct {name}"))?;
                let saved = self.env.clone();
                let mut fields = BTreeMap::new();
                for (n, value) in entries {
                    if fields.contains_key(n) {
                        return Err(format!("duplicate field {n}"));
                    }
                    let ty = def
                        .fields
                        .iter()
                        .find(|(field, _)| field == n)
                        .map(|(_, t)| t)
                        .ok_or_else(|| format!("unknown field {n}"))?;
                    let hint = match ty {
                        Type::Nat => Some(Ty::Nat),
                        Type::Int => Some(Ty::Int),
                        Type::Bool => Some(Ty::Bool),
                        Type::Machine(t) => Some(Ty::Machine(*t)),
                        _ => None,
                    };
                    fields.insert(n.clone(), self.eval(value, hint.as_ref())?);
                }
                self.env = saved;
                let record = Symbol::Record(name.clone(), fields);
                self.record_valid(&record, e.line)?;
                Ok(record)
            }
            Kind::Unary(op, x) if op == "&" => {
                let (r, path) = self.location(x)?;
                let ty = project(self.memory.read(r)?, &path)?.ty();
                Ok(Symbol::Ref(Box::new(ty), r, path))
            }
            Kind::Unary(op, _) if op == "*" => {
                let (r, path) = self.location(e)?;
                project(self.memory.read(r)?, &path).cloned()
            }
            Kind::Unary(op, x) if op == "!" => Ok(Symbol::Bool(
                self.eval(x, Some(&Ty::Bool))?.proposition()?.not(),
            )),
            Kind::Unary(_, x) => {
                let ty = expected
                    .cloned()
                    .or_else(|| self.hint(x))
                    .filter(|t| matches!(t, Ty::Machine(_)))
                    .unwrap_or(Ty::Int);
                let n = if let Kind::Number(n) = x.kind {
                    Linear::number(n)
                } else {
                    self.eval(x, Some(&ty))?.number()?
                };
                Ok(Symbol::Number(ty, n.scale(-1)?))
            }
            Kind::Binary(op, a, b) if op == "&&" || op == "||" => {
                let a = self.eval(a, Some(&Ty::Bool))?.proposition()?;
                // Logical expressions are pure. Both operands must be well-defined.
                let b = self.eval(b, Some(&Ty::Bool))?.proposition()?;
                Ok(Symbol::Bool(if op == "&&" { a.and(b) } else { a.or(b) }))
            }
            Kind::Binary(op, a, b) => {
                let ty = if matches!(op.as_str(), "+" | "-" | "*") {
                    expected.cloned()
                } else {
                    None
                }
                .or_else(|| self.hint(a))
                .or_else(|| self.hint(b))
                .unwrap_or(Ty::Int);
                if !matches!(ty, Ty::Int | Ty::Nat | Ty::Machine(_)) {
                    return Err("arithmetic and comparisons require integer operands".into());
                }
                let a = self.eval(a, Some(&ty))?.number()?;
                let b = self.eval(b, Some(&ty))?.number()?;
                match op.as_str() {
                    "+" => Ok(Symbol::Number(ty, a.add(&b)?)),
                    "-" if matches!(ty, Ty::Nat) => {
                        // Nat subtraction is truncated, with an exact two-case model.
                        let result = self.arbitrary(&Ty::Nat)?;
                        let r = result.number()?;
                        let diff = a.sub(&b)?;
                        let cases = Formula::Ge(diff.clone())
                            .and(equal(&r, &diff)?)
                            .or(Formula::Ge(diff.scale(-1)?.add(&Linear::number(-1))?)
                                .and(equal(&r, &Linear::number(0))?));
                        self.assume(&cases)?;
                        Ok(result)
                    }
                    "-" => Ok(Symbol::Number(ty, a.sub(&b)?)),
                    "*" => {
                        let n = if a.terms.is_empty() {
                            b.scale(a.constant)?
                        } else if b.terms.is_empty() {
                            a.scale(b.constant)?
                        } else {
                            return Err("nonlinear multiplication needs an extended proof theory; unsupported".into());
                        };
                        Ok(Symbol::Number(ty, n))
                    }
                    "==" => Ok(Symbol::Bool(equal(&a, &b)?)),
                    "!=" => Ok(Symbol::Bool(equal(&a, &b)?.not())),
                    ">=" => Ok(Symbol::Bool(Formula::Ge(a.sub(&b)?))),
                    "<=" => Ok(Symbol::Bool(Formula::Ge(b.sub(&a)?))),
                    ">" => Ok(Symbol::Bool(Formula::Ge(
                        a.sub(&b)?.add(&Linear::number(-1))?,
                    ))),
                    "<" => Ok(Symbol::Bool(Formula::Ge(
                        b.sub(&a)?.add(&Linear::number(-1))?,
                    ))),
                    _ => Err("unsupported binary operator".into()),
                }
            }
            Kind::Array(items) => {
                let element = if let Some(Ty::Array(t, _)) = expected {
                    (**t).clone()
                } else if let Some(first) = items.first() {
                    self.hint(first).unwrap_or(Ty::Int)
                } else {
                    return Err("empty array needs an explicit type".into());
                };
                let values = items
                    .iter()
                    .map(|x| self.eval(x, Some(&element)))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Symbol::Array {
                    element: Box::new(element),
                    len: Linear::number(values.len() as i128),
                    items: Some(values),
                    identity: self.fresh_name(),
                })
            }
            Kind::Index(array, index) => {
                let array = self.eval(array, None)?;
                let index = self.nonnegative(index, "nonnegative array index")?;
                let Symbol::Array {
                    element,
                    len,
                    items,
                    identity,
                } = array
                else {
                    return Err("indexing requires an array".into());
                };
                self.prove(
                    &Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?),
                    "array index < length",
                    e.line,
                )?;
                if index.terms.is_empty() {
                    if let Some(value) = items
                        .as_ref()
                        .and_then(|v| usize::try_from(index.constant).ok().and_then(|i| v.get(i)))
                    {
                        return Ok(value.clone());
                    }
                }
                // Repeated reads of the same symbolic element have the same value.
                let key = format!("evg_read_{identity}_{index:?}");
                if let Some(v) = self.env.get(&key) {
                    return Ok(v.clone());
                }
                let v = self.arbitrary(&element)?;
                self.env.insert(key, v.clone());
                Ok(v)
            }
            Kind::Call(name, args) => {
                if self.specification && self.current.as_ref() == Some(name) {
                    return Err("recursive calls are forbidden in specifications".into());
                }
                if name == "move" || name == "drop" {
                    if self.specification {
                        return Err("specifications and facts cannot move or drop values".into());
                    }
                    if args.len() != 1 {
                        return Err(format!("{name} expects one place"));
                    }
                    let (r, path) = self.location(&args[0])?;
                    if !path.is_empty() {
                        return Err(
                            "moving individual fields requires partial-shape tracking; unsupported"
                                .into(),
                        );
                    }
                    let id = self.memory.plane(r)?;
                    if !self.roots.values().any(|p| *p == id) {
                        return Err("cannot move or drop a borrowed parameter plane".into());
                    }
                    let value = self.memory.take(id)?;
                    return Ok(if name == "drop" { Symbol::Unit } else { value });
                }
                let f = self.functions.get(name).cloned().ok_or_else(|| format!("unknown function {name}; calls require an earlier verified declaration (recursion is not supported yet)"))?;
                if args.len() != f.params.len() {
                    return Err(format!("{name} expects {} arguments", f.params.len()));
                }
                // Evaluate actuals in the caller; dependent parameter types in an
                // isolated callee environment. Restore the caller on completion.
                let mut actuals = Vec::new();
                for ((_, t), arg) in f.params.iter().zip(args) {
                    let hint = match t {
                        Type::Nat => Some(Ty::Nat),
                        Type::Int => Some(Ty::Int),
                        Type::Bool => Some(Ty::Bool),
                        Type::Machine(t) => Some(Ty::Machine(*t)),
                        _ => None,
                    };
                    actuals.push(self.eval(arg, hint.as_ref())?);
                }
                let saved = self.env.clone();
                let saved_roots = self.roots.clone();
                self.env.clear();
                self.roots.clear();
                for ((n, t), value) in f.params.iter().zip(actuals) {
                    let t = self.resolve(t)?;
                    self.compatible(&value.ty(), &t, e.line)?;
                    self.env.insert(n.clone(), value);
                }
                if let Some(pre) = &f.pre {
                    let p = self.proposition(pre)?;
                    self.prove(&p, &format!("precondition of {name}"), e.line)?;
                }
                if self.current.as_ref() == Some(name) {
                    let entry = self
                        .measure
                        .clone()
                        .ok_or("recursive calls require a decreases clause")?;
                    let expression = f
                        .decreases
                        .as_ref()
                        .ok_or("recursive calls require a decreases clause")?;
                    let next = self.nonnegative(expression, "nonnegative recursion measure")?;
                    self.prove(
                        &Formula::Ge(entry.sub(&next)?.add(&Linear::number(-1))?),
                        "strictly decreasing recursion measure",
                        e.line,
                    )?;
                }
                let ret = self.resolve(&f.ret)?;
                let value = self.arbitrary(&ret)?;
                self.env.insert("result".into(), value.clone());
                if let Some(post) = &f.post {
                    let p = self.proposition(post)?;
                    self.assume(&p)?;
                }
                self.env = saved;
                self.roots = saved_roots;
                Ok(value)
            }
            Kind::If(condition, yes, no) => {
                let p = self.eval(condition, Some(&Ty::Bool))?.proposition()?;
                let base = self.paths.clone();
                let env = self.env.clone();
                self.paths = extend(&base, &p, false)?;
                let a = self.eval(yes, expected)?;
                let a_paths = self.paths.clone();
                self.paths = extend(&base, &p, true)?;
                self.env = env.clone();
                let b = self.eval(no, Some(&a.ty()))?;
                let b_paths = self.paths.clone();
                self.paths = base;
                self.env = env;
                let result = self.arbitrary(&a.ty())?;
                let relation_a = self.symbol_equal(&result, &a)?;
                let relation_b = self.symbol_equal(&result, &b)?;
                let mut paths = extend(&a_paths, &relation_a, false)?;
                paths.extend(extend(&b_paths, &relation_b, false)?);
                if paths.len() > 64 {
                    return Err("verification path limit reached (64)".into());
                }
                self.paths = paths;
                Ok(result)
            }
        }
    }
    fn symbol_equal(&self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        match (a, b) {
            (Symbol::Number(_, a), Symbol::Number(_, b)) => equal(a, b),
            (Symbol::Bool(a), Symbol::Bool(b)) => Ok(a
                .clone()
                .and(b.clone())
                .or(a.clone().not().and(b.clone().not()))),
            _ => Err("conditional array values are not supported yet".into()),
        }
    }
}

#[derive(Debug)]
pub struct VerifiedProgram {
    pub(crate) functions: Vec<Function>,
    pub(crate) structs: BTreeMap<String, Struct>,
    pub obligations: usize,
}

pub fn verify(source: &str) -> Result<VerifiedProgram> {
    let parsed = syntax::parse(source)?;
    let mut structs = BTreeMap::new();
    let empty_functions = BTreeMap::new();
    for s in &parsed.structs {
        if structs.contains_key(&s.name) {
            return Err(format!("line {}: duplicate struct {}", s.line, s.name));
        }
        let mut ctx = Context::new(&empty_functions, &structs);
        for (n, t) in &s.fields {
            if n == "self" || ctx.env.contains_key(n) {
                return Err(format!("line {}: duplicate or reserved field {n}", s.line));
            }
            let t = ctx.resolve(t)?;
            let value = ctx.arbitrary(&t)?;
            ctx.env.insert(n.clone(), value);
        }
        ctx.env.insert(
            "self".into(),
            Symbol::Record(s.name.clone(), ctx.env.clone()),
        );
        if let Some(p) = &s.invariant {
            ctx.proposition(p)?;
        }
        structs.insert(s.name.clone(), s.clone());
    }
    let mut functions = BTreeMap::new();
    let mut obligations = 0;
    for f in &parsed.functions {
        if matches!(f.name.as_str(), "move" | "drop") {
            return Err(format!("line {}: {} is a reserved builtin", f.line, f.name));
        }
        if type_has_reference(&f.ret, &structs) {
            return Err(format!("line {}: returning references needs an explicit lifetime/plane contract; unsupported", f.line));
        }
        if functions.contains_key(&f.name) {
            return Err(format!("line {}: duplicate function {}", f.line, f.name));
        }
        let mut available = functions.clone();
        if f.decreases.is_some() {
            available.insert(f.name.clone(), f.clone());
        }
        let mut ctx = Context::new(&available, &structs);
        ctx.current = Some(f.name.clone());
        for (n, t) in &f.params {
            if ctx.env.contains_key(n) {
                return Err(format!("line {}: duplicate parameter {n}", f.line));
            }
            let ty = ctx.resolve(t)?;
            let value = ctx.arbitrary(&ty)?;
            ctx.env.insert(n.clone(), value);
        }
        if let Some(pre) = &f.pre {
            ctx.specification = true;
            let p = ctx.eval(pre, Some(&Ty::Bool))?.proposition()?;
            ctx.assume(&p)?;
            ctx.specification = false;
        }
        let ret = ctx.resolve(&f.ret)?;
        if let Some(measure) = &f.decreases {
            ctx.specification = true;
            ctx.measure = Some(ctx.nonnegative(measure, "nonnegative recursion measure")?);
            ctx.specification = false;
        }
        let contract_env = ctx.env.clone();
        for statement in &f.body {
            if let Some(target) = &statement.target {
                ctx.assign(target, &statement.value)?;
                continue;
            }
            if statement.effect {
                ctx.eval(&statement.value, None)?;
                continue;
            }
            if ctx.env.contains_key(&statement.name) || ctx.facts.contains_key(&statement.name) {
                return Err(format!(
                    "line {}: duplicate binding {}",
                    statement.value.line, statement.name
                ));
            }
            if statement.fact {
                ctx.specification = true;
                let p = ctx.eval(&statement.value, Some(&Ty::Bool))?.proposition()?;
                ctx.specification = false;
                if let Some(steps) = &statement.proof {
                    ctx.proof_names(steps, statement.value.line)?;
                }
                ctx.prove(
                    &p,
                    &format!("fact {}", statement.name),
                    statement.value.line,
                )?;
                ctx.assume(&p)?;
                ctx.facts.insert(statement.name.clone(), p);
            } else {
                let ty = statement.ty.as_ref().map(|t| ctx.resolve(t)).transpose()?;
                let value = ctx.eval(&statement.value, ty.as_ref())?;
                ctx.env.insert(statement.name.clone(), value);
            }
        }
        let value = ctx.eval(&f.result, Some(&ret))?;
        ctx.proof_names(&f.proof, f.result.line)?;
        if let Some(post) = &f.post {
            ctx.specification = true;
            ctx.env = contract_env;
            ctx.roots.clear();
            ctx.env.insert("result".into(), value);
            let p = ctx.eval(post, Some(&Ty::Bool))?.proposition()?;
            ctx.prove(&p, &format!("postcondition of {}", f.name), post.line)?;
        }
        obligations += ctx.obligations;
        functions.insert(f.name.clone(), f.clone());
    }
    Ok(VerifiedProgram {
        functions: parsed.functions,
        structs,
        obligations,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn checks_contracts_and_bounds_internally() {
        let p = verify(include_str!("../examples/contracts.evg")).unwrap();
        assert!(p.obligations >= 3);
        for source in [
            include_str!("../examples/reject_bounds.evg"),
            include_str!("../examples/reject_contract.evg"),
        ] {
            assert!(verify(source).is_err());
        }
    }
    #[test]
    fn composes_calls_and_checks_preconditions() {
        let prefix = "fn inc(n: nat) -> nat where (n < 10) ensures (result == n + 1) { n + 1 } ";
        assert!(verify(&format!(
            "{prefix} fn main() -> nat ensures (result == 5) {{ inc(4) }}"
        ))
        .is_ok());
        assert!(verify(&format!("{prefix} fn main() -> nat {{ inc(10) }}")).is_err());
    }
    #[test]
    fn verifies_both_branches_and_natural_subtraction() {
        verify("fn abs(n: int) -> int ensures (result >= 0) { if n >= 0 { n } else { -n } }")
            .unwrap();
        verify("fn sub(n: nat) -> nat ensures (result <= n) { n - 1 }").unwrap();
        assert!(verify(
            "fn bad(n: int) -> int ensures (result >= 0) { if n >= 0 { n } else { n } }"
        )
        .is_err());
    }
    #[test]
    fn facts_are_proved_before_use() {
        assert!(verify("fn bad(n: nat) -> nat { fact lie = n < 0; n }").is_err());
        assert!(verify("fn bad() -> nat { fact h = true by { exact missing }; 0 }").is_err());
        assert!(verify("fn bad() -> nat { result }").is_err());
    }
    #[test]
    fn arrays_and_types_are_checked() {
        verify("fn main() -> nat ensures (result == 20) { let a: [nat; 2] = [10, 20]; a[1] }")
            .unwrap();
        for s in [
            "fn f() -> nat { let a: [nat; 2] = [1]; 0 }",
            "fn f() -> nat { let a: [nat; 1] = [1]; a[1] }",
            "fn f() -> nat { -1 }",
            "fn f() -> bool { 1 }",
        ] {
            assert!(verify(s).is_err(), "{s}");
        }
    }
    #[test]
    fn compound_logic_and_contradictory_preconditions() {
        verify("fn f(n: nat) -> nat where (n < 3 || n > 10) ensures (result != 5) { n }").unwrap();
        verify("fn f(n: nat) -> nat where (n < 0) ensures (result > 100) { n }").unwrap();
    }

    #[test]
    fn struct_invariants_and_atomic_replacement() {
        let prefix = "type Buffer struct { len: nat, cap: nat } where (len <= cap); ";
        let valid = format!("{prefix} fn main() -> nat {{ let b = Buffer {{ len: 1, cap: 2 }}; b = Buffer {{ len: b.len + 2, cap: b.cap + 2 }}; b.len }}");
        assert_eq!(verify(&valid).unwrap().run().unwrap().to_string(), "3");
        for body in [
            "let b = Buffer {len: 3, cap: 2}; b.len",
            "let b = Buffer {len: 1, cap: 2}; b.len = 3; b.len",
            "let b = Buffer {len: 1}; b.len",
            "let b = Buffer {len: 1, cap: 2, extra: 0}; b.len",
        ] {
            assert!(
                verify(&format!("{prefix} fn main() -> nat {{ {body} }}")).is_err(),
                "{body}"
            );
        }
    }

    #[test]
    fn dependent_struct_fields_and_nested_invariants() {
        let s = "type Storage struct { len: nat, data: [int; len] } type Outer struct { storage: Storage } fn main() -> int { let s = Storage {len: 2, data: [10, 20]}; let o = Outer {storage: s}; o.storage.data[1] }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "20");
        assert!(verify("type Storage struct {len: nat, data: [int; len]} fn main() -> nat {let s = Storage {len: 2, data: [1, 2]}; s.len = 3; 0}").is_err());
        assert!(verify("type Inner struct {x: nat} where (x > 0); type Outer struct {inner: Inner} fn main() -> nat {let o = Outer {inner: Inner {x: 1}}; o.inner.x = 0; 0}").is_err());
    }

    #[test]
    fn contracts_capture_entry_parameters() {
        assert!(verify("fn bad(n: nat) -> nat ensures (result == n) { n = 0; n }").is_err());
        let s = "fn reset(n: nat) -> nat ensures (result == 0) { n = 0; n } fn main() -> nat ensures (result == 0) {reset(10)}";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "0");
    }

    #[test]
    fn aliased_references_share_scalar_updates() {
        let s = "fn read(r: &nat) -> nat ensures (result == *r) { *r } fn main() -> nat ensures (result == 7) { let x: nat = 1; let a = &x; let b = &x; *a = 7; read(b) }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "7");
        let s = "fn main() -> nat ensures (result == 11) { let data: [nat; 2] = [1, 2]; let a = &data[0]; let b = &data[1]; *a = 9; *b = 11; *b }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "11");
    }

    #[test]
    fn stale_references_are_compile_errors() {
        for body in [
            "let x: nat = 1; let r = &x; drop(x); *r",
            "let x: nat = 1; let r = &x; let y = move(x); *r",
            "let a: [nat; 1] = [1]; let r = &a[0]; drop(a); *r",
            "let x: nat = 1; let r = &x; drop(x); x = 2; *r",
            "let x: nat = 1; let y = move(x); x",
        ] {
            assert!(
                verify(&format!("fn main() -> nat {{ {body} }}")).is_err(),
                "{body}"
            );
        }
        let s = "fn main() -> nat { let x: nat = 1; let y = move(x); x = 2; x + y }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "3");
        let fixed = "fn main() -> usize ensures (result == 3) { let a: [usize; 2] = [1, 2]; let r = &a[0]; a = [3, 4]; *r }";
        assert_eq!(verify(fixed).unwrap().run().unwrap().to_string(), "3");
    }

    #[test]
    fn reference_updates_recheck_invariants_and_cannot_escape() {
        let prefix = "type Small struct {n: nat} where (n < 4); ";
        assert!(verify(&format!(
            "{prefix} fn main() -> nat {{let x = Small {{n: 1}}; let r = &x.n; *r = 9; x.n }}"
        ))
        .is_err());
        assert!(verify("fn escape() -> &nat {let x: nat = 1; &x}").is_err());
        assert!(verify("fn write(r: &nat) -> () { *r = 1; () }").is_err());
        assert!(verify("fn f(n: nat) -> nat ensures (result == move(n)) { n }").is_err());
    }

    #[test]
    fn verifies_well_founded_recursion() {
        let s = "fn countdown(n: nat) -> nat ensures (result == n) decreases (n) { if n == 0 { 0 } else { countdown(n - 1) + 1 } } fn main() -> nat ensures (result == 12) { countdown(12) }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "12");
        for body in [
            "loop(n)",
            "loop(n + 1)",
            "if n == 0 { loop(n) } else { loop(n - 1) }",
        ] {
            assert!(
                verify(&format!(
                    "fn loop(n: nat) -> nat decreases (n) {{ {body} }}"
                ))
                .is_err(),
                "{body}"
            );
        }
        assert!(verify("fn bad(n: nat) -> nat ensures (bad(n) == 0) decreases (n) {0}").is_err());
    }

    #[test]
    fn machine_overflow_requires_a_proof() {
        assert!(verify("fn increment(n: usize) -> usize { n + 1 }").is_err());
        let p = "fn increment(n: usize) -> usize where (n < usize::MAX) ensures (result == n + 1) { n + 1 } fn main() -> usize ensures (result == usize::MAX) { increment(usize::MAX - 1) }";
        assert_eq!(
            verify(p).unwrap().run().unwrap().to_string(),
            u64::MAX.to_string()
        );
        for s in [
            "fn main() -> usize {usize::MAX + 1}",
            "fn main() -> u8 {256}",
            "fn main() -> u8 {0 - 1}",
            "fn abs(n: isize) -> isize {if n >= 0 {n} else {-n}}",
            "fn main() -> i8 {-129}",
            "fn main() -> i8 {-i8::MIN}",
        ] {
            assert!(verify(s).is_err(), "{s}");
        }
        assert_eq!(
            verify("fn main() -> i8 {-128}")
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "-128"
        );
    }

    #[test]
    fn signed_array_indices_also_need_lower_bounds() {
        assert!(
            verify("fn at(n: usize, a: [isize; n], i: isize) -> isize where (i < 5) {a[i]}")
                .is_err()
        );
        verify("fn at(a: [isize; 5], i: isize) -> isize where (i >= 0 && i < 5) {a[i]}").unwrap();
    }
}
