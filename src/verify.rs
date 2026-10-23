//! Internal elaboration and verification-condition generation.
use crate::{
    certificate::{ProofBundle, Session},
    kernel::Linear,
    memory::{Memory, PlaneId, Projection, Reference},
    syntax::{self, Expr, Function, Kind, MachineInt, Statement, Struct, Type},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Formula {
    True,
    False,
    Ge(Linear),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
}
impl Formula {
    fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Self::True => out.push(0),
            Self::False => out.push(1),
            Self::Ge(row) => {
                out.push(2);
                out.extend(row.constant.to_le_bytes());
                out.extend((row.terms.len() as u64).to_le_bytes());
                for (name, coefficient) in &row.terms {
                    out.extend((name.len() as u64).to_le_bytes());
                    out.extend(name.as_bytes());
                    out.extend(coefficient.to_le_bytes());
                }
            }
            Self::And(a, b) | Self::Or(a, b) => {
                out.push(if matches!(self, Self::And(..)) { 3 } else { 4 });
                a.encode(out);
                b.encode(out);
            }
            Self::Not(p) => {
                out.push(5);
                p.encode(out);
            }
        }
    }
    fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::False, _) | (_, Self::False) => Self::False,
            (Self::True, p) | (p, Self::True) => p,
            (a, b) if a == b => a,
            (a, b) => Self::And(Box::new(a), Box::new(b)),
        }
    }
    fn or(self, other: Self) -> Self {
        match (self, other) {
            (Self::True, _) | (_, Self::True) => Self::True,
            (Self::False, p) | (p, Self::False) => p,
            (a, b) if a == b => a,
            (a, b) => Self::Or(Box::new(a), Box::new(b)),
        }
    }
    fn not(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(p) => *p,
            p => Self::Not(Box::new(p)),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
fn replace_projection(
    value: &mut Symbol,
    path: &[Projection],
    new: Symbol,
    fresh: &mut usize,
) -> Result<()> {
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
                items: Some(items),
                identity,
                ..
            },
        ) => {
            *fresh += 1;
            *identity = format!("evg_{}", fresh);
            items.get_mut(*i).ok_or("reference index out of bounds")?
        }
        _ => return Err("invalid reference projection".into()),
    };
    replace_projection(value, &path[1..], new, fresh)
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
fn clauses<'a>(expression: &'a Expr, out: &mut Vec<&'a Expr>) {
    if let Kind::Binary(op, a, b) = &expression.kind {
        if op == "&&" {
            clauses(a, out);
            clauses(b, out);
            return;
        }
    }
    out.push(expression);
}

pub(crate) fn is_affine(
    t: &Type,
    structs: &BTreeMap<String, Struct>,
    drops: &BTreeSet<String>,
) -> bool {
    match t {
        Type::Named(n) => {
            drops.contains(n)
                || structs.get(n).is_some_and(|s| {
                    s.affine || s.fields.iter().any(|(_, t)| is_affine(t, structs, drops))
                })
        }
        Type::Array(t, _) => is_affine(t, structs, drops),
        _ => false,
    }
}
fn runtime_type(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Int | Type::Nat => false,
        Type::Named(n) => structs
            .get(n)
            .is_some_and(|s| !s.ideal && s.fields.iter().all(|(_, t)| runtime_type(t, structs))),
        Type::Array(t, _) | Type::Ref(t) => runtime_type(t, structs),
        _ => true,
    }
}

fn destructor_expression(e: &Expr) -> bool {
    match &e.kind {
        Kind::Call(..) | Kind::Record(..) => false,
        Kind::Unary(op, _) if op == "&" || op == "*" => false,
        Kind::Unary(_, x) | Kind::Field(x, _) | Kind::FactAt(x, _) => destructor_expression(x),
        Kind::Binary(_, a, b) | Kind::Index(a, b) => {
            destructor_expression(a) && destructor_expression(b)
        }
        Kind::If(c, a, b) => {
            destructor_expression(c) && destructor_expression(a) && destructor_expression(b)
        }
        Kind::Array(xs) => xs.iter().all(destructor_expression),
        _ => true,
    }
}
fn destructor_body(body: &[Statement]) -> bool {
    body.iter().all(|s| match s {
        Statement::Destructure { .. } => false,
        Statement::Assign { target, value } => {
            destructor_expression(target) && destructor_expression(value)
        }
        Statement::Let { value, .. } | Statement::Fact { value, .. } | Statement::Effect(value) => {
            destructor_expression(value)
        }
        Statement::Proof { proposition, .. } => destructor_expression(proposition),
        Statement::Update { body, .. } => destructor_body(body),
    })
}

struct Context<'a> {
    functions: &'a BTreeMap<String, Function>,
    structs: &'a BTreeMap<String, Struct>,
    env: BTreeMap<String, Symbol>,
    facts: BTreeMap<String, Expr>,
    proofs: BTreeMap<String, Formula>,
    paths: Vec<Vec<Linear>>,
    fresh: usize,
    obligations: usize,
    memory: Memory<Symbol>,
    roots: BTreeMap<String, PlaneId>,
    specification: bool,
    current: Option<String>,
    measure: Option<Linear>,
    opened: BTreeMap<String, BTreeSet<String>>,
    drops: &'a BTreeSet<String>,
    dropping: bool,
    helpers: &'a BTreeSet<String>,
    ideal: bool,
    session: &'a mut Session,
    writable: BTreeSet<PlaneId>,
    old_values: BTreeMap<String, Symbol>,
}

impl<'a> Context<'a> {
    fn new(
        functions: &'a BTreeMap<String, Function>,
        structs: &'a BTreeMap<String, Struct>,
        drops: &'a BTreeSet<String>,
        helpers: &'a BTreeSet<String>,
        session: &'a mut Session,
    ) -> Self {
        Self {
            functions,
            structs,
            env: BTreeMap::new(),
            facts: BTreeMap::new(),
            proofs: BTreeMap::new(),
            paths: vec![vec![]],
            fresh: 0,
            obligations: 0,
            memory: Memory::default(),
            roots: BTreeMap::new(),
            specification: false,
            current: None,
            measure: None,
            opened: BTreeMap::new(),
            drops,
            dropping: false,
            helpers,
            ideal: false,
            session,
            writable: BTreeSet::new(),
            old_values: BTreeMap::new(),
        }
    }
    fn fresh_name(&mut self) -> String {
        self.fresh += 1;
        format!("evg_{}", self.fresh)
    }
    fn capture_old(&mut self) -> Result<()> {
        self.old_values.clear();
        for (name, value) in &self.env {
            self.old_values.insert(name.clone(), value.clone());
            if let Symbol::Ref(_, reference, fields) = value {
                let target = project(self.memory.read(*reference)?, fields)?.clone();
                self.old_values.insert(format!("*{name}"), target);
            }
        }
        Ok(())
    }
    fn old_key(e: &Expr) -> Result<String> {
        match &e.kind {
            Kind::Name(n) => Ok(n.clone()),
            Kind::Unary(op, x) if op == "*" => match &x.kind {
                Kind::Name(n) => Ok(format!("*{n}")),
                _ => Err("old currently accepts a parameter or its direct dereference".into()),
            },
            _ => Err("old currently accepts a parameter or its direct dereference".into()),
        }
    }
    fn number_type(&self) -> Ty {
        if self.ideal || self.specification {
            Ty::Int
        } else {
            Ty::Machine(MachineInt::parse("isize").expect("isize type"))
        }
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
            self.session
                .prove(&path)
                .map_err(|e| format!("line {line}: cannot prove {label}: {e}"))?;
        }
        Ok(())
    }
    fn resolve(&mut self, t: &Type) -> Result<Ty> {
        match t {
            Type::Int | Type::Nat if !self.ideal && !self.specification => Err("int and nat are proof-only; use a machine integer for runtime storage or declare ideal code".into()),
            Type::Int => Ok(Ty::Int), Type::Nat => Ok(Ty::Nat),
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
                if self.structs.get(n).is_some_and(|s| s.ideal) && !self.ideal && !self.specification {return Err(format!("{n} is ideal data and has no runtime layout"));}
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
                let saved_facts = self.facts.clone();
                self.facts = def.facts.iter().cloned().collect();
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
                self.facts = saved_facts;
                Ok(value)
            }
        }
    }

    fn record_valid(&mut self, value: &Symbol, line: usize) -> Result<()> {
        self.record_valid_with(value, line, &BTreeSet::new())
    }
    fn record_valid_with(
        &mut self,
        value: &Symbol,
        line: usize,
        lifted: &BTreeSet<String>,
    ) -> Result<()> {
        if let Symbol::Array {
            items: Some(items), ..
        } = value
        {
            for v in items {
                self.record_valid(v, line)?;
            }
            return Ok(());
        }
        let Symbol::Record(name, fields) = value else {
            return Ok(());
        };
        let def = self.structs.get(name).cloned().ok_or("unknown struct")?;
        if def.fields.len() != fields.len() {
            return Err(format!("line {line}: wrong fields for {name}"));
        }
        let saved = self.env.clone();
        let saved_roots = self.roots.clone();
        let saved_facts = self.facts.clone();
        self.facts = def.facts.iter().cloned().collect();
        self.roots.clear();
        self.env.clear();
        for (n, t) in &def.fields {
            let v = fields
                .get(n)
                .ok_or_else(|| format!("line {line}: missing field {n}"))?;
            self.validate_argument(v, line)?;
            let t = self.resolve(t)?;
            self.compatible(&v.ty(), &t, line)?;
            self.env.insert(n.clone(), v.clone());
        }
        self.env.insert("self".into(), value.clone());
        if let Some(p) = &def.invariant {
            let mut requirements = Vec::new();
            clauses(p, &mut requirements);
            for requirement in requirements {
                if matches!(&requirement.kind, Kind::Name(n) if lifted.contains(n)) {
                    continue;
                }
                let p = self.proposition(requirement)?;
                self.prove(&p, &format!("invariant of {name}"), line)?;
            }
        }
        self.env = saved;
        self.roots = saved_roots;
        self.facts = saved_facts;
        Ok(())
    }

    fn assign(&mut self, place: &Expr, value: &Expr) -> Result<()> {
        if matches!(&place.kind, Kind::Unary(op, _) if op == "*") {
            let (reference, fields) = self.location(place)?;
            let id = self.memory.plane(reference)?;
            if !self.roots.values().any(|p| *p == id) && !self.writable.contains(&id) {
                return Err(format!("line {}: writes through reference parameters need an effect contract; unsupported", place.line));
            }
            let old = project(self.memory.read(reference)?, &fields)?.clone();
            if self.symbol_is_affine(&old) {
                return Err("overwriting owned fields through references requires ownership effect proofs; unsupported".into());
            }
            let new = self.eval(value, Some(&old.ty()))?;
            let replace_plane = !self.same_layout(&old, &new)?;
            let mut root = self.memory.read(reference)?.clone();
            replace_projection(&mut root, &fields, new, &mut self.fresh)?;
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
            self.storage(place)?
        };
        let new = self.eval(value, Some(&old.ty()))?;
        if self.dropping && self.symbol_is_affine(&old) {
            return Err(
                "destructors cannot replace owning fields without cleanup/effect proofs".into(),
            );
        }
        let replace_plane = !self.same_layout(&old, &new)?;
        let old_live = self
            .roots
            .get(&name)
            .is_none_or(|id| self.memory.get(*id).is_ok());
        if old_live && self.symbol_is_affine(&old) {
            self.validate_argument(&old, place.line)?;
        }
        let mut root = self
            .env
            .get(&name)
            .cloned()
            .ok_or("unknown assignment target")?;
        replace(&mut root, &fields, new)?;
        let lifted = self.opened.get(&name).cloned().unwrap_or_default();
        self.record_valid_with(&root, place.line, &lifted)?;
        if let Some(id) = self.roots.get(&name) {
            self.memory.write(*id, root.clone(), replace_plane)?;
        }
        self.env.insert(name, root);
        Ok(())
    }

    fn statement(&mut self, s: &Statement) -> Result<()> {
        match s {
            Statement::Destructure {
                record,
                fields,
                value,
            } => {
                let def = self
                    .structs
                    .get(record)
                    .ok_or_else(|| format!("line {}: unknown record {record}", value.line))?;
                if self.drops.contains(record) {
                    return Err(format!(
                        "line {}: destructuring {record} would bypass its Drop implementation",
                        value.line
                    ));
                }
                let expected = def
                    .fields
                    .iter()
                    .map(|(n, _)| n.as_str())
                    .collect::<BTreeSet<_>>();
                let actual = fields
                    .iter()
                    .map(|(n, _)| n.as_str())
                    .collect::<BTreeSet<_>>();
                let bindings = fields
                    .iter()
                    .map(|(_, n)| n.as_str())
                    .collect::<BTreeSet<_>>();
                if actual != expected
                    || actual.len() != fields.len()
                    || bindings.len() != fields.len()
                {
                    return Err(format!("line {}: a record pattern must bind every field exactly once with distinct names", value.line));
                }
                for (_, name) in fields {
                    self.fresh_binding(name, value.line)?;
                }
                let Symbol::Record(_, mut values) =
                    self.eval(value, Some(&Ty::Record(record.clone())))?
                else {
                    return Err("record pattern requires a record".into());
                };
                for (field, name) in fields {
                    let v = values.remove(field).ok_or("missing pattern field")?;
                    self.env.insert(name.clone(), v);
                }
                Ok(())
            }
            Statement::Update {
                places,
                lifts,
                body,
                line,
            } => self.update(places, lifts, body, *line),
            Statement::Assign { target, value } => self.assign(target, value),
            Statement::Effect(e) => {
                self.eval(e, None)?;
                Ok(())
            }
            Statement::Let { name, ty, value } => {
                self.fresh_binding(name, value.line)?;
                let ty = ty.as_ref().map(|t| self.resolve(t)).transpose()?;
                let v = self.eval(value, ty.as_ref())?;
                self.env.insert(name.clone(), v);
                Ok(())
            }
            Statement::Fact { name, value } => {
                self.fresh_binding(name, value.line)?;
                self.proposition(value)?; // Well-formedness only; NOT a proof or an assumption.
                self.facts.insert(name.clone(), value.clone());
                Ok(())
            }
            Statement::Proof {
                name,
                proposition,
                steps,
            } => {
                self.fresh_binding(name, proposition.line)?;
                let p = self.proposition(proposition)?;
                self.prove_with(&p, &format!("proof {name}"), proposition.line, Some(steps))?;
                self.assume(&p)?;
                self.proofs.insert(name.clone(), p);
                Ok(())
            }
        }
    }
    fn fresh_binding(&self, name: &str, line: usize) -> Result<()> {
        if self.env.contains_key(name)
            || self.facts.contains_key(name)
            || self.proofs.contains_key(name)
        {
            return Err(format!("line {line}: duplicate binding {name}"));
        }
        Ok(())
    }

    fn update_expression(&self, e: &Expr) -> bool {
        match &e.kind {
            Kind::Call(name, args) => {
                self.helpers.contains(name) && args.iter().all(|e| self.update_expression(e))
            }
            Kind::Record(..) | Kind::Array(..) => false,
            Kind::Unary(op, x) if op == "*" => {
                matches!(self.hint(x), Some(Ty::Ref(t)) if matches!(*t, Ty::Machine(_) | Ty::Bool | Ty::Int | Ty::Nat))
            }
            Kind::Unary(_, x) | Kind::Field(x, _) | Kind::FactAt(x, _) => self.update_expression(x),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                self.update_expression(a) && self.update_expression(b)
            }
            Kind::If(c, a, b) => {
                self.update_expression(c) && self.update_expression(a) && self.update_expression(b)
            }
            _ => true,
        }
    }
    fn update(
        &mut self,
        places: &[String],
        lifts: &[String],
        body: &[Statement],
        line: usize,
    ) -> Result<()> {
        fn root(e: &Expr) -> Option<&str> {
            match &e.kind {
                Kind::Name(n) => Some(n),
                Kind::Field(b, _) => root(b),
                _ => None,
            }
        }
        if !self.opened.is_empty() {
            return Err("nested invariant updates are not supported yet".into());
        }
        let roots: BTreeSet<_> = places.iter().cloned().collect();
        if roots.len() != places.len() {
            return Err(format!("line {line}: duplicate update place"));
        }
        if lifts.iter().collect::<BTreeSet<_>>().len() != lifts.len() {
            return Err(format!("line {line}: duplicate lifted requirement"));
        }
        let mut opened = BTreeMap::new();
        let mut matched = BTreeSet::new();
        for name in places {
            let v = self.storage(&Expr {
                kind: Kind::Name(name.clone()),
                line,
            })?;
            self.record_valid(&v, line)?;
            let Symbol::Record(typename, _) = v else {
                return Err(format!(
                    "line {line}: update requires a live local struct place"
                ));
            };
            let def = self.structs.get(&typename).ok_or("unknown update type")?;
            let mut required = Vec::new();
            if let Some(p) = &def.invariant {
                clauses(p, &mut required);
            }
            let names: BTreeSet<_> = required
                .iter()
                .filter_map(|p| {
                    if let Kind::Name(n) = &p.kind {
                        Some(n.as_str())
                    } else {
                        None
                    }
                })
                .collect();
            let mut selected = BTreeSet::new();
            for selector in lifts {
                let (qualifier, fact) = selector
                    .split_once("::")
                    .map(|(q, n)| (Some(q), n))
                    .unwrap_or((None, selector.as_str()));
                if qualifier.is_some_and(|q| q != typename) {
                    continue;
                }
                if names.contains(fact) && def.facts.iter().any(|(n, _)| n == fact) {
                    selected.insert(fact.to_owned());
                    matched.insert(selector.clone());
                }
            }
            opened.insert(name.clone(), selected);
        }
        if matched.len() != lifts.len() {
            return Err(format!("line {line}: lifts must name declared facts used as independent where requirements of an opened place"));
        }
        self.opened = opened;
        let mut locals = Vec::new();
        let mut local_facts = Vec::new();
        let mut local_proofs = Vec::new();
        for statement in body {
            match statement {
                Statement::Assign {target, value} if matches!(target.kind, Kind::Field(..)) && self.update_expression(value) => {
                    let name = root(target).ok_or("update writes must target local struct fields")?;
                    if !self.opened.contains_key(name) { return Err(format!("line {}: {name} was not opened by this update", target.line)); }
                    let old = self.storage(target)?;
                    if !matches!(old, Symbol::Number(..) | Symbol::Bool(_)) { return Err(format!("line {}: updates currently allow only scalar fields; replacing owned fields requires destructor/effect proofs", target.line)); }
                    self.assign(target, value)?;
                }
                Statement::Let {name, value, ..} if self.update_expression(value) => {
                    self.statement(statement)?;
                    let ty = self.env.get(name).ok_or("unknown update local")?.ty();
                    let leaf = matches!(ty, Ty::Machine(_) | Ty::Int | Ty::Nat | Ty::Bool | Ty::Unit) || matches!(ty, Ty::Ref(t) if matches!(*t, Ty::Machine(_) | Ty::Int | Ty::Nat | Ty::Bool));
                    if !leaf {return Err(format!("line {}: update locals require scalar values or scalar borrows, without an open object invariant", value.line));}
                    locals.push(name.clone());
                }
                Statement::Fact {name, value, ..} if self.update_expression(value) => {
                    self.statement(statement)?; local_facts.push(name.clone());
                }
                Statement::Proof {name, proposition, ..} if self.update_expression(proposition) => {self.statement(statement)?; local_proofs.push(name.clone());},
                _ => return Err(format!("line {line}: this operation needs invariant-independent effects; moves, drops, exits, and unknown effects are forbidden while invariants are open")),
            }
        }
        for name in places {
            let value = if let Some(id) = self.roots.get(name) {
                self.memory.get(*id)?.clone()
            } else {
                self.env.get(name).cloned().ok_or("unknown update place")?
            };
            self.record_valid(&value, line)?;
        }
        self.opened.clear();
        for name in locals.into_iter().rev() {
            if let Some(id) = self.roots.remove(&name) {
                self.memory.take(id)?;
            }
            self.env.remove(&name);
        }
        for name in local_facts {
            self.facts.remove(&name);
        }
        for name in local_proofs {
            self.proofs.remove(&name);
        }
        Ok(())
    }

    fn same_layout(&mut self, a: &Symbol, b: &Symbol) -> Result<bool> {
        match (a, b) {
            (Symbol::Record(an, a), Symbol::Record(bn, b)) => {
                if an != bn || a.len() != b.len() {
                    return Ok(false);
                }
                for (name, value) in a {
                    let Some(other) = b.get(name) else {
                        return Ok(false);
                    };
                    if !self.same_layout(value, other)? {
                        return Ok(false);
                    }
                }
                Ok(true)
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
                self.obligations += 1;
                for path in extend(&self.paths, &equal(a, b)?, true)? {
                    if !self.session.probe(&path)? {
                        return Ok(false);
                    }
                }
                match (av, bv) {
                    (Some(a), Some(b)) => {
                        if a.len() != b.len() {
                            return Ok(false);
                        }
                        for (a, b) in a.iter().zip(b) {
                            if !self.same_layout(a, b)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(ai == bi
                        || matches!(
                            **element,
                            Ty::Int | Ty::Nat | Ty::Machine(_) | Ty::Bool | Ty::Ref(_) | Ty::Unit
                        )),
                }
            }
            (Symbol::Number(_, _), Symbol::Number(_, _))
            | (Symbol::Bool(_), Symbol::Bool(_))
            | (Symbol::Ref(..), Symbol::Ref(..))
            | (Symbol::Unit, Symbol::Unit) => Ok(true),
            _ => Ok(false),
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
            Kind::Bool(_) => Some(Ty::Bool),
            Kind::Call(name, args) if name == "old" && args.len() == 1 => Self::old_key(&args[0])
                .ok()
                .and_then(|key| self.old_values.get(&key).map(Symbol::ty)),
            Kind::Call(name, _) if name == "nat" => Some(Ty::Nat),
            Kind::Call(name, _) if name == "int" => Some(Ty::Int),
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
            Kind::Index(base, _) => match self.hint(base)? {
                Ty::Array(element, _) => Some(*element),
                _ => None,
            },
            Kind::Field(base, field) => {
                fn stored<'a>(e: &Expr, env: &'a BTreeMap<String, Symbol>) -> Option<&'a Symbol> {
                    match &e.kind {
                        Kind::Name(n) => env.get(n),
                        Kind::Field(base, field) => match stored(base, env)? {
                            Symbol::Record(_, fields) => fields.get(field),
                            _ => None,
                        },
                        _ => None,
                    }
                }
                match stored(base, &self.env)? {
                    Symbol::Record(_, fields) => fields.get(field).map(Symbol::ty),
                    _ => None,
                }
            }
            Kind::Binary(op, _, _)
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||"
                ) =>
            {
                Some(Ty::Bool)
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
    fn prove_with(
        &mut self,
        goal: &Formula,
        label: &str,
        line: usize,
        steps: Option<&[String]>,
    ) -> Result<()> {
        if let Some(steps) = steps {
            if steps.iter().any(|s| s == "trustme") {
                if steps.len() != 1 {
                    return Err(format!(
                        "line {line}: trustme must be a single explicit proof term"
                    ));
                }
                let mut proposition = Vec::new();
                goal.encode(&mut proposition);
                self.session.trust(&self.paths, &proposition, line, label)?;
                self.obligations += 1;
                return Ok(());
            }
            if let Some(name) = steps.iter().find_map(|s| s.strip_prefix("exact ")) {
                if steps.len() != 1 {
                    return Err(format!(
                        "line {line}: exact must be a single proof term in this subset"
                    ));
                }
                let proven = self.proofs.get(name).ok_or_else(|| format!("line {line}: {name} is not a checked proof; fact declarations are propositions, not assumptions"))?;
                if proven != goal {
                    return Err(format!("line {line}: exact {name} proves a different proposition or an earlier state"));
                }
                self.obligations += 1;
                return Ok(());
            }
        }
        self.prove(goal, label, line)
    }
    fn eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let value = self.eval_inner(e, expected).map_err(|s| {
            if s.starts_with("line ") {
                s
            } else {
                format!("line {}: {s}", e.line)
            }
        })?;
        let projecting_owner = matches!(&e.kind, Kind::Field(..) | Kind::Index(..))
            || matches!(&e.kind, Kind::Unary(op, _) if op == "*");
        if !self.specification && self.symbol_is_affine(&value) && projecting_owner {
            return Err(format!("line {}: moving owning fields or borrowed values needs partial-initialization tracking; unsupported", e.line));
        }
        if let Some(t) = expected {
            self.compatible(&value.ty(), t, e.line)?;
        }
        if matches!(value, Symbol::Record(..) | Symbol::Array { .. }) {
            self.record_valid(&value, e.line)?;
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
    fn symbol_is_affine(&self, value: &Symbol) -> bool {
        match value {
            Symbol::Record(n, _) => is_affine(&Type::Named(n.clone()), self.structs, self.drops),
            Symbol::Array {
                items: Some(xs), ..
            } => xs.iter().any(|v| self.symbol_is_affine(v)),
            Symbol::Array { element, .. } => self.ty_is_affine(element),
            _ => false,
        }
    }
    fn ty_is_affine(&self, t: &Ty) -> bool {
        match t {
            Ty::Record(n) => is_affine(&Type::Named(n.clone()), self.structs, self.drops),
            Ty::Array(t, _) => self.ty_is_affine(t),
            _ => false,
        }
    }
    fn ty_has_reference(&self, t: &Ty) -> bool {
        match t {
            Ty::Ref(_) => true,
            Ty::Array(element, _) => self.ty_has_reference(element),
            Ty::Record(name) => type_has_reference(&Type::Named(name.clone()), self.structs),
            _ => false,
        }
    }
    fn finish_scope(&mut self, f: &Function) -> Result<()> {
        let mut names = f.params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>();
        names.extend(
            f.body
                .iter()
                .flat_map(|s| s.bindings().into_iter().map(str::to_owned)),
        );
        for name in names.into_iter().rev() {
            let value = if let Some(id) = self.roots.get(&name) {
                if self.memory.get(*id).is_err() {
                    continue;
                }
                self.memory.take(*id)?
            } else {
                self.env
                    .get(&name)
                    .cloned()
                    .ok_or("unknown cleanup binding")?
            };
            if self.symbol_is_affine(&value) {
                self.validate_argument(&value, f.result.line)?;
            }
        }
        Ok(())
    }
    fn storage(&mut self, e: &Expr) -> Result<Symbol> {
        match &e.kind {
            Kind::Name(n) => {
                if let Some(id) = self.roots.get(n) {
                    self.memory.get(*id).cloned()
                } else {
                    self.env
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown storage place {n}"))
                }
            }
            Kind::Field(base, name) => {
                let Symbol::Record(_, fields) = self.storage(base)? else {
                    return Err("field access requires struct storage".into());
                };
                fields
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {name}"))
            }
            Kind::Unary(op, _) if op == "*" => {
                let (r, path) = self.location(e)?;
                project(self.memory.read(r)?, &path).cloned()
            }
            Kind::Index(base, index) => {
                let array = self.storage(base)?;
                let index = self.nonnegative(index, "nonnegative storage index")?;
                let Symbol::Array {
                    element,
                    len,
                    items,
                    ..
                } = array
                else {
                    return Err("index requires array storage".into());
                };
                self.prove(
                    &Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?),
                    "storage index < length",
                    e.line,
                )?;
                if index.terms.is_empty() {
                    if let Some(v) = items
                        .as_ref()
                        .and_then(|xs| usize::try_from(index.constant).ok().and_then(|i| xs.get(i)))
                    {
                        return Ok(v.clone());
                    }
                }
                if self.ty_has_reference(&element) {
                    return Err("symbolic reads of reference-containing array elements need an alias contract; unsupported".into());
                }
                self.arbitrary(&element)
            }
            _ => self.eval(e, None),
        }
    }
    fn fact_at(&mut self, place: &Expr, fact: &str, line: usize) -> Result<Formula> {
        if !self.specification {
            return Err(format!(
                "line {line}: named type facts are propositions, not runtime values"
            ));
        }
        let value = self.storage(place)?;
        let Symbol::Record(typename, fields) = &value else {
            return Err("type facts require struct storage".into());
        };
        let def = self
            .structs
            .get(typename)
            .ok_or("unknown fact owner")?
            .clone();
        let expression = def
            .facts
            .iter()
            .find(|(name, _)| name == fact)
            .map(|(_, p)| p.clone())
            .ok_or_else(|| format!("unknown fact {typename}::{fact}"))?;
        let saved = self.env.clone();
        let roots = self.roots.clone();
        let facts = self.facts.clone();
        self.env = fields.clone();
        self.env.insert("self".into(), value);
        self.roots.clear();
        self.facts = def.facts.iter().cloned().collect();
        let result = self.proposition(&expression);
        self.env = saved;
        self.roots = roots;
        self.facts = facts;
        result
    }

    fn validate_argument(&mut self, value: &Symbol, line: usize) -> Result<()> {
        if let Symbol::Ref(_, r, path) = value {
            let target = project(self.memory.read(*r)?, path)?.clone();
            self.validate_argument(&target, line)?;
        } else {
            self.record_valid(value, line)?;
        }
        Ok(())
    }

    fn validate_live(&mut self, line: usize) -> Result<()> {
        let values = self
            .env
            .iter()
            .filter_map(|(name, value)| {
                if let Some(id) = self.roots.get(name) {
                    self.memory.get(*id).ok().cloned()
                } else {
                    Some(value.clone())
                }
            })
            .collect::<Vec<_>>();
        for value in values {
            self.record_valid(&value, line)?;
        }
        Ok(())
    }
    fn eval_inner(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        match &e.kind {
            Kind::FactAt(place, name) => Ok(Symbol::Bool(self.fact_at(place, name, e.line)?)),
            Kind::Unit => Ok(Symbol::Unit),
            Kind::Constant(t, n) => Ok(Symbol::Number(Ty::Machine(*t), Linear::number(*n))),
            Kind::Number(n) => Ok(Symbol::Number(
                match expected {
                    Some(Ty::Nat) => Ty::Nat,
                    Some(Ty::Machine(t)) => Ty::Machine(*t),
                    _ => self.number_type(),
                },
                Linear::number(*n),
            )),
            Kind::Bool(b) => Ok(Symbol::Bool(if *b {
                Formula::True
            } else {
                Formula::False
            })),
            Kind::Name(n) => {
                // A struct's field bindings shadow caller-side logical names.
                // Never let an unrelated fact redefine a type invariant.
                if !self.env.contains_key(n) {
                    if let Some(definition) = self.facts.get(n).cloned() {
                        if !self.specification {
                            return Err(format!(
                                "fact {n} is a proof-only proposition, not a runtime boolean"
                            ));
                        }
                        return self.eval(&definition, Some(&Ty::Bool));
                    }
                    if self.proofs.contains_key(n) {
                        return Err(format!("{n} is a proof witness; reference it with exact"));
                    }
                }

                let value = if let Some(id) = self.roots.get(n) {
                    self.memory.get(*id).cloned()
                } else {
                    self.env
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown value {n}"))
                }?;
                if !self.specification && self.symbol_is_affine(&value) {
                    if self.dropping {
                        return Err("destructor receivers and owned fields cannot be moved in this initial destructor subset".into());
                    }
                    let (r, _) = self.location(e)?;
                    let id = self.memory.plane(r)?;
                    self.memory.take(id)?;
                }
                Ok(value)
            }
            Kind::Field(base, name) => {
                let Symbol::Record(_, fields) = self.storage(base)? else {
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
                if def.ideal && !self.ideal && !self.specification {
                    return Err(format!(
                        "{name} is ideal data and cannot be constructed at runtime"
                    ));
                }
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
                    let evaluated = if let Type::Array(element, _) = ty {
                        // Supply the element type now; the complete dependent
                        // field type is checked once all literal fields exist.
                        let element = self.resolve(element)?;
                        self.eval_inner(
                            value,
                            Some(&Ty::Array(Box::new(element), Linear::number(0))),
                        )?
                    } else {
                        self.eval(value, hint.as_ref())?
                    };
                    fields.insert(n.clone(), evaluated);
                }
                self.env = saved;
                let record = Symbol::Record(name.clone(), fields);
                self.record_valid(&record, e.line)?;
                Ok(record)
            }
            Kind::Unary(op, x) if op == "&" => {
                let (r, path) = self.location(x)?;
                let target = project(self.memory.read(r)?, &path)?.clone();
                self.record_valid(&target, e.line)?;
                let ty = target.ty();
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
                    .unwrap_or_else(|| self.number_type());
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
                .unwrap_or_else(|| self.number_type());
                if matches!(ty, Ty::Bool) && matches!(op.as_str(), "==" | "!=") {
                    let a = self.eval(a, Some(&Ty::Bool))?;
                    let b = self.eval(b, Some(&Ty::Bool))?;
                    let equal = self.symbol_equal(&a, &b)?;
                    return Ok(Symbol::Bool(if op == "==" { equal } else { equal.not() }));
                }
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
                    self.hint(first).unwrap_or_else(|| self.number_type())
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
                if self.ty_has_reference(&element) {
                    return Err("symbolic reads of reference-containing array elements need an alias contract; unsupported".into());
                }
                let key = format!("evg_read_{identity}_{index:?}");
                if let Some(v) = self.env.get(&key) {
                    return Ok(v.clone());
                }
                let v = self.arbitrary(&element)?;
                self.env.insert(key, v.clone());
                Ok(v)
            }
            Kind::Call(name, args) => {
                if name == "old" {
                    if !self.specification || args.len() != 1 {
                        return Err(
                            "old is proof-only and takes one entry-state parameter expression"
                                .into(),
                        );
                    }
                    let key = Self::old_key(&args[0])?;
                    return self
                        .old_values
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| format!("{key} is not a function entry parameter"));
                }
                if name == "int" || name == "nat" {
                    if !self.ideal && !self.specification {
                        return Err("mathematical views are proof-only".into());
                    }
                    if args.len() != 1 {
                        return Err(format!("{name} expects one integer"));
                    }
                    let n = self.eval(&args[0], None)?.number()?;
                    if name == "nat" {
                        self.prove(&Formula::Ge(n.clone()), "nonnegative natural view", e.line)?;
                    }
                    return Ok(Symbol::Number(
                        if name == "nat" { Ty::Nat } else { Ty::Int },
                        n,
                    ));
                }
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
                    let stored = self.memory.read(r)?.clone();
                    self.record_valid(&stored, e.line)?;
                    let value = self.memory.take(id)?;
                    self.validate_argument(&value, e.line)?;
                    return Ok(if name == "drop" { Symbol::Unit } else { value });
                }
                let f = self.functions.get(name).cloned().ok_or_else(|| format!("unknown function {name}; calls require an earlier verified declaration (recursion is not supported yet)"))?;
                if !f.modifies.is_empty() && self.specification {
                    return Err("modifying calls are forbidden in proof expressions".into());
                }
                if f.ideal && !self.ideal && !self.specification {
                    return Err(format!(
                        "{name} is ideal code and cannot be called at runtime"
                    ));
                }
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
                    let value = self.eval(arg, hint.as_ref())?;
                    self.validate_argument(&value, e.line)?;
                    actuals.push(value);
                }
                let mut saved = self.env.clone();
                let saved_roots = self.roots.clone();
                let saved_old = self.old_values.clone();
                self.env.clear();
                self.roots.clear();
                for ((n, t), value) in f.params.iter().zip(actuals) {
                    let t = self.resolve(t)?;
                    self.compatible(&value.ty(), &t, e.line)?;
                    self.env.insert(n.clone(), value);
                }
                self.capture_old()?;
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
                for parameter in &f.modifies {
                    let Some(Symbol::Ref(ty, reference, fields)) = self.env.get(parameter).cloned()
                    else {
                        return Err("modifies requires a scalar reference parameter".into());
                    };
                    let id = self.memory.plane(reference)?;
                    if !saved_roots.values().any(|p| *p == id) && !self.writable.contains(&id) {
                        return Err(format!("line {}: call to {name} writes through a parameter without a modifies contract", e.line));
                    }
                    let new = self.arbitrary(&ty)?;
                    let mut root = self.memory.read(reference)?.clone();
                    replace_projection(&mut root, &fields, new, &mut self.fresh)?;
                    self.memory.write(id, root.clone(), false)?;
                    for (binding, plane) in &saved_roots {
                        if *plane == id {
                            saved.insert(binding.clone(), root.clone());
                        }
                    }
                }
                self.env.insert("result".into(), value.clone());
                if let Some(post) = &f.post {
                    let p = self.proposition(post)?;
                    self.assume(&p)?;
                }
                self.env = saved;
                self.roots = saved_roots;
                self.old_values = saved_old;
                if !f.modifies.is_empty() {
                    self.validate_live(e.line)?;
                }
                Ok(value)
            }
            Kind::If(condition, yes, no) => {
                let p = self.eval(condition, Some(&Ty::Bool))?.proposition()?;
                let base = self.paths.clone();
                // Give caller bindings stable storage identities before forking.
                for (name, value) in self.env.clone() {
                    if !self.roots.contains_key(&name) {
                        self.roots.insert(name, self.memory.allocate(value)?);
                    }
                }
                let env = self.env.clone();
                let roots = self.roots.clone();
                let store = self.memory.snapshot();
                self.paths = extend(&base, &p, false)?;
                let a = self.eval(yes, expected)?;
                let a_paths = self.paths.clone();
                let a_store = self.memory.snapshot();
                self.paths = extend(&base, &p, true)?;
                self.env = env.clone();
                self.roots = roots.clone();
                self.memory = store.snapshot();
                let b = self.eval(no, Some(&a.ty()))?;
                let b_paths = self.paths.clone();
                let b_store = self.memory.snapshot();
                self.paths = base;
                self.env = env;
                self.roots = roots;
                self.memory = store.snapshot();
                let mut state_a = Formula::True;
                let mut state_b = Formula::True;
                let a_states = a_store.states();
                let b_states = b_store.states();
                for (index, (id, generation, original)) in store.states().into_iter().enumerate() {
                    let (_, ag, av) = a_states.get(index).ok_or("missing branch plane")?;
                    let (_, bg, bv) = b_states.get(index).ok_or("missing branch plane")?;
                    if ag != bg {
                        return Err("conditional branches have different ownership or storage generations; conditional shapes are not implemented".into());
                    }
                    match (av, bv) {
                        (Some(av), Some(bv)) if *ag == generation => {
                            let (joined, left, right) = self.join_value(av, bv)?;
                            self.memory.write(id, joined, false)?;
                            state_a = state_a.and(left);
                            state_b = state_b.and(right);
                        }
                        (None, None) => {
                            let expected = if original.is_some() {generation.checked_add(1).ok_or("plane generation exhausted")?} else {generation};
                            if *ag != expected { return Err("conditional storage generation cannot be joined".into()); }
                            if original.is_some() { self.memory.take(id)?; }
                        }
                        _ => return Err("conditional branches must leave the same live bindings and storage layout".into()),
                    }
                }
                for (name, id) in &self.roots {
                    if let Ok(value) = self.memory.get(*id) {
                        self.env.insert(name.clone(), value.clone());
                    }
                }
                let result = self.arbitrary(&a.ty())?;
                let relation_a = state_a.and(self.symbol_equal(&result, &a)?);
                let relation_b = state_b.and(self.symbol_equal(&result, &b)?);
                let mut paths = extend(&a_paths, &relation_a, false)?;
                paths.extend(extend(&b_paths, &relation_b, false)?);
                // Drop infeasible branch combinations only with a checked
                // contradiction certificate; a failed probe keeps the path.
                if paths.len() > 1 {
                    let mut feasible = Vec::new();
                    for path in paths {
                        if !self.session.probe(&path)? {
                            feasible.push(path);
                        }
                    }
                    paths = feasible;
                }
                if paths.len() > 64 {
                    return Err("verification path limit reached (64)".into());
                }
                self.paths = paths;
                Ok(result)
            }
        }
    }
    fn join_value(&mut self, a: &Symbol, b: &Symbol) -> Result<(Symbol, Formula, Formula)> {
        if a == b {
            return Ok((a.clone(), Formula::True, Formula::True));
        }
        match (a, b) {
            (Symbol::Number(at, _), Symbol::Number(bt, _)) if at == bt => {
                let value = self.arbitrary(at)?;
                Ok((
                    value.clone(),
                    self.symbol_equal(&value, a)?,
                    self.symbol_equal(&value, b)?,
                ))
            }
            (Symbol::Bool(_), Symbol::Bool(_)) => {
                let value = self.arbitrary(&Ty::Bool)?;
                Ok((
                    value.clone(),
                    self.symbol_equal(&value, a)?,
                    self.symbol_equal(&value, b)?,
                ))
            }
            (Symbol::Record(an, a), Symbol::Record(bn, b)) if an == bn && a.len() == b.len() => {
                let mut fields = BTreeMap::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for (name, value) in a {
                    let (value, l, r) =
                        self.join_value(value, b.get(name).ok_or("branch fields differ")?)?;
                    fields.insert(name.clone(), value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((Symbol::Record(an.clone(), fields), left, right))
            }
            (
                Symbol::Array {
                    element,
                    len,
                    items: Some(a),
                    ..
                },
                Symbol::Array {
                    element: be,
                    len: bl,
                    items: Some(b),
                    ..
                },
            ) if element == be && len == bl && a.len() == b.len() => {
                let mut values = Vec::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for (a, b) in a.iter().zip(b) {
                    let (value, l, r) = self.join_value(a, b)?;
                    values.push(value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((
                    Symbol::Array {
                        element: element.clone(),
                        len: len.clone(),
                        items: Some(values),
                        identity: self.fresh_name(),
                    },
                    left,
                    right,
                ))
            }
            _ => Err(
                "conditional storage joins require matching layouts and stable references".into(),
            ),
        }
    }
    fn symbol_equal(&self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        match (a, b) {
            (Symbol::Number(_, a), Symbol::Number(_, b)) => equal(a, b),
            (Symbol::Bool(a), Symbol::Bool(b)) => Ok(a
                .clone()
                .and(b.clone())
                .or(a.clone().not().and(b.clone().not()))),
            (Symbol::Unit, Symbol::Unit) => Ok(Formula::True),
            (Symbol::Record(an, a), Symbol::Record(bn, b)) if an == bn && a.len() == b.len() => {
                let mut relation = Formula::True;
                for (field, value) in a {
                    let other = b.get(field).ok_or("conditional record fields differ")?;
                    relation = relation.and(self.symbol_equal(value, other)?);
                }
                Ok(relation)
            }
            _ => Err("conditional values need matching scalar or record fields; array and reference joins are not supported yet".into()),
        }
    }
}

#[derive(Debug)]
pub struct VerifiedProgram {
    pub(crate) functions: Vec<Function>,
    pub(crate) structs: BTreeMap<String, Struct>,
    pub obligations: usize,
    pub(crate) drops: BTreeSet<String>,
    trusted: Vec<crate::certificate::TrustedAssumption>,
    proof_searches: usize,
}

impl VerifiedProgram {
    pub fn trusted_assumptions(&self) -> &[crate::certificate::TrustedAssumption] {
        &self.trusted
    }
    pub fn proof_search_count(&self) -> usize {
        self.proof_searches
    }
    pub(crate) fn check_entry(&self) -> Result<()> {
        let main = self
            .functions
            .iter()
            .find(|f| f.name == "main")
            .ok_or("run requires fn main()")?;
        if main.ideal {
            return Err(
                "main is ideal code; proof computations are erased and cannot execute".into(),
            );
        }
        if !main.params.is_empty() {
            return Err("main requires no arguments".into());
        }
        if let Some(pre) = &main.pre {
            let functions = self
                .functions
                .iter()
                .map(|f| (f.name.clone(), f.clone()))
                .collect();
            let helpers = BTreeSet::new();
            let mut session = Session::search();
            let mut ctx = Context::new(
                &functions,
                &self.structs,
                &self.drops,
                &helpers,
                &mut session,
            );
            ctx.current = Some("main".into());
            let p = ctx.proposition(pre)?;
            ctx.prove(&p, "entry precondition of main", pre.line)?;
        }
        Ok(())
    }
}

pub fn verify(source: &str) -> Result<VerifiedProgram> {
    let mut session = Session::search();
    let program = verify_using(source, &mut session)?;
    session.finish()?;
    Ok(program)
}
pub fn prove(source: &str) -> Result<(VerifiedProgram, ProofBundle)> {
    let mut session = Session::recording();
    let program = verify_using(source, &mut session)?;
    session.finish()?;
    Ok((program, session.bundle(source)?))
}
pub fn verify_with_certificate(source: &str, bundle: &ProofBundle) -> Result<VerifiedProgram> {
    bundle.check_source(source)?;
    let mut session = Session::replay(bundle);
    let program = verify_using(source, &mut session)?;
    session.finish()?;
    Ok(program)
}
fn verify_using(source: &str, session: &mut Session) -> Result<VerifiedProgram> {
    let parsed = syntax::parse(source)?;
    let mut structs = BTreeMap::new();
    let empty_functions = BTreeMap::new();
    let empty_drops = BTreeSet::new();
    for s in &parsed.structs {
        if structs.contains_key(&s.name) {
            return Err(format!("line {}: duplicate struct {}", s.line, s.name));
        }
        let mut ctx = Context::new(
            &empty_functions,
            &structs,
            &empty_drops,
            &empty_drops,
            session,
        );
        ctx.ideal = s.ideal;
        for (n, t) in &s.fields {
            if !s.ideal && !runtime_type(t, &structs) {
                return Err(format!(
                    "line {}: field {n} needs a runtime layout; use ideal type for proof data",
                    s.line
                ));
            }
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
        for (name, proposition) in &s.facts {
            ctx.fresh_binding(name, proposition.line)?;
            ctx.proposition(proposition)?;
            ctx.facts.insert(name.clone(), proposition.clone());
        }
        if let Some(p) = &s.invariant {
            ctx.proposition(p)?;
        }
        structs.insert(s.name.clone(), s.clone());
    }
    let mut functions = BTreeMap::new();
    let mut drops = BTreeSet::new();
    let mut helpers = BTreeSet::new();
    for (target, f) in &parsed.destructors {
        if structs.get(target).is_some_and(|s| s.ideal) {
            return Err(format!(
                "line {}: ideal data has no runtime Drop implementation",
                f.line
            ));
        }
        if !structs.contains_key(target) || !drops.insert(target.clone()) {
            return Err(format!(
                "line {}: unknown or duplicate Drop implementation for {target}",
                f.line
            ));
        }
        if !destructor_body(&f.body) || !destructor_expression(&f.result) {
            return Err(format!("line {}: destructor effects require proofs; initial Drop bodies allow local scalar work and facts, without calls, borrowing, or allocation", f.line));
        }
    }
    let mut all_functions = parsed.functions;
    all_functions.extend(parsed.destructors.into_iter().map(|(_, f)| f));
    let mut obligations = 0;
    for f in &all_functions {
        if !f.modifies.is_empty() {
            let references = f
                .params
                .iter()
                .filter(|(_, t)| type_has_reference(t, &structs))
                .collect::<Vec<_>>();
            if f.ideal
                || f.modifies.len() != 1
                || references.len() != 1
                || references[0].0 != f.modifies[0]
                || !matches!(&references[0].1, Type::Ref(t) if matches!(**t, Type::Machine(_) | Type::Bool))
            {
                return Err(format!("line {}: initial modifies contracts require exactly one scalar reference parameter and no other borrowed parameters; alias contracts are not implemented", f.line));
            }
        }
        if !f.ideal
            && (!runtime_type(&f.ret, &structs)
                || f.params.iter().any(|(_, t)| !runtime_type(t, &structs)))
        {
            return Err(format!("line {}: runtime signatures require fixed-layout types; int/nat and ideal records are proof-only", f.line));
        }
        if matches!(f.name.as_str(), "move" | "drop" | "int" | "nat" | "old") {
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
        let mut ctx = Context::new(&available, &structs, &drops, &helpers, session);
        ctx.dropping = f.drop_target.is_some();
        ctx.ideal = f.ideal;
        ctx.current = Some(f.name.clone());
        for (n, t) in &f.params {
            if ctx.env.contains_key(n) {
                return Err(format!("line {}: duplicate parameter {n}", f.line));
            }
            let ty = ctx.resolve(t)?;
            let value = ctx.arbitrary(&ty)?;
            ctx.env.insert(n.clone(), value);
        }
        ctx.capture_old()?;
        for parameter in &f.modifies {
            if let Some(Symbol::Ref(_, reference, _)) = ctx.env.get(parameter) {
                ctx.writable.insert(ctx.memory.plane(*reference)?);
            }
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
            ctx.statement(statement)?;
        }
        let value = ctx.eval(&f.result, Some(&ret))?;
        ctx.validate_live(f.result.line)?;
        ctx.finish_scope(f)?;
        if let Some(post) = &f.post {
            ctx.specification = true;
            ctx.env = contract_env;
            ctx.roots.clear();
            ctx.env.insert("result".into(), value);
            let local_facts = std::mem::take(&mut ctx.facts);
            let p = ctx.eval(post, Some(&Ty::Bool))?.proposition()?;
            ctx.facts = local_facts;
            ctx.prove_with(
                &p,
                &format!("postcondition of {}", f.name),
                post.line,
                f.proof.as_deref(),
            )?;
        } else if f.proof.is_some() {
            return Err(format!(
                "line {}: a function proof block requires an ensures proposition",
                f.line
            ));
        }
        obligations += ctx.obligations;
        if crate::effects::invariant_independent(f, &functions, &helpers) {
            helpers.insert(f.name.clone());
        }
        functions.insert(f.name.clone(), f.clone());
    }
    Ok(VerifiedProgram {
        functions: all_functions,
        structs,
        obligations,
        drops,
        trusted: session.trusted_assumptions().to_vec(),
        proof_searches: session.search_count(),
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn evergreen_counter_library_checks_boundaries_and_refines_rc_counts() {
        let library = include_str!("../stdlib/counter.evg");
        for initial in [0u64, 1, u64::MAX - 1, u64::MAX] {
            let expected = initial.saturating_add(1);
            let success = initial < u64::MAX;
            let source = format!("{library}\nfn main() -> usize ensures (result == {expected}) {{let count: usize = {initial}; let success = counter_try_increment(&count); proof flag: success == {success}; count}}");
            assert_eq!(
                verify(&source).unwrap().run().unwrap().to_string(),
                expected.to_string()
            );
            if initial > 0 {
                let expected = initial - 1;
                let zero = expected == 0;
                let source = format!("{library}\nfn main() -> usize ensures (result == {expected}) {{let count: usize = {initial}; let zero = counter_decrement(&count); proof flag: zero == {zero}; count}}");
                assert_eq!(
                    verify(&source).unwrap().run().unwrap().to_string(),
                    expected.to_string()
                );
            }
        }
        for bad in [
            include_str!("../examples/reject_counter_underflow.evg"),
            include_str!("../examples/reject_counter_overflow.evg"),
        ] {
            assert!(verify(&format!("{library}\n{bad}")).is_err());
        }
        let source = [
            include_str!("../proofs/rc_protocol.evg"),
            library,
            include_str!("../proofs/rc_count_refinement.evg"),
        ]
        .join("\n");
        assert!(verify(&source).is_ok());
        let alternative = source.replace(
            "let success = counter_increment(count);",
            "let success = counter_try_increment(count);",
        );
        assert!(verify(&alternative).is_ok());
        let broken = source.replace("*count = *count - 1;", "*count = *count;");
        assert!(verify(&broken).is_err());
    }

    #[test]
    fn symbolic_array_reads_are_versioned_after_writes() {
        let prefix = "fn increment(r: &usize) where (*r < usize::MAX) modifies(r) ensures (*r == old(*r) + 1) {*r = *r + 1;}";
        for mutation in [
            "let r = &a[0]; *r = 1;",
            "increment(&a[0]);",
            "let x = if true {increment(&a[0])} else {()};",
        ] {
            let source = format!("{prefix} fn unchanged(i: usize) -> bool where (i < 1) ensures (result) {{let a: [usize; 1] = [0]; let before = a[i]; {mutation} a[i] == before}}");
            assert!(
                verify(&source).is_err(),
                "stale array read survived {mutation}"
            );
        }
        let unchanged = "fn unchanged(i: usize) -> bool where (i < 1) ensures (result) {let a: [usize; 1] = [0]; let before = a[i]; a[i] == before}";
        assert!(verify(unchanged).is_ok());
        let copy = "fn unchanged(i: usize) -> bool where (i < 1) ensures (result) {let a: [usize; 1] = [0]; let snapshot = a; let before = snapshot[i]; let r = &a[0]; *r = 1; snapshot[i] == before}";
        assert!(verify(copy).is_ok());
        let alias = "fn bad(i: usize) -> bool where (i < 1) ensures (result) {let n: usize = 0; let a: [&usize; 1] = [&n]; let before = *a[i]; n = 1; *a[i] == before}";
        assert!(verify(alias).unwrap_err().contains("alias contract"));
        let concrete = "fn main() -> usize ensures (result == 1) {let n: usize = 0; let a: [&usize; 1] = [&n]; n = 1; *a[0]}";
        assert_eq!(verify(concrete).unwrap().run().unwrap().to_string(), "1");
    }

    #[test]
    fn conditional_stores_join_effects_without_leaking_branch_assumptions() {
        let source = include_str!("../examples/conditional_writes.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert!(verify(&source.replace(
            "maybe_increment(alias, false)",
            "maybe_increment(alias, true)"
        ))
        .is_err());
        assert!(
            verify(&source.replace("*alias + counters.right", "*alias + counters.right + 1"))
                .is_err()
        );
        let declarations = source.split("type Counters").next().unwrap();
        let invalid = "fn bad(r: &usize, flag: bool) where (*r < usize::MAX) modifies(r) ensures (*r == old(*r) + 1) {if flag {increment(r)} else {()}}";
        assert!(verify(&format!("{declarations}\n{invalid}")).is_err());
        let array = "fn main() -> usize ensures (result == 41) {let a: [usize; 2] = [40, 7]; let alias = &a[0]; let x = if false {()} else {increment(alias)}; proof frame: a[1] == 7; *alias}";
        assert_eq!(
            verify(&format!("{declarations}\n{array}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "41"
        );
        let nested = "fn main() -> usize ensures (result == 2) {let n: usize = 0; let x = if true {if false {()} else {increment(&n)}} else {()}; increment(&n); n}";
        assert_eq!(
            verify(&format!("{declarations}\n{nested}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "2"
        );
    }

    #[test]
    fn branches_must_agree_on_consumed_ownership() {
        let declarations = "affine type Token struct {tag: usize} fn consume(t: Token) -> usize ensures (result == t.tag) {t.tag}";
        let valid = "fn main() -> usize ensures (result == 7) {let t = Token {tag: 7}; if true {consume(t)} else {consume(t)}}";
        assert_eq!(
            verify(&format!("{declarations}\n{valid}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "7"
        );
        let invalid = "fn main() -> usize {let t = Token {tag: 7}; let x = if true {consume(t)} else {0}; t.tag}";
        assert!(verify(&format!("{declarations}\n{invalid}")).is_err());
        let invalid = valid.replace(
            "if true {consume(t)} else {consume(t)}",
            "let x = if true {consume(t)} else {consume(t)}; t.tag",
        );
        assert!(verify(&format!("{declarations}\n{invalid}")).is_err());
    }

    #[test]
    fn scalar_write_contracts_update_aliases_and_frame_other_fields() {
        let source = include_str!("../examples/write_contracts.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert!(verify(&source.replace("modifies(r)", "")).is_err());
        assert!(verify(&source.replace("where (*r < usize::MAX)", "")).is_err());
        assert!(verify(&source.replace("old(*r) + 2", "old(*r) + 3")).is_err());
        let declarations = source.split("type Counters").next().unwrap();
        for body in [
            "fn wrapper(r: &usize) {increment(r);}",
            "fn wrapper(r: &usize, other: &usize) modifies(r) {*r = 1;}",
            "fn main() -> usize {let n: usize = 0; proof p: old(n) == 0; n}",
            "fn main() -> usize {let n: usize = 0; proof p: n == 0; increment(&n); proof stale: n == 0 by {exact p}; n}",
            "type Balanced struct {left: usize, right: usize} where (left == right); fn main() -> usize {let p = Balanced {left: 0, right: 0}; increment(&p.left); p.left}",
        ] {
            assert!(verify(&format!("{declarations}\n{body}")).is_err(), "{body}");
        }
        let bounded = "type Bounded struct {value: usize} where (value <= 10); fn main() -> usize ensures (result == 10) {let p = Bounded {value: 9}; increment(&p.value); p.value}";
        assert_eq!(
            verify(&format!("{declarations}\n{bounded}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "10"
        );
        let runtime_old = "fn f(n: usize) -> usize {old(n)}";
        assert!(verify(runtime_old).is_err());
        let proof_effect = "fn main() -> usize {let n: usize = 0; proof p: increment(&n) == 0; n}";
        assert!(verify(&format!("{declarations}\n{proof_effect}")).is_err());
    }

    #[test]
    fn boolean_write_contracts_use_entry_snapshots() {
        let source = "fn flip(r: &bool) -> () modifies(r) ensures (*r == !old(*r)) {*r = !*r;} fn main() -> bool ensures (result == true) {let value = false; flip(&value); value == (1 < 2)}";
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "true");
        assert!(
            verify(&source.replace("ensures (*r == !old(*r))", "ensures (*r == old(*r))")).is_err()
        );
    }

    #[test]
    fn complete_patterns_transfer_each_field_without_partial_moves() {
        let source = include_str!("../examples/destructure.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        for replacement in [
            "Pair {left: first}",
            "Pair {left: first, left: second}",
            "Pair {left: first, right: first}",
            "Pair {unknown: first, right: second}",
            "Permit {left: first, right: second}",
        ] {
            assert!(
                verify(&source.replace("Pair {left: first, right: second}", replacement)).is_err()
            );
        }
        assert!(
            verify(&source.replace("let a = consume(first);", "let a = pair.left.tag;")).is_err()
        );
        assert!(
            verify(&source.replace("let b = consume(second);", "let b = consume(first);")).is_err()
        );
        let destructor = "type Guard struct {tag: usize} impl Drop for Guard {fn drop(self) {}} fn main() -> usize {let g = Guard {tag: 7}; let Guard {tag} = g; tag}";
        assert!(verify(destructor).unwrap_err().contains("bypass"));
        let ideal = "ideal affine type Ticket struct {tag: nat} ideal type Pair struct {left: Ticket, right: Ticket} ideal fn split() -> nat {let pair = Pair {left: Ticket {tag: 2}, right: Ticket {tag: 3}}; let Pair {left, right} = pair; left.tag + right.tag}";
        assert!(verify(ideal).is_ok());
        let credits = include_str!("../proofs/affine_credits.evg");
        assert!(verify(credits).is_ok());
        let duplicate = format!(
            "{credits}\n{}",
            include_str!("../proofs/reject_duplicate_credit.evg")
        );
        assert!(verify(&duplicate).unwrap_err().contains("shape(T)"));
    }

    #[test]
    fn affine_values_move_without_requiring_a_destructor() {
        let source = include_str!("../examples/affine_values.evg");
        let program = verify(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert!(program.drops.is_empty());
        for body in [
            "let p = Permit {tag: 1}; let q = p; p.tag",
            "let p = Permit {tag: 1}; let q = transfer(p); consume(p)",
            "let e = Envelope {permit: Permit {tag: 1}}; let q = e; e.permit.tag",
            "let a = [Permit {tag: 1}]; let b = a; a[0].tag",
            "let p = Permit {tag: 1}; drop(p); p.tag",
        ] {
            let declarations = source.split("fn main()").next().unwrap();
            assert!(
                verify(&format!("{declarations} fn main() -> usize {{{body}}}")).is_err(),
                "{body}"
            );
        }
        let duplicate = "ideal affine type Ticket struct {tag: nat} ideal fn forward(t: Ticket) -> Ticket {t} ideal fn duplicate() -> nat {let t = Ticket {tag: 7}; let u = forward(t); let v = forward(t); 0}";
        assert!(verify(duplicate).is_err());
        assert!(verify("affine fn main() -> usize {0}").is_err());
        assert!(verify("ideal affine fn main() -> nat {0}").is_err());
    }

    #[test]
    fn conditional_records_preserve_branch_relations_and_nested_types() {
        let source = include_str!("../examples/conditional_records.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert!(verify(&source.replace(
            "Pair {chosen: Checked {value: 42}",
            "Pair {chosen: Checked {value: 0}"
        ))
        .is_err());
        assert!(verify(&source.replace("choose(true,", "choose(false,")).is_err());
        let source = "fn noop(flag: bool) -> () {if flag {()} else {()}} fn main() -> usize {let x = noop(false); 42}";
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn trusted_function_contracts_remain_audited_at_callers() {
        let source = "fn external() -> usize ensures (result == 99) {0} proof {trustme} fn main() -> usize ensures (result == 99) {external()}";
        let program = verify(source).unwrap();
        assert_eq!(program.trusted_assumptions().len(), 1);
        assert!(program.trusted_assumptions()[0].goal.contains("external"));
        // Erased assumptions can lie about runtime behavior, so the audit must
        // survive even when downstream obligations use only checked arithmetic.
        assert_eq!(program.run().unwrap().to_string(), "0");
        assert!(verify(&source.replace("trustme", "omega")).is_err());
    }

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
        let prefix =
            "fn inc(n: usize) -> usize where (n < 10) ensures (result == n + 1) { n + 1 } ";
        assert!(verify(&format!(
            "{prefix} fn main() -> usize ensures (result == 5) {{ inc(4) }}"
        ))
        .is_ok());
        assert!(verify(&format!("{prefix} fn main() -> usize {{ inc(10) }}")).is_err());
    }
    #[test]
    fn verifies_both_branches_and_natural_subtraction() {
        verify("ideal fn abs(n: int) -> int ensures (result >= 0) { if n >= 0 { n } else { -n } }")
            .unwrap();
        verify("ideal fn sub(n: nat) -> nat ensures (result <= n) { n - 1 }").unwrap();
        assert!(verify(
            "fn bad(n: isize) -> isize ensures (result >= 0) { if n >= 0 { n } else { n } }"
        )
        .is_err());
    }
    #[test]
    fn facts_are_proved_before_use() {
        assert!(verify("fn bad(n: usize) -> usize { proof lie: n < 0; n }").is_err());
        assert!(verify("fn bad() -> usize { proof h: true by { exact missing }; 0 }").is_err());
        assert!(verify("fn bad() -> usize { result }").is_err());
    }
    #[test]
    fn arrays_and_types_are_checked() {
        verify("fn main() -> usize ensures (result == 20) { let a: [usize; 2] = [10, 20]; a[1] }")
            .unwrap();
        for s in [
            "fn f() -> usize { let a: [usize; 2] = [1]; 0 }",
            "fn f() -> usize { let a: [usize; 1] = [1]; a[1] }",
            "fn f() -> usize { -1 }",
            "fn f() -> bool { 1 }",
        ] {
            assert!(verify(s).is_err(), "{s}");
        }
    }
    #[test]
    fn compound_logic_and_contradictory_preconditions() {
        verify("fn f(n: usize) -> usize where (n < 3 || n > 10) ensures (result != 5) { n }")
            .unwrap();
        verify("fn f(n: usize) -> usize where (n < 0) ensures (result > 100) { n }").unwrap();
    }

    #[test]
    fn struct_invariants_and_atomic_replacement() {
        let prefix = "type Buffer struct { len: usize, cap: usize } where (len <= cap); ";
        let valid = format!("{prefix} fn main() -> usize {{ let b = Buffer {{ len: 1, cap: 2 }}; b = Buffer {{ len: b.len + 2, cap: b.cap + 2 }}; b.len }}");
        assert_eq!(verify(&valid).unwrap().run().unwrap().to_string(), "3");
        for body in [
            "let b = Buffer {len: 3, cap: 2}; b.len",
            "let b = Buffer {len: 1, cap: 2}; b.len = 3; b.len",
            "let b = Buffer {len: 1}; b.len",
            "let b = Buffer {len: 1, cap: 2, extra: 0}; b.len",
        ] {
            assert!(
                verify(&format!("{prefix} fn main() -> usize {{ {body} }}")).is_err(),
                "{body}"
            );
        }
    }

    #[test]
    fn dependent_struct_fields_and_nested_invariants() {
        let s = "type Storage struct { len: usize, data: [isize; len] } type Outer struct { storage: Storage } fn main() -> isize { let s = Storage {len: 2, data: [10, 20]}; let o = Outer {storage: s}; o.storage.data[1] }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "20");
        assert!(verify("type Storage struct {len: usize, data: [isize; len]} fn main() -> usize {let s = Storage {len: 2, data: [1, 2]}; s.len = 3; 0}").is_err());
        assert!(verify("type Inner struct {x: usize} where (x > 0); type Outer struct {inner: Inner} fn main() -> usize {let o = Outer {inner: Inner {x: 1}}; o.inner.x = 0; 0}").is_err());
    }

    #[test]
    fn contracts_capture_entry_parameters() {
        assert!(verify("fn bad(n: usize) -> usize ensures (result == n) { n = 0; n }").is_err());
        let s = "fn reset(n: usize) -> usize ensures (result == 0) { n = 0; n } fn main() -> usize ensures (result == 0) {reset(10)}";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "0");
    }

    #[test]
    fn aliased_references_share_scalar_updates() {
        let s = "fn read(r: &usize) -> usize ensures (result == *r) { *r } fn main() -> usize ensures (result == 7) { let x: usize = 1; let a = &x; let b = &x; *a = 7; read(b) }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "7");
        let s = "fn main() -> usize ensures (result == 11) { let data: [usize; 2] = [1, 2]; let a = &data[0]; let b = &data[1]; *a = 9; *b = 11; *b }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "11");
    }

    #[test]
    fn stale_references_are_compile_errors() {
        for body in [
            "let x: usize = 1; let r = &x; drop(x); *r",
            "let x: usize = 1; let r = &x; let y = move(x); *r",
            "let a: [usize; 1] = [1]; let r = &a[0]; drop(a); *r",
            "let x: usize = 1; let r = &x; drop(x); x = 2; *r",
            "let x: usize = 1; let y = move(x); x",
        ] {
            assert!(
                verify(&format!("fn main() -> usize {{ {body} }}")).is_err(),
                "{body}"
            );
        }
        let s = "fn main() -> usize { let x: usize = 1; let y = move(x); x = 2; x + y }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "3");
        let fixed = "fn main() -> usize ensures (result == 3) { let a: [usize; 2] = [1, 2]; let r = &a[0]; a = [3, 4]; *r }";
        assert_eq!(verify(fixed).unwrap().run().unwrap().to_string(), "3");
    }

    #[test]
    fn reference_updates_recheck_invariants_and_cannot_escape() {
        let prefix = "type Small struct {n: usize} where (n < 4); ";
        assert!(verify(&format!(
            "{prefix} fn main() -> usize {{let x = Small {{n: 1}}; let r = &x.n; *r = 9; x.n }}"
        ))
        .is_err());
        assert!(verify("fn escape() -> &usize {let x: usize = 1; &x}").is_err());
        assert!(verify("fn write(r: &usize) -> () { *r = 1; () }").is_err());
        assert!(verify("fn f(n: usize) -> usize ensures (result == move(n)) { n }").is_err());
    }

    #[test]
    fn verifies_well_founded_recursion() {
        let s = "fn countdown(n: usize) -> usize ensures (result == n) decreases (n) { if n == 0 { 0 } else { countdown(n - 1) + 1 } } fn main() -> usize ensures (result == 12) { countdown(12) }";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "12");
        for body in [
            "loop(n)",
            "loop(n + 1)",
            "if n == 0 { loop(n) } else { loop(n - 1) }",
        ] {
            assert!(
                verify(&format!(
                    "fn loop(n: usize) -> usize decreases (n) {{ {body} }}"
                ))
                .is_err(),
                "{body}"
            );
        }
        assert!(
            verify("fn bad(n: usize) -> usize ensures (bad(n) == 0) decreases (n) {0}").is_err()
        );
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

    #[test]
    fn explicit_updates_restore_invariants_and_ordinary_writes_preserve_them() {
        let s = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn read(p: &Pair) -> usize {*p.left} fn main() -> usize {let p = Pair {left: 1, right: 1}; update(p) lifts balanced {p.left = 2; p.right = p.left;} p.right}";
        // Field projection binds tighter than dereference.
        let s = s.replace("*p.left", "(*p).left");
        assert_eq!(verify(&s).unwrap().run().unwrap().to_string(), "2");
        let s = "type Storage struct {len: usize, data: [usize; len]} fn main() -> usize {let s = Storage {len: 1, data: [10]}; s = Storage {len: 2, data: [10, 20]}; s.data[1]}";
        assert_eq!(verify(s).unwrap().run().unwrap().to_string(), "20");
    }

    #[test]
    fn incomplete_states_cannot_be_observed_as_the_refined_type() {
        let prefix = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn read(p: &Pair) -> usize {(*p).left} ";
        for body in [
            "let p = Pair {left: 1, right: 1}; let r = &p; p.left = 2; read(r)",
            "let p = Pair {left: 1, right: 1}; p.left = 2; let r = &p; p.right = 2; 0",
            "let p = Pair {left: 1, right: 1}; p.left = 2; drop(p); 0",
        ] {
            assert!(
                verify(&format!("{prefix} fn main() -> usize {{ {body} }}")).is_err(),
                "{body}"
            );
        }
        let body = "let p = Pair {left: 1, right: 1}; let r = &p; update(p) lifts balanced {p.left = 2; p.right = 2;} read(r)";
        assert_eq!(
            verify(&format!("{prefix} fn main() -> usize {{ {body} }}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "2"
        );
    }

    #[test]
    fn library_rc_protocol_is_verified_without_compiler_special_cases() {
        let source = include_str!("../proofs/rc_protocol.evg");
        assert!(verify(source).unwrap().obligations >= 50);
        assert!(verify(&source.replace("RcProtocol", "OrdinaryUserState")).is_ok());
        assert!(verify(include_str!("../proofs/reject_rc_unbalanced.evg")).is_err());
        let double_publish = format!("{source}\nideal fn duplicate_credit(s: RcProtocol) -> RcProtocol where (s.credits == 1) {{publish(publish(s))}}");
        assert!(verify(&double_publish)
            .unwrap_err()
            .contains("precondition of publish"));
    }

    #[test]
    fn updates_enforce_visibility_cleanup_and_restoration_boundaries() {
        let prefix = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn observe(p: &Pair) -> usize {(*p).left} ";
        for update in [
            "update(p) lifts balanced {p.left = 2;}",
            "update(p) lifts balanced {p.left = observe(r); p.right = 2;}",
            "update(p) lifts balanced {p.left = *r; p.right = 2;}",
            "update(p) lifts balanced {p.left = drop(p); p.right = 2;}",
            "update(p) lifts balanced {p.left = move(p); p.right = 2;}",
            "update(p) lifts balanced {p.left = &p; p.right = 2;}",
            "update(p) lifts balanced {q.left = 2; q.right = 2;}",
            "update(p, p) lifts balanced {p.left = 2; p.right = 2;}",
            "update(p) lifts balanced {p = Pair {left: 2, right: 2};}",
            "update(p) lifts balanced {p.left = usize::MAX + 1; p.right = 2;}",
        ] {
            let source = format!("{prefix} fn main() -> usize {{let p = Pair {{left: 1, right: 1}}; let q = Pair {{left: 1, right: 1}}; let r = &p; {update} p.left}}");
            assert!(verify(&source).is_err(), "accepted {update}");
        }
    }

    #[test]
    fn updates_preserve_untouched_owned_fields() {
        let source = "type Resource struct {tag: usize} where (tag == 7); type Pair struct {left: usize, right: usize, resource: Resource} where (fact balanced = left == right; balanced); fn main() -> usize {let p = Pair {left: 1, right: 1, resource: Resource {tag: 7}}; update(p) lifts balanced {p.left = 2; p.right = 2;} p.resource.tag}";
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "7");
        let replace = source.replace(
            "p.left = 2; p.right = 2;",
            "p.resource = Resource {tag: 7};",
        );
        assert!(verify(&replace).is_err());
        assert!(verify("type NonZero struct {value: usize} where (value != 0); fn main() -> usize {let x = NonZero {value: 1}; x.value = 0; 0}").is_err());
    }

    #[test]
    fn borrowed_invariants_are_checked_through_record_fields() {
        let source = "type Positive struct {n: usize} where (n > 0); type Holder struct {p: &Positive} fn read(h: Holder) -> usize ensures (result > 0) {(*h.p).n} fn main() -> usize {let p = Positive {n: 1}; let h = Holder {p: &p}; p.n = 0; let result = read(h); p.n = 1; result}";
        assert!(verify(source).is_err());
    }

    #[test]
    fn dropped_or_moved_owners_have_shape_type() {
        let prefix = "type Resource struct {tag: usize} where (tag == 7); impl Drop for Resource {fn drop(self){}} ";
        for body in [
            "let a = Resource {tag: 7}; let b = a; a.tag",
            "let a = Resource {tag: 7}; drop(a); a.tag",
            "let a = Resource {tag: 7}; drop(a); drop(a); 0",
            "let a = Resource {tag: 7}; let r = &a; let b = a; (*r).tag",
        ] {
            assert!(
                verify(&format!("{prefix} fn main() -> usize {{ {body} }}")).is_err(),
                "{body}"
            );
        }
    }

    #[test]
    fn destructors_are_proved_and_effects_require_explicit_support() {
        for body in [
            "proof impossible: self.tag == 8;",
            "drop(self);",
            "let duplicate = self;",
            "let new = Resource {tag: 7};",
        ] {
            let source = format!("type Resource struct {{tag: usize}} where (tag == 7); impl Drop for Resource {{fn drop(self) {{ {body} }} }} fn main() -> usize {{0}}");
            assert!(verify(&source).is_err(), "{body}");
        }
    }

    #[test]
    fn cleanup_cannot_observe_a_borrow_of_an_already_dropped_plane() {
        let source = "type Borrower struct {p: &usize} impl Drop for Borrower {fn drop(self){}} fn main() -> usize {let first: usize = 1; let h = Borrower {p: &first}; let later: usize = 2; h.p = &later; 0}";
        assert!(verify(source).is_err());
        let source = "type Borrower struct {p: &usize} impl Drop for Borrower {fn drop(self){}} fn main() -> usize {let first: usize = 1; let h = Borrower {p: &first}; 0}";
        assert!(verify(source).is_ok());
    }

    #[test]
    fn independent_calls_and_scalar_borrows_are_allowed_inside_updates() {
        let source = include_str!("../examples/update_helpers.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let missing_restore = source.replace("pair.right = read(view);", "pair.right = 0;");
        assert!(verify(&missing_restore).is_err());
        let escape = source.replace("    pair.right\n}", "    read(view)\n}");
        assert!(verify(&escape).is_err());
        let prefix = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn equal(a: usize, b: usize) -> usize where (a == b) ensures (result == a) {a} ";
        let source = format!("{prefix} fn main() -> usize {{let p = Pair {{left: 1, right: 1}}; update(p) lifts balanced {{p.left = 2; p.right = equal(p.left, p.right);}} p.right}}");
        assert!(verify(&source).is_err());
    }

    #[test]
    fn calls_with_unproven_effects_cannot_observe_open_invariants() {
        let source = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn observe(p: &Pair) -> usize {(*p).left} fn main() -> usize {let p = Pair {left: 1, right: 1}; update(p) lifts balanced {p.left = 2; p.right = observe(&p);} p.right}";
        assert!(verify(source).is_err());
        let source = "type Resource struct {} impl Drop for Resource {fn drop(self){}} type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn cleanup(value: usize) -> usize {let r = Resource {}; value} fn main() -> usize {let p = Pair {left: 1, right: 1}; update(p) lifts balanced {p.left = cleanup(p.left); p.right = p.left;} p.right}";
        assert!(verify(source).is_err());
    }

    #[test]
    fn fact_definitions_are_not_proofs_or_assumptions() {
        let source = include_str!("../examples/named_facts.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert!(verify(include_str!("../examples/reject_false_proof.evg")).is_err());
        assert!(
            verify("fn main() -> usize {fact false_claim = 1 == 2; proof exploit: 2 == 3; 0}")
                .is_err()
        );
        assert!(verify("fn main() -> usize {fact true_claim = 1 == 1; proof p: true_claim by {exact true_claim}; 0}").is_err());
        assert!(verify("fn main() -> usize {fact p = 1 == 1; if p {1} else {0}}").is_err());
    }

    #[test]
    fn exact_uses_the_named_proof_of_the_current_proposition() {
        let source = "fn identity(n: usize) -> usize ensures (result == n) {proof positive: n >= 0; n} proof {exact positive}";
        assert!(verify(source).is_err()); // True goal, but this is the wrong witness.
        let source = "fn main() -> usize {let x: usize = 1; fact p = x == 1; proof old: p; x = 2; proof stale: p by {exact old}; x}";
        assert!(verify(source).is_err());
        let source = "fn main() -> usize {let x: usize = 1; fact p = x == 1; proof old: p; x = 2; proof stale: p; x}";
        assert!(verify(source).is_err());
    }

    #[test]
    fn caller_facts_cannot_redefine_struct_invariants() {
        let source = "type Checked struct {valid: bool} where (valid); fn main() -> usize {fact valid = true; let c = Checked {valid: false}; 0}";
        assert!(verify(source).is_err());
        let source = "type Checked struct {valid: bool} where (valid); fn main() -> usize {fact valid = false; let c = Checked {valid: true}; 0}";
        assert!(verify(source).is_ok());
    }

    #[test]
    fn mathematical_values_and_ideal_records_cannot_leak_into_runtime_storage() {
        for source in [
            "fn main() -> nat {0}",
            "fn main() -> usize {let n: nat = 0; 0}",
            "type Bad struct {n: int} fn main() -> usize {0}",
            "ideal type Model struct {n: nat} fn main() -> usize {let m = Model {n: 0}; 0}",
            "ideal fn answer() -> usize {42} fn main() -> usize {answer()}",
            "fn main() -> usize {let n = nat(42); 0}",
        ] {
            assert!(verify(source).is_err(), "{source}");
        }
        let source = "ideal fn main() -> nat {1 + 2}";
        assert!(verify(source).is_ok());
        assert!(verify(source).unwrap().run().is_err());
    }

    #[test]
    fn proof_views_and_ideal_contracts_are_erased_before_execution() {
        let source = "ideal fn positive(n: nat) -> bool where (n > 0) ensures (result) {true} fn main() -> usize where (positive(nat(1))) {let value: usize = 42; proof p: nat(value) >= 0; value}";
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let source = "fn main() -> usize {let value = 42; proof bounded: value <= isize::MAX; 0}";
        assert!(verify(source).is_ok());
    }

    #[test]
    fn lifted_requirements_are_named_and_selective() {
        let source = include_str!("../examples/selective_update.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let bounded_violation = source.replace(
            "pair.left = 42;",
            "pair.left = 101; pair.right = 101; pair.left = 42;",
        );
        assert!(verify(&bounded_violation).is_err());
        assert!(
            verify(&bounded_violation.replace("lifts balanced", "lifts balanced, bounded")).is_ok()
        );
        assert!(verify(&source.replace("lifts balanced", "lifts bounded")).is_err());
        assert!(verify(&source.replace("lifts balanced", "lifts unknown")).is_err());
        assert!(verify(&source.replace("lifts balanced", "lifts unused_false_claim")).is_err());
        assert!(verify(&source.replace("lifts balanced", "lifts Pair::balanced")).is_ok());
        assert!(verify(&source.replace("lifts balanced", "lifts balanced, balanced")).is_err());
        assert!(verify(&source.replace("lifts balanced", "")).is_err());
    }

    #[test]
    fn named_type_facts_do_not_add_unproven_assumptions() {
        let source = "type State struct {n: usize} where (fact claim = n == 0; true); fn main() -> usize {let s = State {n: 1}; fact false_statement = s::claim; 0}";
        assert!(verify(source).is_ok());
        assert!(verify(&source.replace(
            "fact false_statement = s::claim;",
            "proof invalid: s::claim;"
        ))
        .is_err());
        let source = "type Checked struct {valid: bool} where (fact required = valid; required); fn main() -> usize {fact required = true; let s = Checked {valid: false}; 0}";
        assert!(verify(source).is_err());
    }

    #[test]
    fn rc_and_arc_share_a_lifting_free_ideal_count_protocol() {
        let protocol = include_str!("../proofs/rc_protocol.evg");
        assert!(!protocol.contains("lifts"));
        let model = format!(
            "{protocol}\n{}",
            include_str!("../proofs/arc_interleavings.evg")
        );
        assert!(verify(&model).is_ok());
        let stale = format!(
            "{protocol}\n{}",
            include_str!("../proofs/reject_arc_stale_check.evg")
        );
        assert!(verify(&stale)
            .unwrap_err()
            .contains("precondition of reserve"));
    }
}
