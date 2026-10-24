//! Internal elaboration and verification-condition generation.

use crate::shared::ownership::is_affine;
use crate::{
    compiler::certificate::{ProofBundle, Session},
    compiler::kernel::Linear,
    shared::planes::{Memory, PlaneId, Projection, Reference},
    syntax::{self, Expr, Function, Kind, MachineInt, Statement, Struct, Type},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

mod array_history;

#[cfg(test)]
pub(crate) mod array_model;
mod bodies;
mod cleanup;
mod external;
mod heap;
mod parameters;
mod paths;
mod proofs;
mod references;
mod returns;
mod updates;
mod validation;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Formula {
    True,
    False,
    Ge(Linear),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Not(Box<Self>),
    Implies(Box<Self>, Box<Self>),
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
            Self::Implies(a, b) => {
                out.push(6);
                a.encode(out);
                b.encode(out);
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
    Plane(Box<Ty>),
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
        cells: BTreeMap<Linear, Symbol>,
        identity: String,
    },
    Record(String, BTreeMap<String, Symbol>),
    Unit,
    Ref(Box<Ty>, Reference, Vec<Projection<Linear>>),
    Plane(Box<Ty>, Reference),
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
            Self::Plane(t, _) => Ty::Plane(t.clone()),
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

// Count expanded logical data before snapshots or recursive validation can
// multiply it. References count as handles; their target storage is metered
// separately. These are bootstrap availability limits, not logical assumptions.
const MAX_VALUE_NODES: usize = 32768;
const MAX_VALUE_WORK: usize = 262144;

fn symbol_weight(value: &Symbol) -> Result<usize> {
    enum Node<'a> {
        Value(&'a Symbol, usize),
        Formula(&'a Formula, usize),
    }
    let mut pending = vec![Node::Value(value, 0)];
    let mut weight = 0usize;
    while let Some(node) = pending.pop() {
        weight = weight.saturating_add(1);
        let depth = match &node {
            Node::Value(_, depth) | Node::Formula(_, depth) => *depth,
        };
        if depth >= 128 || weight > MAX_VALUE_NODES {
            return Err("symbolic value expansion limit reached (32768 nodes, depth 128)".into());
        }
        match node {
            Node::Value(Symbol::Number(_, n), _) => weight = weight.saturating_add(n.terms.len()),
            Node::Value(Symbol::Bool(p), depth) => pending.push(Node::Formula(p, depth + 1)),
            Node::Value(
                Symbol::Array {
                    items, cells, len, ..
                },
                depth,
            ) => {
                weight = weight.saturating_add(len.terms.len());
                pending.extend(items.iter().flatten().map(|v| Node::Value(v, depth + 1)));
                pending.extend(cells.values().map(|v| Node::Value(v, depth + 1)));
            }
            Node::Value(Symbol::Record(name, fields), depth) => {
                weight = weight.saturating_add(name.len() / 32);
                pending.extend(fields.values().map(|v| Node::Value(v, depth + 1)));
            }
            Node::Value(Symbol::Ref(_, _, path), _) => weight = weight.saturating_add(path.len()),
            Node::Formula(Formula::Ge(n), _) => weight = weight.saturating_add(n.terms.len()),
            Node::Formula(Formula::Not(p), depth) => pending.push(Node::Formula(p, depth + 1)),
            Node::Formula(
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b),
                depth,
            ) => {
                pending.push(Node::Formula(a, depth + 1));
                pending.push(Node::Formula(b, depth + 1));
            }
            _ => {}
        }
    }
    if weight > MAX_VALUE_NODES {
        return Err("symbolic value expansion limit reached (32768 nodes)".into());
    }
    Ok(weight)
}

fn values_weight<'a>(values: impl IntoIterator<Item = &'a Symbol>) -> Result<usize> {
    let mut cost = 0usize;
    for value in values {
        cost = cost.saturating_add(symbol_weight(value)?);
        if cost > MAX_VALUE_WORK {
            return Err("symbolic snapshot work limit reached".into());
        }
    }
    Ok(cost)
}

fn constant_index(index: &Linear) -> Option<usize> {
    index
        .terms
        .is_empty()
        .then(|| usize::try_from(index.constant).ok())
        .flatten()
}

fn store_weight(memory: &Memory<Symbol>) -> Result<usize> {
    let states = memory.states();
    // Consumed slots still cost work when the store is copied.
    Ok(states.len().saturating_add(values_weight(
        states.iter().filter_map(|(_, _, value)| *value),
    )?))
}

fn project<'a>(value: &'a Symbol, path: &[Projection<Linear>]) -> Result<&'a Symbol> {
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
                items: Some(items),
                cells,
                ..
            },
        ) => constant_index(i)
            .and_then(|i| items.get(i))
            .or_else(|| cells.get(i))
            .ok_or("unknown array reference cell")?,
        (Projection::Index(i), Symbol::Array { cells, .. }) => cells
            .get(i)
            .ok_or("array reference cell has not been materialized")?,
        _ => {
            return Err(
                "reference projection requires a known struct field or array element".into(),
            )
        }
    };
    project(value, &path[1..])
}

fn project_mut<'a>(value: &'a mut Symbol, path: &[Projection<Linear>]) -> Result<&'a mut Symbol> {
    if path.is_empty() {
        return Ok(value);
    }
    let child = match (&path[0], value) {
        (Projection::Field(n), Symbol::Record(_, fields)) => {
            fields.get_mut(n).ok_or("unknown reference field")?
        }
        (
            Projection::Index(i),
            Symbol::Array {
                items: Some(items),
                cells,
                ..
            },
        ) => {
            if let Some(index) = constant_index(i) {
                items
                    .get_mut(index)
                    .ok_or("reference index out of bounds")?
            } else {
                cells.get_mut(i).ok_or("unknown array reference cell")?
            }
        }
        (Projection::Index(i), Symbol::Array { cells, .. }) => {
            cells.get_mut(i).ok_or("unknown array reference cell")?
        }
        _ => return Err("invalid reference projection".into()),
    };
    project_mut(child, &path[1..])
}

fn type_has_reference(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Ref(_) | Type::Plane(_) => true,
        Type::Array(t, _) => type_has_reference(t, structs),
        Type::Named(n) => structs
            .get(n)
            .is_some_and(|s| s.fields.iter().any(|(_, t)| type_has_reference(t, structs))),
        _ => false,
    }
}

/// Each path is a conjunction of inequalities. The path list is a disjunction.
fn extend(
    paths: &[Vec<Linear>],
    formula: &Formula,
    negated: bool,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Vec<Linear>>> {
    extend_normalized(paths, &formula.normalized(), negated, session, work)
}

fn extend_normalized(
    paths: &[Vec<Linear>],
    formula: &Formula,
    negated: bool,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Vec<Linear>>> {
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
        Formula::Not(p) => return extend_normalized(paths, p, !negated, session, work),
        Formula::Implies(a, b) => {
            if negated {
                extend_normalized(
                    &extend_normalized(paths, a, false, session, work)?,
                    b,
                    true,
                    session,
                    work,
                )?
            } else {
                let mut left = extend_normalized(paths, a, true, session, work)?;
                left.extend(extend_normalized(paths, b, false, session, work)?);
                left
            }
        }
        Formula::And(a, b) | Formula::Or(a, b) => {
            let conjunction = matches!(formula, Formula::And(..)) != negated;
            if conjunction {
                extend_normalized(
                    &extend_normalized(paths, a, negated, session, work)?,
                    b,
                    negated,
                    session,
                    work,
                )?
            } else {
                let mut left = extend_normalized(paths, a, negated, session, work)?;
                left.extend(extend_normalized(paths, b, negated, session, work)?);
                left
            }
        }
    };
    paths::bounded(result, session, work)
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

fn runtime_type(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Int | Type::Nat => false,
        Type::Named(n) => structs
            .get(n)
            .is_some_and(|s| !s.ideal && s.runtime_fields().all(|(_, t)| runtime_type(t, structs))),
        Type::Array(t, _) | Type::Ref(t) | Type::Plane(t) => runtime_type(t, structs),
        _ => true,
    }
}

// Erased ownership belongs to proof data. Borrowed views can cross this phase
// boundary; their provenance and liveness use the ordinary reference rules.
fn erased_type(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Plane(_) => false,
        Type::Ref(_) => true,
        Type::Named(name) => structs
            .get(name)
            .is_some_and(|s| s.ideal && s.fields.iter().all(|(_, t)| erased_type(t, structs))),
        Type::Array(element, _) => erased_type(element, structs),
        _ => true,
    }
}

// Address calculations are pure scalar observations of entry storage. The
// ordinary evaluator still checks their types, arithmetic, and array bounds.
fn place_index_expression(e: &Expr) -> bool {
    match &e.kind {
        Kind::Name(_) | Kind::Number(_) | Kind::Constant(..) | Kind::Bool(_) => true,
        Kind::Field(base, _) => place_index_expression(base),
        Kind::Index(base, index) => place_index_expression(base) && place_index_expression(index),
        Kind::Unary(op, value) if matches!(op.as_str(), "-" | "*" | "!") => {
            place_index_expression(value)
        }
        Kind::Binary(op, a, b)
            if matches!(
                op.as_str(),
                "+" | "-" | "*" | "==" | "!=" | "<" | "<=" | ">" | ">=" | "&&" | "||" | "=>"
            ) =>
        {
            place_index_expression(a) && place_index_expression(b)
        }
        Kind::If(condition, yes, no) => {
            place_index_expression(condition)
                && place_index_expression(yes)
                && place_index_expression(no)
        }
        Kind::Call(name, args) if matches!(name.as_str(), "int" | "nat") && args.len() == 1 => {
            place_index_expression(&args[0])
        }
        _ => false,
    }
}

// Exact alias contracts may name an incoming reference or project a fixed
// place through it using a checked scalar index. They cannot allocate, call
// user functions, or introduce evidence.
fn borrow_expression(e: &Expr) -> bool {
    match &e.kind {
        Kind::Name(_) => true,
        Kind::Field(e, _) => borrow_expression(e),
        Kind::Unary(op, e) if op == "&" || op == "*" => borrow_expression(e),
        Kind::Index(e, index) => borrow_expression(e) && place_index_expression(index),
        _ => false,
    }
}

fn destructor_expression(e: &Expr) -> bool {
    match &e.kind {
        Kind::Record(..) => false,
        Kind::Call(_, args) => args.iter().all(destructor_expression),
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
        Statement::Ideal(binding) => destructor_body(std::slice::from_ref(binding.as_ref())),
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

/// Specifications inspect values without consuming ownership. Ideal code is
/// erased computation, but its affine values still move. Runtime code cannot
/// inspect erased bindings. Keep these modes distinct at every phase boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Runtime,
    Ideal,
    Specification,
}

#[derive(Clone)]
struct WritePlace {
    origin: String,
    reference: Reference,
    path: Vec<Projection<Linear>>,
    ty: Box<Ty>,
}

#[derive(Clone)]
struct InputReference {
    origin: String,
    reference: Reference,
    path: Vec<Projection<Linear>>,
    pointee: Box<Ty>,
}

// Identify an incoming reference value by its structural argument path, never
// by pointer equality. Distinct fields may happen to contain the same handle.
fn input_value_path(expression: &Expr) -> Option<String> {
    match &expression.kind {
        Kind::Name(name) => Some(name.clone()),
        Kind::Field(base, field) => Some(format!("{}.{field}", input_value_path(base)?)),
        Kind::Unary(op, base) if op == "*" => {
            if let Kind::Unary(op, place) = &base.kind {
                if op == "&" {
                    return input_value_path(place);
                }
            }
            Some(format!("(*{})", input_value_path(base)?))
        }
        Kind::Index(base, index) => {
            let number = match index.kind {
                Kind::Number(n) | Kind::Constant(_, n) => n,
                _ => return None,
            };
            Some(format!("{}[{number}]", input_value_path(base)?))
        }
        _ => None,
    }
}

fn input_reference_origin(expression: &Expr) -> Option<String> {
    fn indirect(place: &Expr) -> Option<String> {
        match &place.kind {
            Kind::Unary(op, reference) if op == "*" => input_reference_origin(reference),
            Kind::Field(base, _) | Kind::Index(base, _) => indirect(base),
            _ => None,
        }
    }
    if let Kind::Unary(op, place) = &expression.kind {
        if op == "&" {
            return indirect(place);
        }
    }
    input_value_path(expression)
}

fn effect_origin(expression: &Expr) -> Option<&str> {
    match &expression.kind {
        Kind::Name(name) => Some(name),
        Kind::Unary(_, base) | Kind::Field(base, _) | Kind::Index(base, _) => effect_origin(base),
        _ => None,
    }
}

// Only functions that use a compound old(...) expression need an entry store.
// Simple parameter snapshots retain their existing inexpensive representation.
fn needs_old_memory(function: &Function) -> bool {
    fn expression(e: &Expr) -> bool {
        if matches!(&e.kind, Kind::Call(name, args) if name == "old" && args.len() == 1 && Context::old_key(&args[0]).is_none())
        {
            return true;
        }
        match &e.kind {
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => expression(e),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => expression(a) || expression(b),
            Kind::If(c, a, b) => expression(c) || expression(a) || expression(b),
            Kind::Array(items) | Kind::Call(_, items) => items.iter().any(expression),
            Kind::Record(_, fields) => fields.iter().any(|(_, e)| expression(e)),
            _ => false,
        }
    }

    fn ty(t: &Type) -> bool {
        match t {
            Type::Ref(t) | Type::Plane(t) => ty(t),
            Type::Array(t, n) => ty(t) || expression(n),
            _ => false,
        }
    }

    fn statement(s: &Statement) -> bool {
        match s {
            Statement::Ideal(s) => statement(s),
            Statement::Let { ty: t, value, .. } => t.as_ref().is_some_and(ty) || expression(value),
            Statement::Destructure { value, .. }
            | Statement::Fact { value, .. }
            | Statement::Effect(value) => expression(value),
            Statement::Proof { proposition, .. } => expression(proposition),
            Statement::Assign { target, value } => expression(target) || expression(value),
            Statement::Update { body, .. } => body.iter().any(statement),
        }
    }
    function.params.iter().any(|(_, t)| ty(t))
        || ty(&function.ret)
        || function.pre.as_ref().is_some_and(expression)
        || function.post.as_ref().is_some_and(expression)
        || function.decreases.as_ref().is_some_and(expression)
        || function
            .borrows
            .iter()
            .any(|alias| expression(&alias.reference))
        || function.modifies.iter().any(expression)
        || function.body.iter().any(statement)
        || expression(&function.result)
}

struct EntryMemory {
    env: BTreeMap<String, Symbol>,
    roots: BTreeMap<String, PlaneId>,
    memory: Memory<Symbol>,
    module: Option<String>,
}

#[derive(Clone)]
enum ArrayHistory {
    Store {
        base: String,
        index: Linear,
        value: Symbol,
    },
    Choice {
        condition: Formula,
        left: String,
        right: String,
    },
}

struct Context<'a> {
    functions: &'a BTreeMap<String, Function>,
    module: Option<String>,
    declaring: Option<String>,
    ideal_execution: bool,
    partial_execution: bool,
    structs: &'a BTreeMap<String, Struct>,
    env: BTreeMap<String, Symbol>,
    facts: BTreeMap<String, Expr>,
    proofs: BTreeMap<String, Formula>,
    paths: Vec<Vec<Linear>>,
    fresh: usize,
    eval_depth: usize,
    eval_steps: usize,
    value_work: usize,
    obligations: usize,
    memory: Memory<Symbol>,
    roots: BTreeMap<String, PlaneId>,
    phase: Phase,
    current: Option<String>,
    measure: Option<Linear>,
    opened_planes: BTreeMap<PlaneId, BTreeSet<String>>,
    drops: &'a BTreeSet<String>,
    destructors: &'a BTreeMap<String, Function>,
    cleanup_depth: usize,
    dropping: bool,
    helpers: &'a BTreeSet<String>,
    cleanup_helpers: &'a BTreeSet<String>,
    session: &'a mut Session,
    writable: Vec<WritePlace>,
    input_references: Vec<InputReference>,
    old_values: BTreeMap<String, Symbol>,
    old_memory: Option<Box<EntryMemory>>,
    ideal_bindings: BTreeSet<String>,
    array_reads: BTreeMap<(String, Linear), Symbol>,
    array_history: BTreeMap<String, ArrayHistory>,
    array_read_depth: usize,
    temporaries: Vec<(Symbol, usize)>,
}

impl<'a> Context<'a> {
    fn write_permitted(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        owned: bool,
    ) -> Result<bool> {
        let grants = std::mem::take(&mut self.writable);
        let result = self.write_permitted_by(&grants, reference, path, owned);
        self.writable = grants;
        result
    }

    fn write_permitted_by(
        &mut self,
        grants: &[WritePlace],
        reference: Reference,
        path: &[Projection<Linear>],
        owned: bool,
    ) -> Result<bool> {
        if owned {
            return Ok(true);
        }
        let plane = self.memory.plane(reference)?;
        let grants = grants
            .iter()
            .filter(|grant| {
                self.memory.plane(grant.reference).ok() == Some(plane)
                    && grant.path.len() <= path.len()
            })
            .map(|grant| grant.path.clone())
            .collect::<Vec<_>>();
        for grant in grants {
            if self.paths_equal(&grant, &path[..grant.len()])? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn incoming_references(
        &mut self,
        function: &Function,
        strict: bool,
    ) -> Result<Vec<InputReference>> {
        fn visit(
            ctx: &Context<'_>,
            value: &Symbol,
            origin: String,
            mode: (bool, bool),
            inputs: &mut Vec<InputReference>,
            work: &mut usize,
            limit: usize,
        ) -> Result<()> {
            let (strict, borrowed) = mode;
            *work = work.saturating_add(1 + origin.len() / 32);
            if *work > limit {
                return Err(
                    "symbolic value work limit reached while checking incoming references".into(),
                );
            }
            match value {
                Symbol::Ref(pointee, reference, path) => {
                    if inputs.len() >= 8192 {
                        return Err("incoming reference graph limit reached (8192)".into());
                    }
                    for step in path {
                        *work = work.saturating_add(
                            1 + match step {
                                Projection::Field(name) => name.len() / 32,
                                Projection::Index(index) => index.terms.len(),
                            },
                        );
                    }
                    if *work > limit {
                        return Err(
                            "symbolic value work limit reached while checking incoming references"
                                .into(),
                        );
                    }
                    inputs.push(InputReference {
                        origin: origin.clone(),
                        reference: *reference,
                        path: path.clone(),
                        pointee: pointee.clone(),
                    });
                    let target = project(ctx.memory.read(*reference)?, path)?;
                    visit(
                        ctx,
                        target,
                        format!("(*{origin})"),
                        (strict, true),
                        inputs,
                        work,
                        limit,
                    )?;
                }
                Symbol::Plane(pointee, reference) => {
                    if borrowed {
                        if inputs.len() >= 8192 {
                            return Err("incoming reference graph limit reached (8192)".into());
                        }
                        inputs.push(InputReference {
                            origin: origin.clone(),
                            reference: *reference,
                            path: Vec::new(),
                            pointee: pointee.clone(),
                        });
                    }
                    visit(
                        ctx,
                        ctx.memory.read(*reference)?,
                        format!("(*{origin})"),
                        mode,
                        inputs,
                        work,
                        limit,
                    )?;
                }
                Symbol::Record(_, fields) => {
                    for (name, value) in fields {
                        visit(
                            ctx,
                            value,
                            format!("{origin}.{name}"),
                            mode,
                            inputs,
                            work,
                            limit,
                        )?;
                    }
                }
                Symbol::Array {
                    element,
                    len,
                    items,
                    ..
                } if ctx.ty_has_reference(element) => {
                    if let Some(items) = items {
                        for (index, value) in items.iter().enumerate() {
                            visit(
                                ctx,
                                value,
                                format!("{origin}[{index}]"),
                                mode,
                                inputs,
                                work,
                                limit,
                            )?;
                        }
                    } else if strict && *len != Linear::number(0) {
                        return Err(
                            "write contracts cannot summarize opaque arrays containing references"
                                .into(),
                        );
                    }
                }
                _ => {}
            }
            Ok(())
        }
        let mut inputs = Vec::new();
        let mut work = 0usize;
        let remaining = MAX_VALUE_WORK.saturating_sub(self.value_work);
        for (name, _) in &function.params {
            let value = self.env.get(name).ok_or("missing input parameter")?;
            if self.ty_has_reference(&value.ty()) {
                visit(
                    self,
                    value,
                    name.clone(),
                    (strict, false),
                    &mut inputs,
                    &mut work,
                    remaining,
                )?;
            }
        }
        self.charge_value_work(work)?;
        Ok(inputs)
    }

    fn incoming_place(
        &mut self,
        expression: &Expr,
        inputs: &[InputReference],
        expected: Option<&Ty>,
    ) -> Result<WritePlace> {
        let origin = input_reference_origin(expression)
            .ok_or("effect or borrow must project an incoming reference")?;
        let input = inputs.iter().find(|input| input.origin == origin).ok_or(
            "effect or borrow must refer to incoming caller storage, not a local parameter slot",
        )?;
        let Symbol::Ref(ty, reference, path) = self.eval(expression, expected)? else {
            return Err("effect and borrow entries must denote references".into());
        };
        if self.memory.plane(input.reference)? != self.memory.plane(reference)?
            || input.path.len() > path.len()
            || !self.paths_equal(&input.path, &path[..input.path.len()])?
        {
            return Err(
                "effect or borrow cannot acquire a different input reference's plane".into(),
            );
        }
        Ok(WritePlace {
            origin,
            reference,
            path,
            ty,
        })
    }

    fn write_places(
        &mut self,
        function: &Function,
        inputs: &[InputReference],
    ) -> Result<Vec<WritePlace>> {
        let phase = std::mem::replace(&mut self.phase, Phase::Specification);
        let mut places: Vec<WritePlace> = Vec::new();
        for expression in &function.modifies {
            let place = self.incoming_place(expression, inputs, None)?;
            // Erasure belongs to the storage slot, not to the reference value.
            // A pointer stored inside ideal data may still target runtime data.
            let input = inputs
                .iter()
                .find(|input| input.origin == place.origin)
                .ok_or("missing incoming reference for write footprint")?;
            let mut erased = self.proof_storage(&input.pointee);
            let mut target = project(self.memory.read(input.reference)?, &input.path)?;
            for step in &place.path[input.path.len()..] {
                if let (Symbol::Record(name, _), Projection::Field(field)) = (target, step) {
                    erased |= self.structs[name].ideal_fields.contains(field);
                }
                target = project(target, std::slice::from_ref(step))?;
            }
            if function.ideal && !erased {
                return Err("ideal modifies must target proof storage; erased references do not grant writes to runtime pointees".into());
            }
            let supported_region = match &*place.ty {
                Ty::Machine(_) | Ty::Bool => true,
                Ty::Nat | Ty::Int => erased,
                Ty::Record(_) => {
                    self.history_element(&place.ty)
                        || erased && self.erased_ty(&place.ty) && self.scalar_field_value(&place.ty)
                }
                Ty::Array(element, _) => {
                    matches!(**element, Ty::Machine(_) | Ty::Bool)
                        || matches!(**element, Ty::Record(_)) && self.history_element(element)
                }
                _ => false,
            };
            if !supported_region {
                return Err("modifies targets require machine scalars, Booleans, proof-only int/nat slots, copyable scalar-field records, or supported arrays".into());
            }
            // Permissions form a union for one structural input origin. Pointer
            // equality cannot merge independently modeled reference fields.
            let mut redundant = false;
            for previous in &places {
                self.charge_value_work(1)?;
                if previous.origin == place.origin
                    && previous.reference == place.reference
                    && self.paths_equal(&previous.path, &place.path)?
                {
                    redundant = true;
                    break;
                }
            }
            if !redundant {
                places.push(place);
            }
        }
        self.phase = phase;
        Ok(places)
    }

    fn charge_value_work(&mut self, cost: usize) -> Result<()> {
        self.value_work = self.value_work.saturating_add(cost);
        if self.value_work > MAX_VALUE_WORK {
            return Err("symbolic value work limit reached (262144 nodes)".into());
        }
        Ok(())
    }

    fn clone_env(&mut self) -> Result<BTreeMap<String, Symbol>> {
        self.charge_value_work(values_weight(self.env.values())?)?;
        Ok(self.env.clone())
    }

    fn snapshot_memory(&mut self) -> Result<Memory<Symbol>> {
        self.charge_value_work(store_weight(&self.memory)?)?;
        Ok(self.memory.snapshot())
    }

    fn clone_store(&mut self, store: &Memory<Symbol>) -> Result<Memory<Symbol>> {
        self.charge_value_work(store_weight(store)?)?;
        Ok(store.snapshot())
    }

    fn erased_value(&self, value: &Symbol) -> bool {
        match value.ty() {
            Ty::Plane(_) => false,
            Ty::Record(name) => erased_type(&Type::Named(name), self.structs),
            Ty::Array(element, _) => self.erased_ty(&element),
            Ty::Ref(_) => true,
            _ => true,
        }
    }

    fn proof_storage(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Nat | Ty::Int => true,
            Ty::Record(name) => self.structs[name].ideal,
            Ty::Array(element, _) => self.proof_storage(element),
            // A reference is itself a runtime word, regardless of its target.
            _ => false,
        }
    }

    fn erased_ty(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Plane(_) => false,
            Ty::Record(name) => erased_type(&Type::Named(name.clone()), self.structs),
            Ty::Array(element, _) => self.erased_ty(element),
            Ty::Ref(_) => true,
            _ => true,
        }
    }

    fn representation_access(&self, name: &str, line: usize) -> Result<()> {
        if self.declaring.as_deref() == Some(name) {
            return Ok(());
        }
        let def = self
            .structs
            .get(name)
            .ok_or_else(|| format!("unknown struct {name}"))?;
        if def.opaque && def.module != self.module {
            return Err(format!(
                "line {line}: {name} has an opaque representation outside its defining module"
            ));
        }
        Ok(())
    }

    fn field_access(&self, name: &str, field: &str, line: usize) -> Result<()> {
        self.representation_access(name, line)?;
        if self.phase == Phase::Runtime && self.structs[name].ideal_fields.contains(field) {
            return Err(format!(
                "line {line}: {name}.{field} is ideal data and cannot be accessed at runtime"
            ));
        }
        Ok(())
    }

    fn follows(&mut self, proposition: &Formula) -> Result<bool> {
        for path in extend(
            &self.paths,
            proposition,
            true,
            self.session,
            &mut self.value_work,
        )? {
            if !self.session.probe(&path)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn paths_disjoint(
        &mut self,
        a: &[Projection<Linear>],
        b: &[Projection<Linear>],
    ) -> Result<bool> {
        for (a, b) in a.iter().zip(b) {
            match (a, b) {
                (Projection::Field(a), Projection::Field(b)) if a != b => return Ok(true),
                (Projection::Index(a), Projection::Index(b)) if a != b => {
                    return self.follows(&equal(a, b)?.not())
                }
                (a, b) if a == b => {}
                _ => return Ok(false),
            }
        }
        Ok(false)
    }

    fn paths_equal(&mut self, a: &[Projection<Linear>], b: &[Projection<Linear>]) -> Result<bool> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            match (a, b) {
                (a, b) if a == b => {}
                (Projection::Index(a), Projection::Index(b)) if self.follows(&equal(a, b)?)? => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn updated_cell(
        &mut self,
        target: &Linear,
        index: &Linear,
        previous: &Symbol,
        new: &Symbol,
    ) -> Result<Symbol> {
        if target == index {
            return Ok(new.clone());
        }
        if target.terms == index.terms {
            return Ok(previous.clone());
        }
        let aliases = equal(target, index)?;
        if self.follows(&aliases)? {
            return Ok(new.clone());
        }
        if self.follows(&aliases.clone().not())? {
            return Ok(previous.clone());
        }
        let result = self.history_value(&previous.ty())?;
        let relation = aliases
            .clone()
            .and(self.symbol_equal(&result, new)?)
            .or(aliases.not().and(self.symbol_equal(&result, previous)?));
        self.assume(&relation)?;
        Ok(result)
    }

    fn replace_projection(
        &mut self,
        value: &mut Symbol,
        path: &[Projection<Linear>],
        new: Symbol,
    ) -> Result<()> {
        self.charge_value_work(symbol_weight(value)?)?;
        if path.is_empty() {
            *value = new;
            return Ok(());
        }
        if let (
            Projection::Index(target),
            Symbol::Array {
                element,
                items,
                cells,
                identity,
                ..
            },
        ) = (&path[0], &mut *value)
        {
            if self.history_element(element) {
                // Updating a record field is a store of the complete updated
                // element. All other index views see that same structural value.
                let replacement = if path.len() == 1 {
                    new
                } else {
                    // The location was materialized before the store. Do not
                    // assume its nominal invariant while a call summary is
                    // still assembling multiple field updates.
                    let mut value = cells
                        .get(target)
                        .or_else(|| {
                            constant_index(target).and_then(|index| items.as_ref()?.get(index))
                        })
                        .cloned()
                        .ok_or("missing record array write view")?;
                    self.replace_projection(&mut value, &path[1..], new)?;
                    value
                };
                let mut observed = cells.clone();
                if let Some(values) = items.take() {
                    for (index, value) in values.into_iter().enumerate() {
                        observed.insert(Linear::number(index as i128), value);
                    }
                }
                for ((contents, index), value) in &self.array_reads {
                    if contents == identity {
                        observed
                            .entry(index.clone())
                            .or_insert_with(|| value.clone());
                    }
                }
                for (index, previous) in &observed {
                    self.array_reads
                        .entry((identity.clone(), index.clone()))
                        .or_insert_with(|| previous.clone());
                }
                let next = self.fresh_name();
                self.array_history.insert(
                    next.clone(),
                    ArrayHistory::Store {
                        base: identity.clone(),
                        index: target.clone(),
                        value: replacement.clone(),
                    },
                );
                let mut updated = BTreeMap::new();
                for (index, previous) in observed {
                    updated.insert(
                        index.clone(),
                        self.updated_cell(target, &index, &previous, &replacement)?,
                    );
                }
                updated.insert(target.clone(), replacement);
                *cells = updated;
                *identity = next;
                return Ok(());
            }
            *identity = self.fresh_name();
        }
        let child = match (&path[0], value) {
            (Projection::Field(name), Symbol::Record(_, fields)) => {
                fields.get_mut(name).ok_or("unknown reference field")?
            }
            (
                Projection::Index(index),
                Symbol::Array {
                    items: Some(items), ..
                },
            ) => constant_index(index)
                .and_then(|i| items.get_mut(i))
                .ok_or("unsupported aggregate index projection")?,
            (Projection::Index(index), Symbol::Array { cells, .. }) => {
                cells.get_mut(index).ok_or("unknown array reference cell")?
            }
            _ => return Err("invalid reference projection".into()),
        };
        self.replace_projection(child, &path[1..], new)
    }

    fn new(
        functions: &'a BTreeMap<String, Function>,
        structs: &'a BTreeMap<String, Struct>,
        drops: &'a BTreeSet<String>,
        destructors: &'a BTreeMap<String, Function>,
        helpers: &'a BTreeSet<String>,
        cleanup_helpers: &'a BTreeSet<String>,
        session: &'a mut Session,
    ) -> Self {
        Self {
            functions,
            module: None,
            declaring: None,
            ideal_execution: false,
            partial_execution: false,
            structs,
            env: BTreeMap::new(),
            facts: BTreeMap::new(),
            proofs: BTreeMap::new(),
            paths: vec![vec![]],
            fresh: 0,
            eval_depth: 0,
            eval_steps: 0,
            value_work: 0,
            obligations: 0,
            memory: Memory::default(),
            roots: BTreeMap::new(),
            phase: Phase::Runtime,
            current: None,
            measure: None,
            opened_planes: BTreeMap::new(),
            drops,
            destructors,
            cleanup_depth: 0,
            dropping: false,
            helpers,
            cleanup_helpers,
            session,
            writable: Vec::new(),
            input_references: Vec::new(),
            old_values: BTreeMap::new(),
            old_memory: None,
            ideal_bindings: BTreeSet::new(),
            array_reads: BTreeMap::new(),
            array_history: BTreeMap::new(),
            array_read_depth: 0,
            temporaries: Vec::new(),
        }
    }

    fn fresh_name(&mut self) -> String {
        self.fresh += 1;
        format!("evg_{}", self.fresh)
    }

    fn runtime_name(&self, name: &str) -> Result<()> {
        if self.ideal_bindings.contains(name) && self.phase == Phase::Runtime {
            return Err(format!(
                "{name} is an ideal parameter and cannot be read by runtime code"
            ));
        }
        Ok(())
    }

    fn capture_old(&mut self, function: &Function) -> Result<()> {
        self.charge_value_work(values_weight(self.env.values())?)?;
        let target_cost = self
            .env
            .values()
            .try_fold(0usize, |cost, value| -> Result<usize> {
                let extra = if let Symbol::Ref(_, reference, fields) = value {
                    symbol_weight(project(self.memory.read(*reference)?, fields)?)?
                } else if let Symbol::Plane(_, reference) = value {
                    symbol_weight(self.memory.read(*reference)?)?
                } else {
                    0
                };
                Ok(cost.saturating_add(extra))
            })?;
        self.charge_value_work(target_cost)?;
        self.old_values.clear();
        let mut targets = Vec::new();
        for (name, value) in &self.env {
            self.old_values.insert(name.clone(), value.clone());
            if let Symbol::Ref(_, reference, fields) = value {
                targets.push((name.clone(), *reference, fields.clone()));
            } else if let Symbol::Plane(_, reference) = value {
                targets.push((name.clone(), *reference, Vec::new()));
            }
        }
        for (name, reference, fields) in targets {
            let target = self.read_projection_value(reference, &fields)?;
            self.old_values.insert(format!("*{name}"), target);
        }
        self.old_memory = if function.entry_memory {
            Some(Box::new(EntryMemory {
                env: self.clone_env()?,
                roots: self.roots.clone(),
                memory: self.snapshot_memory()?,
                module: self.module.clone(),
            }))
        } else {
            None
        };
        Ok(())
    }

    fn entry_observation(&self, expression: &Expr) -> bool {
        if place_index_expression(expression) {
            return true;
        }
        match &expression.kind {
            Kind::Call(name, args) => {
                let scalar_call = matches!(name.as_str(), "int" | "nat")
                    || self.functions.get(name).is_some_and(|function| {
                        !function.partial
                            && function.modifies.is_empty()
                            && matches!(
                                function.ret,
                                Type::Int | Type::Nat | Type::Bool | Type::Machine(_) | Type::Unit
                            )
                    });
                scalar_call && args.iter().all(|arg| self.entry_observation(arg))
            }
            Kind::Field(base, _) => self.entry_observation(base),
            Kind::Index(base, index) | Kind::Binary(_, base, index) => {
                self.entry_observation(base) && self.entry_observation(index)
            }
            Kind::Unary(op, value) if matches!(op.as_str(), "-" | "*" | "!") => {
                self.entry_observation(value)
            }
            Kind::If(condition, yes, no) => {
                self.entry_observation(condition)
                    && self.entry_observation(yes)
                    && self.entry_observation(no)
            }
            _ => false,
        }
    }

    fn old_expression(&mut self, expression: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        if let Some(key) = Self::old_key(expression) {
            return self
                .old_values
                .get(&key)
                .cloned()
                .ok_or_else(|| format!("{key} is not a function entry parameter"));
        }
        if !self.entry_observation(expression) {
            return Err(
                "old snapshots require storage observations or total scalar calls without write effects".into(),
            );
        }
        let mut entry = self
            .old_memory
            .take()
            .ok_or("old expression has no function entry memory")?;
        std::mem::swap(&mut self.env, &mut entry.env);
        std::mem::swap(&mut self.roots, &mut entry.roots);
        std::mem::swap(&mut self.memory, &mut entry.memory);
        std::mem::swap(&mut self.module, &mut entry.module);
        let facts = std::mem::take(&mut self.facts);
        let proofs = std::mem::take(&mut self.proofs);
        let phase = std::mem::replace(&mut self.phase, Phase::Specification);
        let value = self.eval(expression, expected);
        self.phase = phase;
        self.facts = facts;
        self.proofs = proofs;
        std::mem::swap(&mut self.env, &mut entry.env);
        std::mem::swap(&mut self.roots, &mut entry.roots);
        std::mem::swap(&mut self.memory, &mut entry.memory);
        std::mem::swap(&mut self.module, &mut entry.module);
        self.old_memory = Some(entry);
        // Pure entry expressions cannot construct addresses. Conditional
        // selections may introduce a new symbolic cell path on an incoming
        // handle. Materialize its LIVE view separately from the frozen read.
        if let Ok(value) = &value {
            self.materialize_live_reference_views(value, expression.line)?;
        }
        value
    }

    fn old_key(e: &Expr) -> Option<String> {
        match &e.kind {
            Kind::Name(n) => Some(n.clone()),
            Kind::Unary(op, x) if op == "*" => match &x.kind {
                Kind::Name(n) => Some(format!("*{n}")),
                _ => None,
            },
            _ => None,
        }
    }

    fn number_type(&self) -> Ty {
        if self.phase != Phase::Runtime {
            Ty::Int
        } else {
            Ty::Machine(MachineInt::parse("isize").expect("isize type"))
        }
    }

    fn assume(&mut self, p: &Formula) -> Result<()> {
        let paths = extend(&self.paths, p, false, self.session, &mut self.value_work)?;
        self.paths = self.feasible_paths(paths)?;
        Ok(())
    }

    fn feasible_paths(&mut self, paths: Vec<Vec<Linear>>) -> Result<Vec<Vec<Linear>>> {
        if paths.len() <= 1 {
            return Ok(paths);
        }
        let mut feasible = Vec::new();
        for path in paths {
            if !self.session.probe(&path)? {
                feasible.push(path);
            }
        }
        Ok(feasible)
    }

    fn proposition(&mut self, e: &Expr) -> Result<Formula> {
        let saved = self.phase;
        self.phase = Phase::Specification;
        let result = self.eval(e, Some(&Ty::Bool)).and_then(|v| v.proposition());
        self.phase = saved;
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
        for path in extend(&self.paths, p, true, self.session, &mut self.value_work)? {
            self.session
                .prove(&path)
                .map_err(|e| format!("line {line}: cannot prove {label}: {e}"))?;
        }
        Ok(())
    }

    fn resolve(&mut self, t: &Type) -> Result<Ty> {
        match t {
            Type::Int | Type::Nat if self.phase == Phase::Runtime => Err("int and nat are proof-only; use a machine integer for runtime storage or declare ideal code".into()),
            Type::Int => Ok(Ty::Int), Type::Nat => Ok(Ty::Nat),
            Type::Bool => Ok(Ty::Bool),
            Type::Machine(t) => Ok(Ty::Machine(*t)),
            Type::Unit => Ok(Ty::Unit),
            Type::Ref(t) => Ok(Ty::Ref(Box::new(self.resolve(t)?))),
            Type::Plane(t) => {
                if !runtime_type(t, self.structs) || !heap::payload_type(t, self.structs) {
                    return Err("owned planes require runtime payloads without borrowed references".into());
                }
                crate::compiler::layout::of(t, self.structs)?;
                Ok(Ty::Plane(Box::new(self.resolve(t)?)))
            }
            Type::Named(n) => {
                if !self.structs.contains_key(n) {
                    return Err(format!(
                        "unknown struct {n}; recursive types are not supported yet"
                    ));
                }
                if self.structs.get(n).is_some_and(|s| s.ideal) && self.phase == Phase::Runtime {return Err(format!("{n} is ideal data and has no runtime layout"));}
                Ok(Ty::Record(n.clone()))
            }
            Type::Array(element, len) => {
                let element = self.resolve(element)?;
                let saved_spec = self.phase;
                self.phase = Phase::Specification;
                let n = self.nonnegative(len, "nonnegative array length")?;
                self.phase = saved_spec;
                Ok(Ty::Array(Box::new(element), n))
            }
        }
    }

    fn literal_element_hint(&mut self, t: &Type) -> Result<Option<Ty>> {
        match t {
            // Nested dependent lengths need the callee's parameter environment.
            Type::Array(..) => Ok(None),
            Type::Ref(inner) => Ok(self
                .literal_element_hint(inner)?
                .map(|t| Ty::Ref(Box::new(t)))),
            _ => self.resolve(t).map(Some),
        }
    }

    fn compatible(&mut self, got: &Ty, expected: &Ty, line: usize) -> Result<()> {
        match (got, expected) {
            (Ty::Int, Ty::Int)
            | (Ty::Nat, Ty::Nat)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Unit, Ty::Unit) => Ok(()),
            (Ty::Ref(a), Ty::Ref(b)) => self.compatible(a, b, line),
            (Ty::Plane(a), Ty::Plane(b)) => self.compatible(a, b, line),
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
        self.charge_value_work(1)?;
        if self.fresh >= 8192 {
            return Err("symbolic value expansion limit reached (8192)".into());
        }
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
            Ty::Plane(t) => {
                let value = self.arbitrary(t)?;
                let plane = self.memory.allocate(value)?;
                Ok(Symbol::Plane(t.clone(), self.memory.borrow(plane)?))
            }
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
            Ty::Array(element, len) => {
                // Reference ports must be stable across every observation of an
                // incoming fixed array. Model each port once, rather than
                // manufacturing a new pointee whenever an element is read.
                let items = if self.ty_has_reference(element) && len.terms.is_empty() {
                    let length = usize::try_from(len.constant)
                        .map_err(|_| "invalid reference array extent")?;
                    if length > 2048 {
                        return Err(
                            "incoming reference array expansion limit reached (2048)".into()
                        );
                    }
                    let mut items = Vec::with_capacity(length);
                    for _ in 0..length {
                        items.push(self.arbitrary(element)?);
                    }
                    Some(items)
                } else {
                    None
                };
                Ok(Symbol::Array {
                    element: element.clone(),
                    len: len.clone(),
                    items,
                    cells: BTreeMap::new(),
                    identity: name,
                })
            }
            Ty::Record(name) => {
                let def = self.structs.get(name).ok_or("unknown struct")?;
                let saved = std::mem::take(&mut self.env);
                let saved_roots = std::mem::take(&mut self.roots);
                let saved_facts = std::mem::take(&mut self.facts);
                let saved_module = std::mem::replace(&mut self.module, def.module.clone());
                self.facts = def.facts.iter().cloned().collect();
                self.roots.clear();
                self.env.clear();
                let mut fields = BTreeMap::new();
                for (n, t) in &def.fields {
                    let phase = self.phase;
                    if def.ideal_fields.contains(n) && self.phase == Phase::Runtime {
                        self.phase = Phase::Ideal;
                    }
                    let t = self.resolve(t)?;
                    let v = self.arbitrary(&t)?;
                    self.phase = phase;
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
                self.module = saved_module;
                Ok(value)
            }
        }
    }

    fn assign(&mut self, place: &Expr, value: &Expr) -> Result<()> {
        if place.indirect_place() {
            let (reference, fields) = self.location(place)?;
            let id = self.memory.plane(reference)?;
            let owned = self.owns_plane(id)?;
            if !self.write_permitted(reference, &fields, owned)? {
                return Err(format!("line {}: writes through reference parameters need an effect contract; unsupported", place.line));
            }
            let old = project(self.memory.read(reference)?, &fields)?.clone();
            if self.symbol_is_affine(&old)
                && !(self.phase == Phase::Ideal && self.erased_value(&old))
            {
                return Err("overwriting owned fields through references requires ownership effect proofs; unsupported".into());
            }
            let mut new = self.eval(value, Some(&old.ty()))?;
            let replace_plane = !self.same_layout(&old, &new)?;
            if !replace_plane {
                self.preserve_views(&old, &mut new)?;
            }
            let mut root = self.memory.read(reference)?.clone();
            self.replace_projection(&mut root, &fields, new)?;
            let lifted = self.opened_planes.get(&id).cloned().unwrap_or_default();
            // Validate against the resulting store: a field reference may point
            // back into this very root. Failure rejects the whole verification.
            self.memory.write(id, root.clone(), replace_plane)?;
            self.retained_valid_with(&root, place.line, &lifted)?;
            for (n, plane) in &self.roots {
                if *plane == id {
                    self.env.insert(n.clone(), root.clone());
                }
            }
            return self.validate_opened_planes(place.line);
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
        self.runtime_name(&name)?;
        let old = if let Kind::Name(n) = &place.kind {
            if let Some(value) = self.roots.get(n).and_then(|id| self.memory.get(*id).ok()) {
                value.clone()
            } else {
                self.env
                    .get(n)
                    .cloned()
                    .ok_or("unknown assignment target")?
            }
        } else {
            self.storage(place)?
        };
        let mut new = self.eval(value, Some(&old.ty()))?;
        if self.dropping && self.symbol_is_affine(&old) {
            return Err(
                "destructors cannot replace owning fields without cleanup/effect proofs".into(),
            );
        }
        let replace_plane = !self.same_layout(&old, &new)?;
        if !replace_plane {
            self.preserve_views(&old, &mut new)?;
        }
        let old_live = self
            .roots
            .get(&name)
            .is_none_or(|id| self.memory.get(*id).is_ok());
        if !fields.is_empty() && !old_live {
            return Err(format!("line {}: field assignment cannot restore shape(T); replace consumed owner {name} as a whole", place.line));
        }
        if old_live && self.symbol_is_affine(&old) {
            self.validate_argument(&old, place.line)?;
            self.cleanup_value(old, place.line)?;
        }
        let mut root = if let Some(value) = self
            .roots
            .get(&name)
            .and_then(|id| self.memory.get(*id).ok())
        {
            value.clone()
        } else {
            self.env
                .get(&name)
                .cloned()
                .ok_or("unknown assignment target")?
        };
        replace(&mut root, &fields, new)?;
        let lifted = self
            .roots
            .get(&name)
            .and_then(|plane| self.opened_planes.get(plane))
            .cloned()
            .unwrap_or_default();
        if let Some(id) = self.roots.get(&name) {
            self.memory.write(*id, root.clone(), replace_plane)?;
        }
        self.retained_valid_with(&root, place.line, &lifted)?;
        self.env.insert(name, root);
        self.validate_opened_planes(place.line)
    }

    fn statement(&mut self, s: &Statement) -> Result<()> {
        let start = self.temporaries.len();
        self.statement_inner(s)?;
        self.finish_temporaries(start)
    }

    fn finish_temporaries(&mut self, start: usize) -> Result<()> {
        for (value, line) in self.temporaries.split_off(start).into_iter().rev() {
            self.validate_argument(&value, line)
                .map_err(|e| format!("line {line}: implicit temporary cleanup: {e}"))?;
            self.cleanup_value(value, line)?;
        }
        Ok(())
    }

    fn scoped_eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let start = self.temporaries.len();
        let value = self.eval(e, expected)?;
        self.finish_temporaries(start)?;
        Ok(value)
    }

    fn statement_inner(&mut self, s: &Statement) -> Result<()> {
        match s {
            Statement::Ideal(binding) => {
                if let Statement::Assign { target, .. } = binding.as_ref() {
                    fn erased(context: &Context<'_>, expression: &Expr) -> bool {
                        match &expression.kind {
                            Kind::Name(name) => {
                                context.ideal_execution || context.ideal_bindings.contains(name)
                            }
                            Kind::Index(base, _) => erased(context, base),
                            Kind::Unary(op, _) if op == "*" => {
                                // Following a pointer resets the storage role:
                                // an erased pointer can still target live data.
                                context
                                    .hint(expression)
                                    .is_some_and(|ty| context.proof_storage(&ty))
                            }
                            Kind::Field(base, field) => {
                                erased(context, base)
                                    || matches!(context.hint(base), Some(Ty::Record(name)) if context.structs[&name].ideal_fields.contains(field))
                            }
                            _ => false,
                        }
                    }
                    if !erased(self, target) {
                        return Err("ideal assignments cannot modify runtime storage".into());
                    }
                }
                if !matches!(
                    binding.as_ref(),
                    Statement::Let { .. }
                        | Statement::Destructure { .. }
                        | Statement::Assign { .. }
                ) {
                    return Err(
                        "ideal statements require a binding, complete pattern, or ideal assignment"
                            .into(),
                    );
                }
                let phase = std::mem::replace(&mut self.phase, Phase::Ideal);
                let result = self.statement(binding);
                self.phase = phase;
                result?;
                self.ideal_bindings
                    .extend(binding.bindings().into_iter().map(str::to_owned));
                Ok(())
            }
            Statement::Destructure {
                record,
                fields,
                value,
            } => {
                self.representation_access(record, value.line)?;
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
                    if def.ideal_fields.contains(field) {
                        self.ideal_bindings.insert(name.clone());
                    }
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
                let value = self.eval(e, None)?;
                if self.symbol_is_affine(&value) {
                    self.validate_argument(&value, e.line)?;
                }
                self.cleanup_value(value, e.line)
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

    // A contents replacement preserves storage identity, including previously
    // materialized symbolic cell paths. Rebuild their values from new contents.
    fn preserve_views(&mut self, old: &Symbol, new: &mut Symbol) -> Result<()> {
        self.charge_value_work(1)?;
        match (old, new) {
            (
                Symbol::Array {
                    cells: observed, ..
                },
                Symbol::Array {
                    element,
                    identity,
                    items,
                    cells,
                    ..
                },
            ) if self.history_element(element) => {
                self.charge_value_work(observed.len())?;
                for index in observed.keys() {
                    let value =
                        self.read_array(element, identity, index, items.as_deref(), cells)?;
                    cells.insert(index.clone(), value);
                }
            }
            (
                Symbol::Array {
                    items: Some(before),
                    ..
                },
                Symbol::Array {
                    items: Some(after), ..
                },
            ) => {
                for (previous, value) in before.iter().zip(after) {
                    self.preserve_views(previous, value)?;
                }
            }
            (Symbol::Record(a, before), Symbol::Record(b, after)) if a == b => {
                for (name, value) in after {
                    if let Some(previous) = before.get(name) {
                        self.preserve_views(previous, value)?;
                    }
                }
            }
            _ => {}
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
                    ..
                },
                Symbol::Array {
                    len: b,
                    items: bv,
                    identity: bi,
                    ..
                },
            ) => {
                self.obligations += 1;
                for path in extend(
                    &self.paths,
                    &equal(a, b)?,
                    true,
                    self.session,
                    &mut self.value_work,
                )? {
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
                        || self.history_element(element)
                        || matches!(
                            **element,
                            Ty::Int | Ty::Nat | Ty::Machine(_) | Ty::Bool | Ty::Ref(_) | Ty::Unit
                        )),
                }
            }
            (Symbol::Number(_, _), Symbol::Number(_, _))
            | (Symbol::Bool(_), Symbol::Bool(_))
            | (Symbol::Ref(..), Symbol::Ref(..))
            | (Symbol::Plane(..), Symbol::Plane(..))
            | (Symbol::Unit, Symbol::Unit) => Ok(true),
            _ => Ok(false),
        }
    }

    fn location(&mut self, e: &Expr) -> Result<(Reference, Vec<Projection<Linear>>)> {
        match &e.kind {
            Kind::Name(n) => {
                self.runtime_name(n)?;
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
                let Symbol::Record(typename, _) = project(self.memory.read(r)?, &path)? else {
                    return Err("field reference requires a record".into());
                };
                self.field_access(typename, n, e.line)?;
                path.push(Projection::Field(n.clone()));
                project(self.memory.read(r)?, &path)?;
                Ok((r, path))
            }
            Kind::Index(base, i) => {
                let (r, mut path) = self.location(base)?;
                let index = self.nonnegative(i, "nonnegative reference index")?;
                self.charge_value_work(symbol_weight(self.memory.read(r)?)?)?;
                let mut root = self.memory.read(r)?.clone();
                let array = project(&root, &path)?.clone();
                let Symbol::Array {
                    element,
                    len,
                    items,
                    cells,
                    identity,
                } = array
                else {
                    return Err("reference index requires array storage".into());
                };
                self.prove(
                    &Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?),
                    "reference index < length",
                    e.line,
                )?;
                let literal = constant_index(&index)
                    .and_then(|i| items.as_ref().and_then(|items| items.get(i)));
                if !cells.contains_key(&index)
                    && (literal.is_none() || self.history_element(element.as_ref()))
                {
                    if !self.history_element(element.as_ref()) {
                        return Err("borrowing opaque array elements requires scalars or copyable scalar-field records".into());
                    }
                    let value =
                        self.read_array(&element, &identity, &index, items.as_deref(), &cells)?;
                    let Symbol::Array { cells, .. } = project_mut(&mut root, &path)? else {
                        return Err("invalid array storage".into());
                    };
                    cells.insert(index.clone(), value);
                    let plane = self.memory.plane(r)?;
                    self.memory.write(plane, root, false)?;
                }
                path.push(Projection::Index(index));
                project(self.memory.read(r)?, &path)?;
                Ok((r, path))
            }
            Kind::Unary(op, x) if op == "*" => {
                let (r, path) = match self.storage(x)? {
                    Symbol::Ref(_, r, path) => (r, path),
                    Symbol::Plane(_, r) => (r, Vec::new()),
                    _ => return Err("dereference requires a reference or owned plane".into()),
                };
                self.memory.read(r)?;
                Ok((r, path))
            }
            _ => Err(format!("line {}: expected a referenceable place", e.line)),
        }
    }

    fn declared_hint(t: &Type) -> Option<Ty> {
        match t {
            Type::Int => Some(Ty::Int),
            Type::Nat => Some(Ty::Nat),
            Type::Bool => Some(Ty::Bool),
            Type::Unit => Some(Ty::Unit),
            Type::Machine(t) => Some(Ty::Machine(*t)),
            Type::Named(n) => Some(Ty::Record(n.clone())),
            Type::Ref(t) => Self::declared_hint(t).map(|t| Ty::Ref(Box::new(t))),
            Type::Plane(t) => Self::declared_hint(t).map(|t| Ty::Plane(Box::new(t))),
            Type::Array(..) => None,
        }
    }

    // Read types from already modeled storage without evaluation or proof
    // assumptions. This includes arrays behind record fields and references;
    // dependent extents cannot be reconstructed from a field declaration alone.
    fn stored_hint(&self, expression: &Expr) -> Option<&Symbol> {
        match &expression.kind {
            Kind::Name(name) => {
                if let Some(plane) = self.roots.get(name) {
                    self.memory.get(*plane).ok()
                } else {
                    self.env.get(name)
                }
            }
            Kind::Field(base, field) => match self.stored_hint(base)? {
                Symbol::Record(_, fields) => fields.get(field),
                _ => None,
            },
            Kind::Unary(op, base) if op == "*" => match self.stored_hint(base)? {
                Symbol::Ref(_, reference, path) => {
                    project(self.memory.read(*reference).ok()?, path).ok()
                }
                Symbol::Plane(_, reference) => self.memory.read(*reference).ok(),
                _ => None,
            },
            Kind::Index(base, index) => {
                let index = match index.kind {
                    Kind::Number(index) | Kind::Constant(_, index) => {
                        usize::try_from(index).ok()?
                    }
                    _ => return None,
                };
                match self.stored_hint(base)? {
                    Symbol::Array {
                        items: Some(items), ..
                    } => items.get(index),
                    Symbol::Array { cells, .. } => cells.get(&Linear::number(index as i128)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn hint(&self, e: &Expr) -> Option<Ty> {
        if let Some(value) = self.stored_hint(e) {
            return Some(value.ty());
        }
        match &e.kind {
            Kind::Bool(_) => Some(Ty::Bool),
            Kind::Call(name, args) if name == "old" && args.len() == 1 => Self::old_key(&args[0])
                .and_then(|key| self.old_values.get(&key).map(Symbol::ty))
                .or_else(|| self.hint(&args[0])),
            Kind::Call(name, _) if name == "nat" => Some(Ty::Nat),
            Kind::Call(name, _) if name == "int" => Some(Ty::Int),
            Kind::Call(name, args) if name == "alloc" && args.len() == 1 => {
                self.hint(&args[0]).map(|t| Ty::Plane(Box::new(t)))
            }
            Kind::Constant(t, _) => Some(Ty::Machine(*t)),
            Kind::Name(n) => self.env.get(n).map(Symbol::ty),
            Kind::Record(n, _) => Some(Ty::Record(n.clone())),
            Kind::Unary(op, x) if op == "&" => self.hint(x).map(|t| Ty::Ref(Box::new(t))),
            Kind::Unary(op, x) if op == "*" => {
                if let Some(Ty::Ref(t) | Ty::Plane(t)) = self.hint(x) {
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
                let Ty::Record(name) = self.hint(base)? else {
                    return None;
                };
                self.structs
                    .get(&name)?
                    .fields
                    .iter()
                    .find(|(n, _)| n == field)
                    .and_then(|(_, t)| Self::declared_hint(t))
            }
            Kind::Binary(op, _, _)
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "=>"
                ) =>
            {
                Some(Ty::Bool)
            }
            Kind::Binary(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::If(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::Call(n, _) => self
                .functions
                .get(n)
                .and_then(|f| Self::declared_hint(&f.ret)),
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
            return self.proof_script(goal, label, line, steps);
        }
        self.prove(goal, label, line)
    }

    fn eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        if self.eval_depth >= 32 || self.eval_steps >= 100_000 {
            return Err(format!(
                "line {}: verification evaluation limit reached",
                e.line
            ));
        }
        self.eval_depth += 1;
        self.eval_steps += 1;
        let result = self.eval_checked(e, expected);
        self.eval_depth -= 1;
        result
    }

    fn eval_checked(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let value = self.eval_inner(e, expected).map_err(|s| {
            if s.starts_with("line ") {
                s
            } else {
                format!("line {}: {s}", e.line)
            }
        })?;
        self.charge_value_work(symbol_weight(&value)?)
            .map_err(|error| format!("line {}: {error}", e.line))?;
        let projecting_owner = matches!(&e.kind, Kind::Field(..) | Kind::Index(..))
            || matches!(&e.kind, Kind::Unary(op, _) if op == "*");
        if self.phase != Phase::Specification && self.symbol_is_affine(&value) && projecting_owner {
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
            Symbol::Plane(..) => true,
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
            Ty::Plane(_) => true,
            Ty::Record(n) => is_affine(&Type::Named(n.clone()), self.structs, self.drops),
            Ty::Array(t, _) => self.ty_is_affine(t),
            _ => false,
        }
    }

    // Extensional array histories can compare these values structurally.
    // Reference identity, nested arrays, and owning values need their own rules.
    // Reference-free scalar trees can be havoced without changing storage
    // identity, layouts, or hidden reference provenance. Affinity is a separate
    // condition: array histories need copyable values, proof effects do not.
    fn scalar_field_value(&self, t: &Ty) -> bool {
        fn fields(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
            match t {
                Type::Named(name) => structs.get(name).is_some_and(|definition| {
                    definition.fields.iter().all(|(_, ty)| fields(ty, structs))
                }),
                Type::Ref(_) | Type::Plane(_) | Type::Array(..) => false,
                _ => true,
            }
        }
        match t {
            Ty::Record(name) => fields(&Type::Named(name.clone()), self.structs),
            Ty::Ref(_) | Ty::Plane(_) | Ty::Array(..) => false,
            _ => true,
        }
    }

    fn history_element(&self, t: &Ty) -> bool {
        !self.ty_is_affine(t) && self.scalar_field_value(t)
    }

    fn ty_has_reference(&self, t: &Ty) -> bool {
        match t {
            Ty::Ref(_) | Ty::Plane(_) => true,
            Ty::Array(element, _) => self.ty_has_reference(element),
            Ty::Record(name) => type_has_reference(&Type::Named(name.clone()), self.structs),
            _ => false,
        }
    }

    fn assume_element_type(&mut self, value: &Symbol) -> Result<()> {
        let bounds = match value {
            Symbol::Number(Ty::Machine(t), n) => {
                let (lo, hi) = t.bounds();
                vec![n.sub(&Linear::number(lo))?, Linear::number(hi).sub(n)?]
            }
            Symbol::Number(Ty::Nat, n) => vec![n.clone()],
            Symbol::Array { len, .. } => vec![len.clone()],
            _ => Vec::new(),
        };
        for bound in bounds {
            if self.paths.iter().any(|path| !path.contains(&bound)) {
                self.assume(&Formula::Ge(bound))?;
            }
        }
        if let Symbol::Array { items, cells, .. } = value {
            for element in items.iter().flatten().chain(cells.values()) {
                self.assume_element_type(element)?;
            }
        }
        if let Symbol::Record(name, fields) = value {
            for value in fields.values() {
                self.assume_element_type(value)?;
            }
            let definition = self
                .structs
                .get(name)
                .cloned()
                .ok_or("unknown array element type")?;
            if let Some(invariant) = definition.invariant {
                let saved_module = std::mem::replace(&mut self.module, definition.module.clone());
                let env = std::mem::replace(&mut self.env, fields.clone());
                let roots = std::mem::take(&mut self.roots);
                let facts =
                    std::mem::replace(&mut self.facts, definition.facts.into_iter().collect());
                self.env.insert("self".into(), value.clone());
                let invariant = self.proposition(&invariant)?;
                self.assume(&invariant)?;
                self.env = env;
                self.roots = roots;
                self.facts = facts;
                self.module = saved_module;
            }
        }
        Ok(())
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
                self.env.remove(&name).ok_or("unknown cleanup binding")?
            };
            if self.symbol_is_affine(&value) {
                self.validate_argument(&value, f.result.line)?;
            }
            if self.phase == Phase::Runtime && !self.ideal_bindings.contains(&name) {
                if name == "self" && f.drop_target.is_some() {
                    self.cleanup_fields(value, f.result.line)?;
                } else {
                    self.cleanup_value(value, f.result.line)?;
                }
            }
        }
        Ok(())
    }

    fn read_array(
        &mut self,
        element: &Ty,
        identity: &str,
        index: &Linear,
        items: Option<&[Symbol]>,
        cells: &BTreeMap<Linear, Symbol>,
    ) -> Result<Symbol> {
        if self.history_element(element) {
            let observations = values_weight(cells.values())?
                .saturating_add(values_weight(items.into_iter().flatten())?);
            self.charge_value_work(observations)?;
            let observed = cells
                .iter()
                .map(|(index, value)| (index.clone(), value.clone()))
                .chain(
                    items
                        .into_iter()
                        .flatten()
                        .enumerate()
                        .map(|(index, value)| (Linear::number(index as i128), value.clone())),
                )
                .collect::<Vec<_>>();
            for (index, value) in observed {
                let key = (identity.to_owned(), index);
                if let Some(existing) = self.array_reads.get(&key).cloned() {
                    if existing != value {
                        self.assume(&self.symbol_equal(&existing, &value)?)?;
                    }
                } else {
                    self.array_reads.insert(key, value);
                }
            }
        }
        self.array_read(element, identity, index)
    }

    fn array_read(&mut self, element: &Ty, identity: &str, index: &Linear) -> Result<Symbol> {
        self.charge_value_work(1)?;
        if self.array_read_depth >= 64 {
            return Err("array history read depth limit reached (64)".into());
        }
        self.array_read_depth += 1;
        let result = (|| {
            let value = self.array_read_value(element, identity, index)?;
            self.replay_array_history(element, identity, index, &value)?;
            Ok(value)
        })();
        self.array_read_depth -= 1;
        result
    }

    fn array_read_value(&mut self, element: &Ty, identity: &str, index: &Linear) -> Result<Symbol> {
        // Stable contents identities give extensional reads across scopes. A
        // reference-bearing selection needs an alias rule, not a fresh plane.
        if self.ty_has_reference(element) {
            return Err("symbolic reads of reference-containing array elements need an alias contract; unsupported".into());
        }
        let key = (identity.to_owned(), index.clone());
        if let Some(value) = self.array_reads.get(&key).cloned() {
            // Replay type facts, never facts specific to the first read's path.
            self.assume_history_type(&value, !self.array_history.contains_key(identity))?;
            return Ok(value);
        }
        let value = if self.history_element(element) {
            let value = self.history_value(element)?;
            self.assume_history_type(&value, !self.array_history.contains_key(identity))?;
            value
        } else {
            self.arbitrary(element)?
        };
        if self.history_element(element) {
            let observations = self
                .array_reads
                .iter()
                .filter(|((contents, _), _)| contents == identity)
                .map(|((_, index), value)| (index.clone(), value.clone()))
                .collect::<Vec<_>>();
            for (other, previous) in observations {
                if index.terms == other.terms && index.constant != other.constant {
                    continue;
                }
                let aliases = equal(index, &other)?;
                let relation = aliases.not().or(self.symbol_equal(&value, &previous)?);
                self.assume(&relation)?;
            }
        }
        self.array_reads.insert(key, value.clone());
        Ok(value)
    }

    fn storage(&mut self, e: &Expr) -> Result<Symbol> {
        let value = self.storage_inner(e)?;
        self.charge_value_work(symbol_weight(&value)?)?;
        Ok(value)
    }

    fn storage_inner(&mut self, e: &Expr) -> Result<Symbol> {
        match &e.kind {
            Kind::Name(n) => {
                self.runtime_name(n)?;
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
                let Symbol::Record(typename, fields) = self.storage(base)? else {
                    return Err("field access requires struct storage".into());
                };
                self.field_access(&typename, name, e.line)?;
                fields
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {name}"))
            }
            Kind::Unary(op, _) if op == "*" => {
                let (r, path) = self.location(e)?;
                self.read_projection_value(r, &path)
            }
            Kind::Index(base, index) => {
                let array = self.storage(base)?;
                let index = self.nonnegative(index, "nonnegative storage index")?;
                let Symbol::Array {
                    element,
                    len,
                    items,
                    cells,
                    identity,
                } = array
                else {
                    return Err("index requires array storage".into());
                };
                self.prove(
                    &Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?),
                    "storage index < length",
                    e.line,
                )?;
                if self.history_element(element.as_ref()) {
                    return self.read_array(&element, &identity, &index, items.as_deref(), &cells);
                }
                if index.terms.is_empty() {
                    if let Some(v) = items
                        .as_ref()
                        .and_then(|xs| usize::try_from(index.constant).ok().and_then(|i| xs.get(i)))
                    {
                        return Ok(v.clone());
                    }
                }
                if index.terms.is_empty() {
                    if let Ok(i) = usize::try_from(index.constant) {
                        if let Some(value) = cells.get(&Linear::number(i as i128)) {
                            return Ok(value.clone());
                        }
                    }
                }
                self.read_array(&element, &identity, &index, items.as_deref(), &cells)
            }
            _ => {
                let value = self.eval(e, None)?;
                if self.phase != Phase::Specification && self.symbol_is_affine(&value) {
                    self.temporaries.push((value.clone(), e.line));
                }
                Ok(value)
            }
        }
    }

    fn fact_at(&mut self, place: &Expr, fact: &str, line: usize) -> Result<Formula> {
        if self.phase != Phase::Specification {
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
        let saved = self.clone_env()?;
        let roots = self.roots.clone();
        let facts = self.facts.clone();
        self.env = fields.clone();
        self.env.insert("self".into(), value);
        self.roots.clear();
        self.facts = def.facts.iter().cloned().collect();
        let saved_module = std::mem::replace(&mut self.module, def.module.clone());
        let result = self.proposition(&expression);
        self.module = saved_module;
        self.env = saved;
        self.roots = roots;
        self.facts = facts;
        result
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
                self.runtime_name(n)?;
                // Never let an unrelated fact redefine a type invariant.
                if !self.env.contains_key(n) {
                    if let Some(definition) = self.facts.get(n).cloned() {
                        if self.phase != Phase::Specification {
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
                if self.phase != Phase::Specification && self.symbol_is_affine(&value) {
                    if self.phase == Phase::Ideal && !self.erased_value(&value) {
                        return Err("ideal execution cannot consume runtime ownership; use a read-only proof view".into());
                    }
                    if self.phase == Phase::Runtime && !self.opened_planes.is_empty() {
                        return Err(
                            "runtime ownership moves are forbidden while invariants are open"
                                .into(),
                        );
                    }
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
                let Symbol::Record(typename, fields) = self.storage(base)? else {
                    return Err("field access requires a struct".into());
                };
                self.field_access(&typename, name, e.line)?;
                fields
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {name}"))
            }
            Kind::Record(name, entries) => {
                self.representation_access(name, e.line)?;
                if self.phase == Phase::Ideal
                    && is_affine(&Type::Named(name.clone()), self.structs, self.drops)
                    && !erased_type(&Type::Named(name.clone()), self.structs)
                {
                    return Err("ideal execution cannot construct runtime ownership".into());
                }
                let def = self
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown struct {name}"))?;
                if def.ideal && self.phase == Phase::Runtime {
                    return Err(format!(
                        "{name} is ideal data and cannot be constructed at runtime"
                    ));
                }
                let saved = self.clone_env()?;
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
                    let saved_phase = self.phase;
                    if def.ideal_fields.contains(n) && self.phase == Phase::Runtime {
                        self.phase = Phase::Ideal;
                    }
                    let evaluated = if let Type::Array(element, _) = ty {
                        // Supply the element type now; the complete dependent
                        // field type is checked once all literal fields exist.
                        let element = self.resolve(element)?;
                        self.eval_inner(
                            value,
                            Some(&Ty::Array(Box::new(element), Linear::number(0))),
                        )?
                    } else if matches!(ty, Type::Plane(_)) {
                        let ty = self.resolve(ty)?;
                        self.eval(value, Some(&ty))?
                    } else {
                        self.eval(value, hint.as_ref())?
                    };
                    self.phase = saved_phase;
                    fields.insert(n.clone(), evaluated);
                }
                self.env = saved;
                let record = Symbol::Record(name.clone(), fields);
                self.record_valid(&record, e.line)?;
                Ok(record)
            }
            Kind::Unary(op, x) if op == "&" => {
                let (r, path) = self.location(x)?;
                self.charge_value_work(symbol_weight(project(self.memory.read(r)?, &path)?)?)?;
                let target = project(self.memory.read(r)?, &path)?.clone();
                self.record_valid(&target, e.line)?;
                let ty = target.ty();
                Ok(Symbol::Ref(Box::new(ty), r, path))
            }
            Kind::Unary(op, _) if op == "*" => {
                let (r, path) = self.location(e)?;
                self.read_projection_value(r, &path)
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
            Kind::Binary(op, a, b) if matches!(op.as_str(), "&&" | "||" | "=>") => {
                let a = self.eval(a, Some(&Ty::Bool))?.proposition()?;
                // Logical expressions are pure. Both operands must be well-defined.
                let b = self.eval(b, Some(&Ty::Bool))?.proposition()?;
                Ok(Symbol::Bool(match op.as_str() {
                    "&&" => Formula::And(Box::new(a), Box::new(b)),
                    "=>" => Formula::Implies(Box::new(a), Box::new(b)),
                    _ => Formula::Or(Box::new(a), Box::new(b)),
                }))
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
                if matches!(ty, Ty::Ref(_)) && matches!(op.as_str(), "==" | "!=") {
                    let a = self.eval(a, Some(&ty))?;
                    let b = self.eval(b, Some(&ty))?;
                    let equal = self.reference_equality(&a, &b)?;
                    return Ok(Symbol::Bool(if op == "==" { equal } else { equal.not() }));
                }
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
                    cells: BTreeMap::new(),
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
                    cells,
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
                if self.history_element(&element) {
                    return self.read_array(&element, &identity, &index, items.as_deref(), &cells);
                }
                if index.terms.is_empty() {
                    if let Some(value) = items
                        .as_ref()
                        .and_then(|v| usize::try_from(index.constant).ok().and_then(|i| v.get(i)))
                    {
                        return Ok(value.clone());
                    }
                }
                if index.terms.is_empty() {
                    if let Ok(i) = usize::try_from(index.constant) {
                        if let Some(value) = cells.get(&Linear::number(i as i128)) {
                            return Ok(value.clone());
                        }
                    }
                }
                self.read_array(&element, &identity, &index, items.as_deref(), &cells)
            }
            Kind::Call(name, args) => {
                if name == "alloc" {
                    return self.allocate_owned(args, expected, e.line);
                }
                if name == "old" {
                    if self.phase == Phase::Runtime || args.len() != 1 {
                        return Err(
                            "old is proof-only and takes one entry-state parameter expression"
                                .into(),
                        );
                    }
                    let value = self.old_expression(&args[0], expected)?;
                    if self.phase == Phase::Ideal && self.symbol_is_affine(&value) {
                        return Err(
                            "old ownership snapshots are proof views, not new ideal resources"
                                .into(),
                        );
                    }
                    return Ok(value);
                }
                if name == "int" || name == "nat" {
                    if self.phase == Phase::Runtime {
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
                if self.phase == Phase::Specification && self.current.as_ref() == Some(name) {
                    return Err("recursive calls are forbidden in specifications".into());
                }
                if name == "move" || name == "drop" {
                    if self.phase == Phase::Runtime && !self.opened_planes.is_empty() {
                        return Err(
                            "moves and drops are forbidden while invariants are open".into()
                        );
                    }
                    if self.dropping {
                        return Err(
                            "destructors cannot transfer ownership or invoke nested cleanup".into(),
                        );
                    }
                    if self.phase == Phase::Specification {
                        return Err("specifications and facts cannot move or drop values".into());
                    }
                    if args.len() != 1 {
                        return Err(format!("{name} expects one place"));
                    }
                    if self.phase == Phase::Ideal
                        && !self.ideal_execution
                        && !matches!(&args[0].kind, Kind::Name(n) if self.ideal_bindings.contains(n))
                    {
                        return Err("erased execution cannot move or drop a runtime place".into());
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
                    if name == "drop" {
                        self.cleanup_value(value, e.line)?;
                        return Ok(Symbol::Unit);
                    }
                    return Ok(value);
                }
                let f = self.functions.get(name).ok_or_else(|| format!("unknown function {name}; calls require an earlier verified declaration; ideal recursion requires decreases"))?;
                if self.phase == Phase::Runtime
                    && !self.opened_planes.is_empty()
                    && !self.cleanup_helpers.contains(name)
                {
                    return Err("calls while invariants are open require checked scalar ownership-free effects".into());
                }
                if self.dropping
                    && self.phase == Phase::Runtime
                    && !self.cleanup_helpers.contains(name)
                {
                    return Err(
                        "destructor calls require a checked scalar ownership-free effect summary"
                            .into(),
                    );
                }
                if f.partial {
                    if self.phase != Phase::Runtime {
                        return Err("potentially divergent functions cannot be used in proofs or ideal execution".into());
                    }
                    self.partial_execution = true;
                }
                if self.phase == Phase::Specification
                    && (heap::owns_planes_type(&f.ret, self.structs)
                        || f.params
                            .iter()
                            .any(|(_, ty)| heap::owns_planes_type(ty, self.structs)))
                {
                    return Err("proof calls must borrow heap owners; ownership transfers and owning results cannot be erased".into());
                }
                if !f.modifies.is_empty() && self.phase == Phase::Specification {
                    return Err("modifying calls are forbidden in proof expressions".into());
                }
                if self.phase == Phase::Ideal && !f.ideal && !self.helpers.contains(name) {
                    return Err("modifying calls and runtime effects cannot be erased; an ideal expression needs ideal code or a checked pure scalar helper".into());
                }
                if f.ideal && self.phase == Phase::Runtime {
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
                for ((parameter, t), arg) in f.params.iter().zip(args) {
                    let hint = match t {
                        Type::Nat => Some(Ty::Nat),
                        Type::Int => Some(Ty::Int),
                        Type::Bool => Some(Ty::Bool),
                        Type::Machine(t) => Some(Ty::Machine(*t)),
                        Type::Plane(_) => Some(self.resolve(t)?),
                        _ => None,
                    };
                    let saved_specification = self.phase;
                    if f.ideal_params.contains(parameter) && self.phase != Phase::Specification {
                        self.phase = Phase::Ideal;
                    }
                    let value = if let (Type::Array(element, _), Kind::Array(_)) = (t, &arg.kind) {
                        if let Some(element) = self.literal_element_hint(element)? {
                            // Infer literal elements now; defer its length check
                            // to the isolated, fully bound callee environment.
                            self.eval_inner(
                                arg,
                                Some(&Ty::Array(Box::new(element), Linear::number(0))),
                            )?
                        } else {
                            self.eval(arg, hint.as_ref())?
                        }
                    } else {
                        self.eval(arg, hint.as_ref())?
                    };
                    self.phase = saved_specification;
                    self.validate_argument(&value, e.line)?;
                    actuals.push(value);
                }
                // A later argument can consume storage borrowed by an earlier
                // argument. Recheck the complete actual list at the call boundary.
                for value in &actuals {
                    self.validate_argument(value, e.line)?;
                }
                let mut saved = std::mem::take(&mut self.env);
                let saved_roots = std::mem::take(&mut self.roots);
                let saved_old = std::mem::take(&mut self.old_values);
                let saved_old_memory = self.old_memory.take();
                let saved_ideal = std::mem::take(&mut self.ideal_bindings);
                let saved_module = std::mem::replace(&mut self.module, f.module.clone());
                self.ideal_bindings = f.ideal_params.iter().cloned().collect();
                self.env.clear();
                self.roots.clear();
                self.bind_arguments(f, actuals, e.line)?;
                self.capture_old(f)?;
                if let Some(pre) = &f.pre {
                    let p = self.proposition(pre)?;
                    self.prove(&p, &format!("precondition of {name}"), e.line)?;
                }
                let inputs = if f
                    .params
                    .iter()
                    .any(|(_, ty)| type_has_reference(ty, self.structs))
                {
                    self.incoming_references(f, !f.modifies.is_empty())?
                } else {
                    Vec::new()
                };
                let writes = self.write_places(f, &inputs)?;
                // Even read-only contracts may observe reference identity.
                // An independent-port summary cannot describe aliased inputs.
                let overlaps = self.reference_ports_overlap(&inputs)?;
                if overlaps && f.external.is_some() {
                    return Err("external calls with overlapping reference ports require an alias-aware contract; unsupported".into());
                }
                if self.current.as_ref() == Some(name) && !f.partial {
                    let entry = self
                        .measure
                        .clone()
                        .ok_or("recursive calls require a decreases clause")?;
                    let expression = f
                        .decreases
                        .as_ref()
                        .ok_or("recursive calls require a decreases clause")?;
                    let saved_specification = self.phase;
                    self.phase = Phase::Specification;
                    let next = self.nonnegative(expression, "nonnegative recursion measure")?;
                    self.phase = saved_specification;
                    self.prove(
                        &Formula::Ge(entry.sub(&next)?.add(&Linear::number(-1))?),
                        "strictly decreasing recursion measure",
                        e.line,
                    )?;
                }
                let ret = self.resolve(&f.ret)?;
                let mut changed_roots = BTreeSet::new();
                for write in &writes {
                    let id = self.memory.plane(write.reference)?;
                    changed_roots.insert(id);
                    let owned =
                        self.owns_plane_in(&saved, &saved_roots, id)? || self.owns_plane(id)?;
                    if !self.write_permitted(write.reference, &write.path, owned)? {
                        return Err(format!("line {}: call to {name} writes through a parameter without a matching modifies contract", e.line));
                    }
                }
                let heap_call = heap::function_uses_planes(f, self.structs);
                let value = if overlaps
                    || heap_call
                    || !self.opened_planes.is_empty() && !f.modifies.is_empty()
                {
                    let reason = if overlaps {
                        "overlaps incoming references"
                    } else if heap_call {
                        "uses owned planes"
                    } else {
                        "writes while invariants are open"
                    };
                    self.check_actual_body(f, &ret, writes, inputs)
                        .map_err(|error| {
                            format!(
                                "line {}: call to {name} {reason}; body recheck failed: {error}",
                                e.line
                            )
                        })?
                } else {
                    let value = if !f.borrows.is_empty() {
                        let aliases = self.return_aliases(f, None)?;
                        self.return_shape(&ret, &mut Vec::new(), &aliases)?
                    } else {
                        self.arbitrary(&ret)?
                    };
                    for write in writes {
                        let id = self.memory.plane(write.reference)?;
                        let mut new = self.arbitrary(&write.ty)?;
                        self.charge_value_work(symbol_weight(self.memory.read(write.reference)?)?)?;
                        let mut root = self.memory.read(write.reference)?.clone();
                        self.preserve_views(project(&root, &write.path)?, &mut new)?;
                        self.replace_projection(&mut root, &write.path, new)?;
                        self.memory.write(id, root, false)?;
                    }
                    for input in inputs.iter().filter(|_| !f.modifies.is_empty()) {
                        // Each input's declared type is an implicit return contract.
                        // The body is checked to preserve these views even if the
                        // local parameter is rebound. Caller-only enclosing types
                        // are obligations below, not assumptions here.
                        self.charge_value_work(symbol_weight(project(
                            self.memory.read(input.reference)?,
                            &input.path,
                        )?)?)?;
                        let target =
                            project(self.memory.read(input.reference)?, &input.path)?.clone();
                        self.assume_element_type(&target)?;
                    }
                    if !f.borrows.is_empty() {
                        self.assume_return_type(&value, &ret)?;
                    }
                    self.env.insert("result".into(), value.clone());
                    if let Some(post) = &f.post {
                        let p = self.proposition(post)?;
                        self.assume(&p)?;
                    }
                    // Alias contracts describe entry storage. After applying the
                    // checked postcondition, revalidate the saved reference and its
                    // current target. Havoced contents need not satisfy nominal
                    // invariants until that postcondition has constrained them.
                    if !f.borrows.is_empty() && !f.modifies.is_empty() {
                        self.validate_argument(&value, e.line)?;
                    }
                    value
                };
                if heap_call {
                    // An actual body may write and then release storage it
                    // received by ownership. Surviving plain aliases are never;
                    // validating a fictional post-store root would revive it.
                    changed_roots.retain(|root| self.memory.get(*root).is_ok());
                }
                for root in &changed_roots {
                    self.charge_value_work(symbol_weight(self.memory.get(*root)?)?)?;
                    let stored = self.memory.get(*root)?.clone();
                    for (binding, plane) in &saved_roots {
                        if plane == root {
                            saved.insert(binding.clone(), stored.clone());
                        }
                    }
                }
                self.env = saved;
                self.roots = saved_roots;
                self.old_values = saved_old;
                self.old_memory = saved_old_memory;
                self.ideal_bindings = saved_ideal;
                self.module = saved_module;
                for root in changed_roots {
                    self.charge_value_work(symbol_weight(self.memory.get(root)?)?)?;
                    let stored = self.memory.get(root)?.clone();
                    let lifted = self.opened_planes.get(&root).cloned().unwrap_or_default();
                    self.retained_valid_with(&stored, e.line, &lifted)?;
                }
                if !f.modifies.is_empty() {
                    self.validate_live(e.line)?;
                }
                Ok(value)
            }
            Kind::If(condition, yes, no) => {
                let p = self
                    .scoped_eval(condition, Some(&Ty::Bool))?
                    .proposition()?;
                let base = self.paths.clone();
                // Give caller bindings stable storage identities before forking.
                for (name, value) in self.clone_env()? {
                    if !self.roots.contains_key(&name) {
                        self.roots.insert(name, self.memory.allocate(value)?);
                    }
                }
                let env = self.clone_env()?;
                let roots = self.roots.clone();
                let store = self.snapshot_memory()?;
                self.paths = extend(&base, &p, false, self.session, &mut self.value_work)?;
                let a = self.scoped_eval(yes, expected)?;
                let a_paths = self.paths.clone();
                let a_store = self.snapshot_memory()?;
                self.paths = extend(&base, &p, true, self.session, &mut self.value_work)?;
                self.charge_value_work(values_weight(env.values())?)?;
                self.env = env.clone();
                self.roots = roots.clone();
                self.memory = self.clone_store(&store)?;
                let b = self.scoped_eval(no, Some(&a.ty()))?;
                let b_paths = self.paths.clone();
                let b_store = self.snapshot_memory()?;
                self.paths = base;
                self.env = env;
                self.roots = roots;
                self.memory = self.clone_store(&store)?;
                let mut state_a = Formula::True;
                let mut state_b = Formula::True;
                let mut views = Vec::new();
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
                            let (joined, left, right) = self.join_value(av, bv, &mut views)?;
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
                let (result, left, right) = self.join_value(&a, &b, &mut views)?;
                let relation_a = state_a.and(left);
                let relation_b = state_b.and(right);
                let mut paths = extend(
                    &a_paths,
                    &relation_a,
                    false,
                    self.session,
                    &mut self.value_work,
                )?;
                paths.extend(extend(
                    &b_paths,
                    &relation_b,
                    false,
                    self.session,
                    &mut self.value_work,
                )?);
                // Drop infeasible branch combinations only with a checked
                // contradiction certificate; a failed probe keeps the path.
                paths = self.feasible_paths(paths)?;
                self.paths = paths::bounded(paths, self.session, &mut self.value_work)?;
                for view in views {
                    self.materialize_joined_reference(&view, e.line)?;
                }
                for (name, id) in &self.roots {
                    if let Ok(value) = self.memory.get(*id) {
                        self.env.insert(name.clone(), value.clone());
                    }
                }
                Ok(result)
            }
        }
    }

    fn join_value(
        &mut self,
        a: &Symbol,
        b: &Symbol,
        views: &mut Vec<Symbol>,
    ) -> Result<(Symbol, Formula, Formula)> {
        self.charge_value_work(1)?;
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
            (Symbol::Ref(at, ar, ap), Symbol::Ref(bt, br, bp))
                if at == bt
                    && ar == br
                    && ap.len() == bp.len()
                    && !ap.is_empty()
                    && self.history_element(at) =>
            {
                let offset = ap
                    .iter()
                    .zip(bp)
                    .position(|(a, b)| a != b)
                    .ok_or("conditional reference paths unexpectedly coincide")?;
                let (Projection::Index(a), Projection::Index(b)) = (&ap[offset], &bp[offset])
                else {
                    return Err(
                        "conditional references require one differing array index and matching field paths"
                            .into(),
                    );
                };
                if ap[offset + 1..] != bp[offset + 1..]
                    || ap[offset + 1..]
                        .iter()
                        .any(|step| !matches!(step, Projection::Field(_)))
                {
                    return Err("conditional references require one differing array index and matching field paths".into());
                }
                let index = self.arbitrary(&Ty::Nat)?.number()?;
                let mut path = ap.clone();
                path[offset] = Projection::Index(index.clone());
                let value = Symbol::Ref(at.clone(), *ar, path);
                views.push(value.clone());
                Ok((value, equal(&index, a)?, equal(&index, b)?))
            }
            (Symbol::Record(an, a), Symbol::Record(bn, b)) if an == bn && a.len() == b.len() => {
                let mut fields = BTreeMap::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for (name, value) in a {
                    let (value, l, r) =
                        self.join_value(value, b.get(name).ok_or("branch fields differ")?, views)?;
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
            ) if element == be
                && len == bl
                && a.len() == b.len()
                && !self.history_element(element) =>
            {
                let mut values = Vec::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for (a, b) in a.iter().zip(b) {
                    let (value, l, r) = self.join_value(a, b, views)?;
                    values.push(value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((
                    Symbol::Array {
                        element: element.clone(),
                        len: len.clone(),
                        items: Some(values),
                        cells: BTreeMap::new(),
                        identity: self.fresh_name(),
                    },
                    left,
                    right,
                ))
            }
            (
                Symbol::Array {
                    element,
                    len,
                    items: a_items,
                    cells: a_cells,
                    identity: a_id,
                },
                Symbol::Array {
                    element: b_element,
                    len: b_len,
                    items: b_items,
                    cells: b_cells,
                    identity: b_id,
                },
            ) if element == b_element && len == b_len && self.history_element(element) => {
                if a_id == b_id {
                    let mut cells = a_cells.clone();
                    for (index, value) in b_cells {
                        if cells.get(index).is_some_and(|existing| existing != value) {
                            return Err(
                                "inconsistent materialization of one array contents identity"
                                    .into(),
                            );
                        }
                        cells.insert(index.clone(), value.clone());
                    }
                    return Ok((
                        Symbol::Array {
                            element: element.clone(),
                            len: len.clone(),
                            items: a_items.clone(),
                            cells,
                            identity: a_id.clone(),
                        },
                        Formula::True,
                        Formula::True,
                    ));
                }
                let indices = a_cells
                    .keys()
                    .chain(b_cells.keys())
                    .cloned()
                    .chain(
                        (0..a_items.as_ref().map_or(0, Vec::len))
                            .map(|i| Linear::number(i as i128)),
                    )
                    .chain(
                        (0..b_items.as_ref().map_or(0, Vec::len))
                            .map(|i| Linear::number(i as i128)),
                    )
                    .collect::<BTreeSet<_>>();
                let condition = self.arbitrary(&Ty::Bool)?.proposition()?;
                let identity = self.fresh_name();
                self.array_history.insert(
                    identity.clone(),
                    ArrayHistory::Choice {
                        condition: condition.clone(),
                        left: a_id.clone(),
                        right: b_id.clone(),
                    },
                );
                let mut cells = BTreeMap::new();
                let mut left = condition.clone();
                let mut right = condition.not();
                for index in indices {
                    let a = a_items
                        .as_ref()
                        .and_then(|items| constant_index(&index).and_then(|i| items.get(i)))
                        .or_else(|| a_cells.get(&index));
                    let b = b_items
                        .as_ref()
                        .and_then(|items| constant_index(&index).and_then(|i| items.get(i)))
                        .or_else(|| b_cells.get(&index));
                    // Missing predecessor cells are read lazily under their
                    // history guard, never assumed outside their birth branch.
                    let (value, l, r) = match (a, b) {
                        (Some(a), Some(b)) => self.join_value(a, b, views)?,
                        (a, b) => {
                            let value = self.arbitrary(element)?;
                            let l = match a {
                                Some(a) => self.symbol_equal(&value, a)?,
                                None => Formula::True,
                            };
                            let r = match b {
                                Some(b) => self.symbol_equal(&value, b)?,
                                None => Formula::True,
                            };
                            (value, l, r)
                        }
                    };
                    cells.insert(index, value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((
                    Symbol::Array {
                        element: element.clone(),
                        len: len.clone(),
                        items: None,
                        cells,
                        identity,
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
    pub(crate) cleanup_helpers: BTreeSet<String>,
    trusted: Vec<crate::compiler::certificate::TrustedAssumption>,
    proof_searches: usize,
}

impl VerifiedProgram {
    pub(crate) fn uses_owned_planes(&self) -> bool {
        self.functions
            .iter()
            .any(|f| heap::function_uses_planes(f, &self.structs))
    }

    pub fn trusted_assumptions(&self) -> &[crate::compiler::certificate::TrustedAssumption] {
        &self.trusted
    }

    pub fn potentially_diverging_functions(&self) -> impl Iterator<Item = &str> {
        self.functions
            .iter()
            .filter(|f| f.partial)
            .map(|f| f.name.as_str())
    }

    pub fn proof_search_count(&self) -> usize {
        self.proof_searches
    }

    pub(crate) fn check_entry(&self) -> Result<()> {
        crate::shared::worker::run("evergreen-entry-checker", || self.check_entry_inner())
    }

    fn check_entry_inner(&self) -> Result<()> {
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
            let destructors = BTreeMap::new();
            let mut session = Session::search();
            let mut ctx = Context::new(
                &functions,
                &self.structs,
                &self.drops,
                &destructors,
                &helpers,
                &helpers,
                &mut session,
            );
            ctx.current = Some("main".into());
            ctx.capture_old(main)?;
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

// Bound the unfolded type graph before recursive property checks or symbolic
// record construction. Costs are computed once per declaration using the
// already checked prefix, so repeated fields cannot cause exponential work.
fn check_type_expansion(structs: &[Struct]) -> Result<()> {
    fn cost(t: &Type, known: &BTreeMap<String, (usize, usize)>) -> (usize, usize) {
        let (nodes, depth) = match t {
            Type::Named(n) => known.get(n).copied().unwrap_or((1, 1)),
            Type::Ref(t) | Type::Plane(t) | Type::Array(t, _) => cost(t, known),
            _ => (0, 0),
        };
        (nodes.saturating_add(1), depth.saturating_add(1))
    }
    let mut known = BTreeMap::new();
    for s in structs {
        let mut nodes = 1usize;
        let mut depth = 1usize;
        for (_, t) in &s.fields {
            let (n, d) = cost(t, &known);
            nodes = nodes.saturating_add(n);
            depth = depth.max(d.saturating_add(1));
        }
        if nodes > 2048 || depth > 64 {
            return Err(format!(
                "line {}: type expansion limit reached for {} (2048 nodes, depth 64)",
                s.line, s.name
            ));
        }
        known.insert(s.name.clone(), (nodes, depth));
    }
    Ok(())
}

fn verify_using(source: &str, session: &mut Session) -> Result<VerifiedProgram> {
    crate::shared::worker::run("evergreen-verifier", || verify_inner(source, session))
}

fn verify_inner(source: &str, session: &mut Session) -> Result<VerifiedProgram> {
    let parsed = syntax::parse(source)?;
    check_type_expansion(&parsed.structs)?;
    let mut structs = BTreeMap::new();
    let empty_functions = BTreeMap::new();
    let empty_drops = BTreeSet::new();
    let empty_destructors = BTreeMap::new();
    for s in &parsed.structs {
        if structs.contains_key(&s.name) {
            return Err(format!("line {}: duplicate struct {}", s.line, s.name));
        }
        let mut ctx = Context::new(
            &empty_functions,
            &structs,
            &empty_drops,
            &empty_destructors,
            &empty_drops,
            &empty_drops,
            session,
        );
        ctx.module = s.module.clone();
        ctx.declaring = Some(s.name.clone());
        ctx.phase = if s.ideal {
            Phase::Ideal
        } else {
            Phase::Runtime
        };
        for (n, t) in &s.fields {
            if s.ideal_fields.contains(n) && !erased_type(t, &structs) {
                return Err(format!("line {}: ideal field {n} may own only proof data; runtime owners must be borrowed", s.line));
            }
            if !s.ideal && !s.ideal_fields.contains(n) && !runtime_type(t, &structs) {
                return Err(format!(
                    "line {}: field {n} needs a runtime layout; use ideal type for proof data",
                    s.line
                ));
            }
            if n == "self" || ctx.env.contains_key(n) {
                return Err(format!("line {}: duplicate or reserved field {n}", s.line));
            }
            let phase = ctx.phase;
            if s.ideal_fields.contains(n) && ctx.phase == Phase::Runtime {
                ctx.phase = Phase::Ideal;
            }
            let t = ctx.resolve(t)?;
            let value = ctx.arbitrary(&t)?;
            ctx.phase = phase;
            ctx.env.insert(n.clone(), value);
        }
        let fields = ctx.clone_env()?;
        ctx.env
            .insert("self".into(), Symbol::Record(s.name.clone(), fields));
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
    let mut cleanup_helpers = BTreeSet::new();
    for (target, f) in &parsed.destructors {
        if structs.get(target).is_some_and(|s| s.module != f.module) {
            return Err(format!(
                "line {}: Drop must be defined in the type's defining module",
                f.line
            ));
        }
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
            return Err(format!("line {}: destructor effects require proofs; Drop bodies allow scalar work, checked scalar helpers, borrows, and facts without constructing or destructuring ownership", f.line));
        }
    }
    let destructors = parsed
        .destructors
        .iter()
        .map(|(name, method)| {
            let mut method = method.clone();
            method.entry_memory = needs_old_memory(&method);
            (name.clone(), method)
        })
        .collect::<BTreeMap<_, _>>();
    let mut all_functions = parsed.functions;
    all_functions.extend(parsed.destructors.into_iter().map(|(_, f)| f));
    let mut obligations = 0;
    for f in &mut all_functions {
        f.entry_memory = needs_old_memory(f);
        f.partial = f.external.is_some()
            || !f.ideal && f.decreases.is_none() && crate::compiler::effects::recursive(f);
        for (name, ty) in &f.params {
            if f.ideal_params.contains(name) && !erased_type(ty, &structs) {
                return Err(format!("line {}: ideal parameters may own only proof data; runtime owners must be borrowed", f.line));
            }
            if f.ideal && is_affine(ty, &structs, &drops) && !erased_type(ty, &structs) {
                return Err(format!(
                    "line {}: ideal functions may borrow runtime ownership but cannot consume it",
                    f.line
                ));
            }
        }
        if f.ideal && is_affine(&f.ret, &structs, &drops) && !erased_type(&f.ret, &structs) {
            return Err(format!(
                "line {}: ideal functions cannot produce runtime ownership",
                f.line
            ));
        }
        if !f.modifies.is_empty() {
            let references = f
                .params
                .iter()
                .filter(|(_, t)| type_has_reference(t, &structs))
                .collect::<Vec<_>>();
            if f.modifies.iter().any(|expression| {
                !borrow_expression(expression)
                    || !references
                        .iter()
                        .any(|(name, _)| Some(name.as_str()) == effect_origin(expression))
            }) {
                return Err(format!("line {}: modifies requires projections of incoming reference-bearing parameters", f.line));
            }
        }
        if !f.ideal
            && (!runtime_type(&f.ret, &structs)
                || f.params
                    .iter()
                    .any(|(n, t)| !f.ideal_params.contains(n) && !runtime_type(t, &structs)))
        {
            return Err(format!("line {}: runtime signatures require fixed-layout types; int/nat and ideal records are proof-only", f.line));
        }
        if matches!(
            f.name.rsplit("::").next().unwrap_or(&f.name),
            "move" | "drop" | "alloc" | "int" | "nat" | "old"
        ) {
            return Err(format!("line {}: {} is a reserved builtin", f.line, f.name));
        }
        returns::check_return_borrows(f, &structs)?;
        if functions.contains_key(&f.name) {
            return Err(format!("line {}: duplicate function {}", f.line, f.name));
        }
        if f.decreases.is_some() || f.partial {
            functions.insert(f.name.clone(), f.clone());
        }
        let mut ctx = Context::new(
            &functions,
            &structs,
            &drops,
            &destructors,
            &helpers,
            &cleanup_helpers,
            session,
        );
        ctx.module = f.module.clone();
        ctx.ideal_execution = f.ideal;
        ctx.partial_execution = f.partial;
        ctx.dropping = f.drop_target.is_some();
        let execution = if f.ideal {
            Phase::Ideal
        } else {
            Phase::Runtime
        };
        ctx.phase = execution;
        ctx.ideal_bindings = f.ideal_params.iter().cloned().collect();
        ctx.current = Some(f.name.clone());
        ctx.declare_parameters(f)?;
        ctx.capture_old(f)?;
        if let Some(pre) = &f.pre {
            ctx.phase = Phase::Specification;
            let p = ctx.eval(pre, Some(&Ty::Bool))?.proposition()?;
            ctx.assume(&p)?;
            ctx.phase = execution;
        }
        let inputs = if f.modifies.is_empty() && f.borrows.is_empty() {
            Vec::new()
        } else {
            ctx.incoming_references(f, !f.modifies.is_empty())?
        };
        ctx.writable = ctx.write_places(f, &inputs)?;
        ctx.input_references = inputs.clone();
        let ret = ctx.resolve(&f.ret)?;
        if let Some(measure) = &f.decreases {
            ctx.phase = Phase::Specification;
            ctx.measure = Some(ctx.nonnegative(measure, "nonnegative recursion measure")?);
            ctx.phase = execution;
        }
        if f.external.is_some() {
            ctx.check_external(f, &ret)?;
        } else {
            ctx.check_function_body(f, &ret, &inputs, true)?;
        }
        obligations += ctx.obligations;
        f.partial = ctx.partial_execution;
        if crate::compiler::effects::invariant_independent(f, &functions, &helpers) {
            helpers.insert(f.name.clone());
        }
        if crate::compiler::effects::ownership_free(f, &functions, &cleanup_helpers) {
            cleanup_helpers.insert(f.name.clone());
        }
        functions.insert(f.name.clone(), f.clone());
    }
    Ok(VerifiedProgram {
        functions: all_functions,
        structs,
        obligations,
        drops,
        cleanup_helpers,
        trusted: session.trusted_assumptions().to_vec(),
        proof_searches: session.search_count(),
    })
}

#[cfg(test)]
mod tests;
