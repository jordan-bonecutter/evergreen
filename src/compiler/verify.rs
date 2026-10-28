//! Internal elaboration and verification-condition generation.

use crate::shared::ownership::is_move_only;
use crate::{
    compiler::certificate::{ProofBundle, Session},
    compiler::kernel::Linear,
    shared::planes::{Memory, PlaneId, Projection as PlaneProjection, Reference},
    syntax::{self, Expr, Function, Kind, MachineInt, Statement, Struct, Type},
};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;
type Projection<I = Linear> = PlaneProjection<I, Ty>;

mod admissions;
mod array_history;
mod array_ports;
mod array_predicates;
mod array_values;
mod assignments;
mod diagnostics;
mod uninitialized_arrays;

#[cfg(test)]
pub(crate) mod array_model;
mod blocks;
mod bodies;
mod calls;
mod cases;
mod cleanup;
mod cleanup_summaries;
mod conditionals;
mod context;
mod conversions;
#[cfg(test)]
mod declaration_tests;
use context::{Context, Declarations};
mod evidence;
mod external;
mod footprints;
mod guarded_references;
mod heap;
mod ideal;
#[cfg(test)]
mod index_order_tests;
mod layout_queries;
mod literals;
mod logical_contracts;
mod loops;
mod machine_arithmetic;
#[cfg(test)]
mod match_tests;
mod ownership;
mod parameters;
mod paths;
mod places;
use paths::{extend, extend_from};
mod program;
mod proofs;
mod proposition;
mod quantified;
use proposition::Formula;
mod references;
#[cfg(test)]
pub(crate) mod replacement_tests;
mod returns;
mod state;
mod storage_layout;
mod subjects;
mod summaries;
mod union_borrows;
mod union_moves;
mod unions;
mod updates;
mod validation;
mod value_evidence;
mod write_contracts;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Ty {
    Int,
    Nat,
    Bool,
    Unit,
    Ref(Box<Ty>),
    Unique(Box<Ty>),
    Shared(Box<Ty>),
    Machine(MachineInt),
    Array(Box<Ty>, Linear),
    Record(String),
    Union(Vec<Ty>),
    Shape(Box<Ty>),
    Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Symbol {
    Union {
        members: Vec<Ty>,
        active: Linear,
        payloads: Vec<Option<Symbol>>,
    },
    Shape(Box<Ty>),
    Type {
        members: Vec<Ty>,
        active: Linear,
    },
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
    RefCases(Box<Ty>, Vec<guarded_references::Case>),
    Unique(Box<Ty>, Reference),
    Shared(Box<Ty>, crate::shared::planes::OwnedReference),
}

impl Symbol {
    fn ty(&self) -> Ty {
        match self {
            Self::Union { members, .. } => Ty::Union(members.clone()),
            Self::Shape(inner) => Ty::Shape(inner.clone()),
            Self::Type { .. } => Ty::Type,
            Self::Number(t, _) => t.clone(),
            Self::Bool(_) => Ty::Bool,
            Self::Array { element, len, .. } => Ty::Array(element.clone(), len.clone()),
            Self::Record(name, _) => Ty::Record(name.clone()),
            Self::Unit => Ty::Unit,
            Self::Ref(t, _, _) => Ty::Ref(t.clone()),
            Self::RefCases(t, _) => Ty::Ref(t.clone()),
            Self::Unique(t, _) => Ty::Unique(t.clone()),
            Self::Shared(t, _) => Ty::Shared(t.clone()),
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
        Type(&'a Ty, usize),
    }
    let mut pending = vec![Node::Value(value, 0)];
    let mut weight = 0usize;
    while let Some(node) = pending.pop() {
        weight = weight.saturating_add(1);
        let depth = match &node {
            Node::Value(_, depth) | Node::Formula(_, depth) | Node::Type(_, depth) => *depth,
        };
        if depth >= 128 || weight > MAX_VALUE_NODES {
            return Err("symbolic value expansion limit reached (32768 nodes, depth 128)".into());
        }
        match node {
            Node::Value(
                Symbol::Union {
                    members,
                    active,
                    payloads,
                },
                depth,
            ) => {
                weight = weight.saturating_add(active.terms.len());
                pending.extend(members.iter().map(|ty| Node::Type(ty, depth + 1)));
                pending.extend(
                    payloads
                        .iter()
                        .flatten()
                        .map(|value| Node::Value(value, depth + 1)),
                );
            }
            Node::Value(Symbol::Type { members, active }, depth) => {
                weight = weight.saturating_add(active.terms.len());
                pending.extend(members.iter().map(|ty| Node::Type(ty, depth + 1)));
            }
            Node::Value(Symbol::Shape(inner), depth) => pending.push(Node::Type(inner, depth + 1)),
            Node::Type(
                Ty::Ref(inner) | Ty::Unique(inner) | Ty::Shared(inner) | Ty::Shape(inner),
                depth,
            ) => pending.push(Node::Type(inner, depth + 1)),
            Node::Type(Ty::Union(members), depth) => {
                pending.extend(members.iter().map(|ty| Node::Type(ty, depth + 1)))
            }
            Node::Type(Ty::Array(inner, length), depth) => {
                weight = weight.saturating_add(length.terms.len());
                pending.push(Node::Type(inner, depth + 1));
            }
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
            Node::Value(Symbol::Ref(_, _, path), depth) => {
                weight = weight.saturating_add(path.len());
                for step in path {
                    if let Projection::Member { expected, .. } = step {
                        pending.push(Node::Type(expected, depth + 1));
                    }
                }
            }
            Node::Value(Symbol::RefCases(ty, cases), depth) => {
                pending.push(Node::Type(ty, depth + 1));
                for case in cases {
                    weight = weight.saturating_add(case.path.len() + 1);
                    for step in &case.path {
                        if let Projection::Member { expected, .. } = step {
                            pending.push(Node::Type(expected, depth + 1));
                        }
                    }
                    pending.push(Node::Formula(&case.guard, depth + 1));
                }
            }
            Node::Formula(Formula::Ge(n), _) => weight = weight.saturating_add(n.terms.len()),
            Node::Formula(Formula::Predicate { symbol, arguments }, _) => {
                if symbol.is_empty() {
                    return Err("predicate symbols must be nonempty".into());
                }
                weight = arguments
                    .iter()
                    .fold(weight.saturating_add(symbol.len()), |cost, argument| {
                        cost.saturating_add(1 + argument.terms.len())
                    });
            }
            Node::Formula(Formula::Not(p), depth) => pending.push(Node::Formula(p, depth + 1)),
            Node::Formula(
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b),
                depth,
            ) => {
                pending.push(Node::Formula(a, depth + 1));
                pending.push(Node::Formula(b, depth + 1));
            }
            Node::Formula(
                Formula::Forall {
                    variable,
                    domain,
                    body,
                },
                depth,
            ) => {
                if variable.is_empty() || variable.len() > 256 {
                    return Err("invalid quantified variable name".into());
                }
                weight = weight.saturating_add(variable.len());
                pending.push(Node::Formula(domain, depth + 1));
                pending.push(Node::Formula(body, depth + 1));
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
        (
            Projection::Member { index, expected },
            Symbol::Union {
                members, payloads, ..
            },
        ) if members.get(*index) == Some(expected) => payloads
            .get(*index)
            .and_then(Option::as_ref)
            .ok_or("union member has no accessible payload")?,
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
        (
            Projection::Member { index, expected },
            Symbol::Union {
                members, payloads, ..
            },
        ) => {
            if members.get(*index) != Some(expected) {
                return Err("union member interpretation type changed".into());
            }
            payloads
                .get_mut(*index)
                .and_then(Option::as_mut)
                .ok_or("union member has no accessible payload")?
        }
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
        Type::Ref(_) | Type::Unique(_) | Type::Shared(_) => true,
        Type::Union(members) => members.iter().any(|ty| type_has_reference(ty, structs)),
        Type::Shape(_) => false,
        Type::Array(t, _) => type_has_reference(t, structs),
        Type::Named(n) => structs
            .get(n)
            .is_some_and(|s| s.fields.iter().any(|(_, t)| type_has_reference(t, structs))),
        _ => false,
    }
}

fn type_has_borrowed_reference(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Ref(_) => true,
        Type::Unique(inner) | Type::Shared(inner) | Type::Array(inner, _) => {
            type_has_borrowed_reference(inner, structs)
        }
        Type::Shape(_) => false,
        Type::Union(members) => members
            .iter()
            .any(|ty| type_has_borrowed_reference(ty, structs)),
        Type::Named(name) => structs.get(name).is_some_and(|s| {
            s.fields
                .iter()
                .any(|(_, ty)| type_has_borrowed_reference(ty, structs))
        }),
        _ => false,
    }
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
        Type::Union(members) => members.iter().all(|ty| runtime_type(ty, structs)),
        Type::Array(t, _) | Type::Ref(t) | Type::Unique(t) | Type::Shared(t) | Type::Shape(t) => {
            runtime_type(t, structs)
        }
        _ => true,
    }
}

// Erased ownership belongs to proof data. Borrowed views can cross this phase
// boundary; their provenance and liveness use the ordinary reference rules.
fn erased_type(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Unique(_) | Type::Shared(_) => false,
        Type::Ref(_) => true,
        Type::Named(name) => structs
            .get(name)
            .is_some_and(|s| s.ideal && s.fields.iter().all(|(_, t)| erased_type(t, structs))),
        Type::Array(element, _) => erased_type(element, structs),
        Type::Union(members) => members.iter().all(|ty| erased_type(ty, structs)),
        Type::Shape(_) => true,
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
        Kind::Call(name, args) if matches!(name.as_str(), "size_of" | "align_of") => {
            matches!(
                args.as_slice(),
                [Expr {
                    kind: Kind::Type(_),
                    ..
                }]
            )
        }
        Kind::Call(name, args)
            if (matches!(name.as_str(), "integer" | "nat")
                || MachineInt::parse(name).is_some())
                && args.len() == 1 =>
        {
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
        Kind::If(_, yes, no) => borrow_expression(yes) && borrow_expression(no),
        _ => false,
    }
}

fn destructor_expression(e: &Expr) -> bool {
    match &e.kind {
        Kind::Block(body, tail) => destructor_body(body) && destructor_expression(tail),
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
        Statement::Destructure { value, .. } => {
            matches!(&value.kind, Kind::Name(name) if name == "self")
        }
        Statement::Assign { target, value, .. } => {
            destructor_expression(target) && destructor_expression(value)
        }
        Statement::Let { value, .. } | Statement::Fact { value, .. } | Statement::Effect(value) => {
            destructor_expression(value)
        }
        Statement::Proof { proposition, .. } => destructor_expression(proposition),
        Statement::Update { body, .. } => destructor_body(body),
        Statement::While {
            condition,
            invariant,
            modifies,
            decreases,
            body,
            ..
        } => {
            destructor_expression(condition)
                && destructor_expression(invariant)
                && modifies.iter().all(destructor_expression)
                && decreases.as_ref().is_none_or(destructor_expression)
                && destructor_body(body)
        }
    })
}

/// Specifications inspect values without consuming ownership. Ideal code is
/// erased computation, but its move-only values still move. Runtime code cannot
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
    guard: Formula,
    reference: Reference,
    path: Vec<Projection<Linear>>,
    ty: Box<Ty>,
}

#[derive(Clone)]
struct InputReference {
    // None retains physical alias/liveness checks without granting a named
    // nested source footprint for a symbolic array element.
    origin: Option<String>,
    guard: Formula,
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
            Kind::Block(body, tail) => body.iter().any(statement) || expression(tail),
            Kind::Array(items) | Kind::Call(_, items) => items.iter().any(expression),
            Kind::Record(_, fields) => fields.iter().any(|(_, e)| expression(e)),
            _ => false,
        }
    }

    fn ty(t: &Type) -> bool {
        match t {
            Type::Ref(t) | Type::Unique(t) | Type::Shared(t) | Type::Shape(t) => ty(t),
            Type::Union(members) => members.iter().any(ty),
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
            Statement::Assign { target, value, .. } => expression(target) || expression(value),
            Statement::Update { body, .. } => body.iter().any(statement),
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                ..
            } => {
                expression(condition)
                    || expression(invariant)
                    || decreases.as_ref().is_some_and(expression)
                    || modifies.iter().any(expression)
                    || body.iter().any(statement)
            }
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
    facts: state::State,
    module: Option<String>,
    censuses: BTreeMap<Reference, Linear>,
}

#[derive(Clone)]
enum ArrayHistory {
    Fill(Symbol),
    // Empty default; live resource cells stay in the array's sparse map.
    Uninitialized(Symbol),
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

impl<'a> Context<'a> {
    fn charge_value_work(&mut self, cost: usize) -> Result<()> {
        self.work.value_work = self.work.value_work.saturating_add(cost);
        if self.work.value_work > MAX_VALUE_WORK {
            return Err("symbolic value work limit reached (262144 nodes)".into());
        }
        Ok(())
    }

    fn clone_env(&mut self) -> Result<BTreeMap<String, Symbol>> {
        self.charge_value_work(values_weight(self.locals.values.values())?)?;
        Ok(self.locals.values.clone())
    }

    fn snapshot_memory(&mut self) -> Result<Memory<Symbol>> {
        self.charge_value_work(
            store_weight(&self.storage.memory)?
                .saturating_add(self.censuses.len().saturating_mul(2)),
        )?;
        Ok(self.storage.memory.snapshot())
    }

    fn clone_store(&mut self, store: &Memory<Symbol>) -> Result<Memory<Symbol>> {
        self.charge_value_work(store_weight(store)?)?;
        Ok(store.snapshot())
    }

    fn erased_value(&self, value: &Symbol) -> bool {
        match value.ty() {
            Ty::Union(members) => members.iter().all(|ty| self.proof_storage(ty)),
            Ty::Unique(_) | Ty::Shared(_) => false,
            Ty::Record(name) => erased_type(&Type::Named(name), self.declarations.structs),
            Ty::Array(element, _) => self.erased_ty(&element),
            Ty::Ref(_) => true,
            _ => true,
        }
    }

    fn proof_storage(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Union(members) => members.iter().all(|ty| self.proof_storage(ty)),
            Ty::Shape(inner) => self.proof_storage(inner),
            Ty::Nat | Ty::Int => true,
            Ty::Record(name) => self.declarations.structs[name].ideal,
            Ty::Array(element, _) => self.proof_storage(element),
            // A reference is itself a runtime word, regardless of its target.
            _ => false,
        }
    }

    fn erased_ty(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Union(members) => members.iter().all(|ty| self.proof_storage(ty)),
            Ty::Unique(_) | Ty::Shared(_) => false,
            Ty::Record(name) => erased_type(&Type::Named(name.clone()), self.declarations.structs),
            Ty::Array(element, _) => self.erased_ty(element),
            Ty::Ref(_) => true,
            _ => true,
        }
    }

    fn representation_access(&self, name: &str, line: usize) -> Result<()> {
        if self.locals.declaring.as_deref() == Some(name) {
            return Ok(());
        }
        let def = self
            .declarations
            .structs
            .get(name)
            .ok_or_else(|| format!("unknown struct {name}"))?;
        if def.opaque && def.module != self.locals.module {
            return Err(format!(
                "line {line}: {name} has an opaque representation outside its defining module"
            ));
        }
        Ok(())
    }

    fn field_access(&self, name: &str, field: &str, line: usize) -> Result<()> {
        self.representation_access(name, line)?;
        if self.execution.phase == Phase::Runtime
            && self.declarations.structs[name].ideal_fields.contains(field)
        {
            return Err(format!(
                "line {line}: {name}.{field} is ideal data and cannot be accessed at runtime"
            ));
        }
        Ok(())
    }

    fn follows(&mut self, proposition: &Formula) -> Result<bool> {
        for path in extend(
            &self.proof.paths,
            proposition,
            true,
            self.session,
            &mut self.work.value_work,
        )?
        .iter()
        {
            if !self.session.probe(path)? {
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
        self.remember_scalar_literal(value)?;
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
                for ((contents, index), value) in &self.arrays.reads {
                    if contents == identity {
                        observed
                            .entry(index.clone())
                            .or_insert_with(|| value.clone());
                    }
                }
                for (index, previous) in &observed {
                    self.arrays
                        .reads
                        .entry((identity.clone(), index.clone()))
                        .or_insert_with(|| previous.clone());
                }
                let next = self.fresh_name();
                self.arrays.history.insert(
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
            if self.array_input_origin(identity)?.is_some() {
                let mut replacement = cells
                    .get(target)
                    .cloned()
                    .ok_or("missing resource array write view")?;
                self.replace_projection(&mut replacement, &path[1..], new)?;
                let next = self.fresh_name();
                self.arrays.history.insert(
                    next.clone(),
                    ArrayHistory::Store {
                        base: identity.clone(),
                        index: target.clone(),
                        value: replacement.clone(),
                    },
                );
                cells.insert(target.clone(), replacement);
                *identity = next;
                return Ok(());
            }
            let empty = match self.arrays.history.get(identity) {
                Some(ArrayHistory::Uninitialized(initial)) => Some(initial.clone()),
                _ => None,
            };
            *identity = self.fresh_name();
            if let Some(initial) = empty {
                self.charge_value_work(symbol_weight(&initial)?)?;
                self.arrays
                    .history
                    .insert(identity.clone(), ArrayHistory::Uninitialized(initial));
            }
        }
        let child = match (&path[0], value) {
            (
                Projection::Member { index, expected },
                Symbol::Union {
                    members, payloads, ..
                },
            ) => {
                if members.get(*index) != Some(expected) {
                    return Err("union member interpretation type changed".into());
                }
                payloads
                    .get_mut(*index)
                    .and_then(Option::as_mut)
                    .ok_or("union member has no accessible payload")?
            }
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

    fn fresh_name(&mut self) -> String {
        self.work.fresh += 1;
        format!("evg_{}", self.work.fresh)
    }

    fn runtime_name(&self, name: &str) -> Result<()> {
        if self.locals.ideal_bindings.contains(name) && self.execution.phase == Phase::Runtime {
            return Err(format!(
                "{name} is an ideal parameter and cannot be read by runtime code"
            ));
        }
        Ok(())
    }

    fn capture_old(&mut self, function: &Function) -> Result<()> {
        if function.entry_memory {
            // An entry address must name the same parameter slot as the live
            // execution. Creating its slot only in the frozen store would give
            // old(&parameter) a fictional allocation identity.
            for (name, _) in &function.params {
                if !self.locals.places.contains_key(name) {
                    let value = self
                        .locals
                        .values
                        .get(name)
                        .cloned()
                        .ok_or("missing entry parameter")?;
                    self.charge_value_work(symbol_weight(&value)?)?;
                    let plane = self.allocate_symbol(value)?;
                    self.locals.places.insert(name.clone(), plane);
                }
            }
        }
        self.entry.world = self.proof.subjects.save_world()?;
        self.charge_value_work(values_weight(self.locals.values.values())?)?;
        let target_cost =
            self.locals
                .values
                .values()
                .try_fold(0usize, |cost, value| -> Result<usize> {
                    let extra = if let Symbol::Ref(_, reference, fields) = value {
                        symbol_weight(project(self.storage.memory.read(*reference)?, fields)?)?
                    } else if let Symbol::Unique(_, reference) = value {
                        symbol_weight(self.storage.memory.read(*reference)?)?
                    } else if let Symbol::Shared(_, owner) = value {
                        symbol_weight(self.storage.memory.read(owner.reference())?)?
                    } else {
                        0
                    };
                    Ok(cost.saturating_add(extra))
                })?;
        self.charge_value_work(target_cost)?;
        self.entry.values.clear();
        let mut targets = Vec::new();
        let mut conditional_targets = Vec::new();
        for (name, value) in &self.locals.values {
            self.entry.values.insert(name.clone(), value.clone());
            if let Symbol::Ref(_, reference, fields) = value {
                targets.push((name.clone(), *reference, fields.clone()));
            } else if matches!(value, Symbol::RefCases(..)) {
                conditional_targets.push((name.clone(), value.clone()));
            } else if let Symbol::Unique(_, reference) = value {
                targets.push((name.clone(), *reference, Vec::new()));
            } else if let Symbol::Shared(_, owner) = value {
                targets.push((name.clone(), owner.reference(), Vec::new()));
            }
        }
        for (name, reference, fields) in targets {
            let target = self.read_projection_value(reference, &fields, function.line)?;
            self.entry.values.insert(format!("*{name}"), target);
        }
        for (name, value) in conditional_targets {
            let target = self.read_reference(&value, function.line)?;
            self.entry.values.insert(format!("*{name}"), target);
        }
        self.entry.memory = if function.entry_memory {
            Some(Box::new(EntryMemory {
                env: self.clone_env()?,
                roots: self.locals.places.clone(),
                memory: self.snapshot_memory()?,
                facts: self.proof.subjects.snapshot(),
                module: self.locals.module.clone(),
                censuses: self.censuses.clone(),
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
            Kind::Type(_) => true,
            Kind::Call(name, args) => {
                let observed_call = MachineInt::parse(name).is_some()
                    || matches!(
                        name.as_str(),
                        "integer" | "nat" | "owner_count" | "size_of" | "align_of"
                    )
                    || self
                        .declarations
                        .functions
                        .get(name)
                        .is_some_and(|function| {
                            !function.partial
                                && function.modifies.is_empty()
                                && (matches!(
                                    function.ret,
                                    Type::Int
                                        | Type::Nat
                                        | Type::Bool
                                        | Type::Machine(_)
                                        | Type::Unit
                                ) || matches!(function.ret, Type::Ref(_))
                                    && !function.borrows.is_empty()
                                    && (function.ideal
                                        || self.declarations.cleanup_helpers.contains(name)))
                        });
                observed_call && args.iter().all(|arg| self.entry_observation(arg))
            }
            Kind::Unary(op, place) if op == "&" => self.entry_address(place),
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

    fn entry_address(&self, expression: &Expr) -> bool {
        match &expression.kind {
            Kind::Name(_) => true,
            Kind::Field(base, _) => self.entry_address(base),
            Kind::Index(base, index) => self.entry_address(base) && self.entry_observation(index),
            Kind::Unary(op, pointer) if op == "*" => self.entry_observation(pointer),
            _ => false,
        }
    }

    fn old_expression(&mut self, expression: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        if let Some(key) = Self::old_key(expression) {
            return self
                .entry
                .values
                .get(&key)
                .cloned()
                .ok_or_else(|| format!("{key} is not a function entry parameter"));
        }
        if !self.entry_observation(expression) {
            return Err(
                "old snapshots require entry storage or total scalar/reference observations without write or ownership effects".into(),
            );
        }
        let mut entry = self
            .entry
            .memory
            .take()
            .ok_or("old expression has no function entry memory")?;
        std::mem::swap(&mut self.locals.values, &mut entry.env);
        std::mem::swap(&mut self.locals.places, &mut entry.roots);
        std::mem::swap(&mut self.storage.memory, &mut entry.memory);
        std::mem::swap(&mut self.locals.module, &mut entry.module);
        std::mem::swap(&mut self.censuses, &mut entry.censuses);
        let live_state = self.proof.subjects.snapshot();
        self.proof.subjects.restore(entry.facts.clone());
        let facts = std::mem::take(&mut self.proof.facts);
        let proofs = std::mem::take(&mut self.proof.witnesses);
        let claims = std::mem::take(&mut self.proof.claims);
        let value_claims = std::mem::take(&mut self.proof.value_claims);
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let ownership_epoch = self.work.ownership_transitions;
        let value = self.eval(expression, expected);
        let changed_claims = self.work.ownership_transitions != ownership_epoch;
        self.execution.phase = phase;
        self.proof.facts = facts;
        self.proof.witnesses = proofs;
        self.proof.claims = claims;
        self.proof.value_claims = value_claims;
        std::mem::swap(&mut self.locals.values, &mut entry.env);
        std::mem::swap(&mut self.locals.places, &mut entry.roots);
        std::mem::swap(&mut self.storage.memory, &mut entry.memory);
        std::mem::swap(&mut self.locals.module, &mut entry.module);
        std::mem::swap(&mut self.censuses, &mut entry.censuses);
        entry.facts = self.proof.subjects.snapshot();
        self.proof.subjects.restore(live_state);
        self.entry.memory = Some(entry);
        if changed_claims {
            return Err("old observations cannot change allocation lifetime claims".into());
        }
        // Entry addresses refer to pre-existing slots or incoming storage.
        // Conditional selections may introduce a new symbolic cell path on an
        // incoming handle. Materialize its LIVE view separately from the read.
        if let Ok(value) = &value {
            self.materialize_input_planes()?;
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
        if self.execution.phase != Phase::Runtime {
            Ty::Int
        } else {
            Ty::Machine(MachineInt::parse("isize").expect("isize type"))
        }
    }

    fn assume(&mut self, p: &Formula) -> Result<()> {
        if self.proof.contract_parents.is_empty() {
            self.assume_from(p, paths::Origin::Unresolved)
        } else {
            let node = self
                .proof
                .evidence
                .contract(p.clone(), self.proof.contract_parents.clone())?;
            if self.evidence_dependencies(node)?.admissions.is_empty() {
                self.assume_from(p, paths::Origin::Evidence(node))
            } else {
                self.proof.value_claims.push(node);
                Ok(())
            }
        }
    }

    fn assume_from(&mut self, p: &Formula, origin: paths::Origin) -> Result<()> {
        let paths = extend_from(
            &self.proof.paths,
            p,
            false,
            origin,
            self.session,
            &mut self.work.value_work,
        )?;
        self.proof.paths = self.feasible_paths(paths)?;
        Ok(())
    }

    fn feasible_paths(&mut self, paths: paths::Paths) -> Result<paths::Paths> {
        paths::feasible(paths, self.session)
    }

    fn proposition(&mut self, e: &Expr) -> Result<Formula> {
        let saved = self.execution.phase;
        self.execution.phase = Phase::Specification;
        let result = self.eval(e, Some(&Ty::Bool)).and_then(|v| v.proposition());
        self.execution.phase = saved;
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
        let node = self.prove_subjects(p, None, label, line)?;
        if !self.evidence_dependencies(node)?.admissions.is_empty() {
            self.proof.value_claims.push(node);
        }
        Ok(())
    }

    fn resolve(&mut self, t: &Type) -> Result<Ty> {
        match t {
            Type::Apply(..) => Err("generic type requires concrete specialization before verification".into()),
            Type::Union(members) => self.resolve_union(members),
            Type::Shape(inner) => {
                let inner = self.resolve(inner)?;
                if matches!(inner, Ty::Shape(_)) { return Err("shape(shape(T)) is not a distinct storage state".into()); }
                Ok(Ty::Shape(Box::new(inner)))
            }
            Type::Int | Type::Nat if self.execution.phase == Phase::Runtime => Err("integer and nat are proof-only; use a machine integer for runtime storage or declare ideal code".into()),
            Type::Int => Ok(Ty::Int), Type::Nat => Ok(Ty::Nat),
            Type::Bool => Ok(Ty::Bool),
            Type::Machine(t) => Ok(Ty::Machine(*t)),
            Type::Unit => Ok(Ty::Unit),
            Type::Ref(t) => Ok(Ty::Ref(Box::new(self.resolve(t)?))),
            Type::Unique(t) => {
                if !runtime_type(t, self.declarations.structs) || !heap::payload_type(t, self.declarations.structs) {
                    return Err("owned planes require runtime payloads without borrowed references".into());
                }
                heap::payload_layout(t, self.declarations.structs)?;
                Ok(Ty::Unique(Box::new(self.resolve(t)?)))
            }
            Type::Shared(t) => {
                if !runtime_type(t, self.declarations.structs) || !heap::payload_type(t, self.declarations.structs) {
                    return Err("owning references require runtime payloads without borrowed references".into());
                }
                heap::payload_layout(t, self.declarations.structs)?;
                Ok(Ty::Shared(Box::new(self.resolve(t)?)))
            }
            Type::Named(n) => {
                if !self.declarations.structs.contains_key(n) {
                    return Err(format!(
                        "unknown struct {n}; recursive types are not supported yet"
                    ));
                }
                if self.declarations.structs.get(n).is_some_and(|s| s.ideal) && self.execution.phase == Phase::Runtime {return Err(format!("{n} is ideal data and has no runtime layout"));}
                Ok(Ty::Record(n.clone()))
            }
            Type::Array(element, len) => {
                let element = self.resolve(element)?;
                let saved_spec = self.execution.phase;
                self.execution.phase = Phase::Specification;
                let n = self.nonnegative(len, "nonnegative array length")?;
                self.execution.phase = saved_spec;
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
            Type::Unique(inner) => Ok(self
                .literal_element_hint(inner)?
                .map(|t| Ty::Unique(Box::new(t)))),
            Type::Shared(inner) => Ok(self
                .literal_element_hint(inner)?
                .map(|t| Ty::Shared(Box::new(t)))),
            _ => self.resolve(t).map(Some),
        }
    }

    fn compatible(&mut self, got: &Ty, expected: &Ty, line: usize) -> Result<()> {
        match (got, expected) {
            (Ty::Union(a), Ty::Union(b)) if a == b => Ok(()),
            (Ty::Shape(a), Ty::Shape(b)) => self.compatible(a, b, line),
            (Ty::Type, Ty::Type) => Ok(()),
            (Ty::Int, Ty::Int)
            | (Ty::Nat, Ty::Nat)
            | (Ty::Bool, Ty::Bool)
            | (Ty::Unit, Ty::Unit) => Ok(()),
            (Ty::Ref(a), Ty::Ref(b)) => self.compatible(a, b, line),
            (Ty::Unique(a), Ty::Unique(b)) => self.compatible(a, b, line),
            (Ty::Shared(a), Ty::Shared(b)) => self.compatible(a, b, line),
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
        if self.work.fresh >= 8192 {
            return Err("symbolic value expansion limit reached (8192)".into());
        }
        let name = self.fresh_name();
        match t {
            Ty::Union(members) => self.arbitrary_union(members),
            Ty::Shape(inner) => Ok(Symbol::Shape(inner.clone())),
            Ty::Type => Err("type observations have no arbitrary runtime values".into()),
            Ty::Machine(t) => {
                let n = Linear::variable(name);
                let (lo, hi) = t.bounds();
                self.assume_from(
                    &Formula::Ge(n.sub(&Linear::number(lo))?),
                    paths::Origin::Unresolved,
                )?;
                self.assume_from(
                    &Formula::Ge(Linear::number(hi).sub(&n)?),
                    paths::Origin::Unresolved,
                )?;
                Ok(Symbol::Number(Ty::Machine(*t), n))
            }
            Ty::Unit => Ok(Symbol::Unit),
            Ty::Shared(t) => self.arbitrary_owner(t),
            Ty::Unique(t) => {
                if let Ty::Array(element, length) = t.as_ref() {
                    let syntax = heap::syntax_type(element, 0)?;
                    let stride =
                        crate::compiler::layout::of(&syntax, self.declarations.structs)?.size;
                    self.assume(&Formula::Ge(
                        Linear::number(
                            (crate::compiler::layout::MAX_ALLOCATION_BYTES / stride as u64) as i128,
                        )
                        .sub(length)?,
                    ))?;
                }
                let value = self.arbitrary(t)?;
                let plane = self.allocate_symbol(value)?;
                Ok(Symbol::Unique(
                    t.clone(),
                    self.storage.memory.borrow(plane)?,
                ))
            }
            Ty::Ref(t) => {
                let v = self.arbitrary(t)?;
                let id = self.allocate_symbol(v)?;
                Ok(Symbol::Ref(
                    t.clone(),
                    self.storage.memory.borrow(id)?,
                    vec![],
                ))
            }
            Ty::Int => Ok(Symbol::Number(Ty::Int, Linear::variable(name))),
            Ty::Nat => {
                let n = Linear::variable(name);
                self.assume_from(&Formula::Ge(n.clone()), paths::Origin::Unresolved)?;
                Ok(Symbol::Number(Ty::Nat, n))
            }
            Ty::Bool => {
                let n = Linear::variable(name);
                self.assume_from(&Formula::Ge(n.clone()), paths::Origin::Unresolved)?;
                self.assume_from(
                    &Formula::Ge(Linear::number(1).sub(&n)?),
                    paths::Origin::Unresolved,
                )?;
                let predicate = equal(&n, &Linear::number(1))?;
                self.charge_value_work(
                    predicate
                        .storage_weight()?
                        .saturating_add(n.terms.len() + 1),
                )?;
                self.arrays.boolean_words.insert(predicate.clone(), n);
                Ok(Symbol::Bool(predicate))
            }
            Ty::Array(element, len) => {
                self.arrays.inputs.insert(name.clone());
                Ok(Symbol::Array {
                    element: element.clone(),
                    len: len.clone(),
                    items: None,
                    cells: BTreeMap::new(),
                    identity: name,
                })
            }
            Ty::Record(name) => {
                let def = self
                    .declarations
                    .structs
                    .get(name)
                    .ok_or("unknown struct")?;
                let saved = std::mem::take(&mut self.locals.values);
                let saved_roots = std::mem::take(&mut self.locals.places);
                let saved_facts = std::mem::take(&mut self.proof.facts);
                let saved_module = std::mem::replace(&mut self.locals.module, def.module.clone());
                self.proof.facts = def.facts.iter().cloned().collect();
                self.locals.places.clear();
                self.locals.values.clear();
                let mut fields = BTreeMap::new();
                for (n, t) in &def.fields {
                    let phase = self.execution.phase;
                    if def.ideal_fields.contains(n) && self.execution.phase == Phase::Runtime {
                        self.execution.phase = Phase::Ideal;
                    }
                    let t = self.resolve(t)?;
                    let v = self.arbitrary(&t)?;
                    self.execution.phase = phase;
                    fields.insert(n.clone(), v.clone());
                    self.locals.values.insert(n.clone(), v);
                }
                let value = Symbol::Record(name.clone(), fields);
                self.locals.values.insert("self".into(), value.clone());
                if let Some(p) = &def.invariant {
                    self.assume_declared_invariant(p)?;
                }
                self.locals.values = saved;
                self.locals.places = saved_roots;
                self.proof.facts = saved_facts;
                self.locals.module = saved_module;
                Ok(value)
            }
        }
    }

    fn statement(&mut self, s: &Statement) -> Result<()> {
        let start = self.storage.temporaries.len();
        self.statement_inner(s)?;
        self.finish_temporaries(start)?;
        self.proof.states.push(self.proof.subjects.snapshot());
        Ok(())
    }

    fn finish_temporaries(&mut self, start: usize) -> Result<()> {
        for (value, line) in self.storage.temporaries.split_off(start).into_iter().rev() {
            self.validate_argument(&value, line)
                .map_err(|e| format!("line {line}: implicit temporary cleanup: {e}"))?;
            self.cleanup_value(value, line)?;
        }
        Ok(())
    }

    fn scoped_eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let start = self.storage.temporaries.len();
        let value = self.eval(e, expected)?;
        self.finish_temporaries(start)?;
        Ok(value)
    }

    fn statement_inner(&mut self, s: &Statement) -> Result<()> {
        match s {
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                line,
            } => self.check_while(loops::Loop {
                condition,
                invariant,
                modifies,
                decreases: decreases.as_ref(),
                body,
                line: *line,
            }),
            Statement::Ideal(binding) => {
                if let Statement::Assign { target, .. } = binding.as_ref() {
                    fn erased(context: &Context<'_>, expression: &Expr) -> bool {
                        match &expression.kind {
                            Kind::Name(name) => {
                                context.execution.ideal_execution
                                    || context.locals.ideal_bindings.contains(name)
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
                                    || matches!(context.hint(base), Some(Ty::Record(name)) if context.declarations.structs[&name].ideal_fields.contains(field))
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
                let phase = std::mem::replace(&mut self.execution.phase, Phase::Ideal);
                let result = self.statement(binding);
                self.execution.phase = phase;
                result?;
                self.locals
                    .ideal_bindings
                    .extend(binding.bindings().into_iter().map(str::to_owned));
                Ok(())
            }
            Statement::Destructure {
                record,
                arguments,
                fields,
                value,
            } => {
                if !arguments.is_empty() {
                    return Err("generic record pattern requires specialization".into());
                }
                self.representation_access(record, value.line)?;
                let def = self
                    .declarations
                    .structs
                    .get(record)
                    .ok_or_else(|| format!("line {}: unknown record {record}", value.line))?;
                let drop_receiver = self.execution.dropping
                    && self.execution.phase == Phase::Runtime
                    && matches!(&value.kind, Kind::Name(name) if name == "self")
                    && self
                        .declarations
                        .destructors
                        .get(record)
                        .is_some_and(|method| {
                            self.execution.current.as_ref() == Some(&method.name)
                        });
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
                let evaluated = if drop_receiver {
                    self.take_drop_receiver(record, value)?
                } else {
                    self.eval(value, Some(&Ty::Record(record.clone())))?
                };
                let Symbol::Record(_, mut values) = evaluated else {
                    return Err("record pattern requires a record".into());
                };
                for (field, name) in fields {
                    let v = values.remove(field).ok_or("missing pattern field")?;
                    if def.ideal_fields.contains(field) {
                        self.locals.ideal_bindings.insert(name.clone());
                    }
                    self.locals.values.insert(name.clone(), v);
                }
                Ok(())
            }
            Statement::Update {
                places,
                lifts,
                body,
                line,
            } => self.update(places, lifts, body, *line),
            Statement::Assign {
                target,
                value,
                starts,
            } => self.assign_starting_owners(target, value, starts),
            Statement::Effect(e) => {
                let start = self.proof.results.len();
                let value = self.eval(e, None)?;
                if self.symbol_is_move_only(&value) {
                    self.validate_argument(&value, e.line)?;
                }
                self.cleanup_value(value, e.line)?;
                self.proof.results.truncate(start);
                Ok(())
            }
            Statement::Let { name, ty, value } => {
                self.fresh_binding(name, value.line)?;
                let ty = ty.as_ref().map(|t| self.resolve(t)).transpose()?;
                let start = self.proof.results.len();
                let v = self.eval(value, ty.as_ref())?;
                self.locals.values.insert(name.clone(), v.clone());
                self.bind_call_evidence(name, &v, start, value.line)?;
                Ok(())
            }
            Statement::Fact { name, value } => {
                self.fresh_binding(name, value.line)?;
                self.proposition(value)?; // Well-formedness only; NOT a proof or an assumption.
                self.proof.facts.insert(name.clone(), value.clone());
                Ok(())
            }
            Statement::Proof {
                name,
                proposition,
                steps,
            } => {
                if name != "_" {
                    self.fresh_binding(name, proposition.line)?;
                }
                let mut subjects = self.claim_subjects(proposition)?;
                let p = self.proposition(proposition)?;
                if !subjects.complete {
                    // Specifications cannot mutate source storage. A first
                    // observation may have materialized a deferred input port;
                    // capture that existing identity without re-evaluation.
                    subjects = self.claim_subjects(proposition)?;
                }
                debug_assert!(
                    !subjects.complete
                        || self
                            .proof
                            .subjects
                            .current(&subjects, &self.storage.memory)?
                );
                let label = if name == "_" {
                    "anonymous proof".into()
                } else {
                    format!("proof {name}")
                };
                let evidence =
                    self.proof_script_for(&p, &label, proposition.line, steps, Some(&subjects))?;
                if !p.is_arithmetic() {
                    // Logical theorems remain state-indexed candidates. They
                    // cannot become arithmetic assumptions without elimination.
                    self.publish_evidence(evidence, subjects)?;
                    self.proof.claims.insert(evidence);
                } else {
                    self.publish_evidence(evidence, subjects)?;
                    let dependencies = self.evidence_dependencies(evidence)?;
                    if dependencies.admissions.is_empty() {
                        self.assume_from(&p, paths::Origin::Evidence(evidence))?;
                    } else {
                        self.proof.claims.insert(evidence);
                    }
                }
                if name != "_" {
                    self.proof.witnesses.insert(name.clone(), evidence);
                }
                Ok(())
            }
        }
    }

    fn fresh_binding(&self, name: &str, line: usize) -> Result<()> {
        if self.locals.values.contains_key(name)
            || self.proof.facts.contains_key(name)
            || self.proof.witnesses.contains_key(name)
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

    fn location(&mut self, e: &Expr) -> Result<(Reference, Vec<Projection<Linear>>)> {
        match &e.kind {
            Kind::Name(n) => {
                self.runtime_name(n)?;
                let id = if let Some(id) = self.locals.places.get(n) {
                    *id
                } else {
                    let v = self
                        .locals
                        .values
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown place {n}"))?;
                    let id = self.allocate_symbol(v)?;
                    self.locals.places.insert(n.clone(), id);
                    id
                };
                Ok((self.storage.memory.borrow(id)?, vec![]))
            }
            Kind::Field(..) | Kind::Index(..) => {
                let value = self.place_reference(e)?;
                self.direct_reference(&value)
            }
            Kind::Unary(op, _) if op == "*" => {
                let value = self.place_reference(e)?;
                self.direct_reference(&value)
            }
            Kind::Bytes(_) | Kind::Record(..) | Kind::Call(..) | Kind::If(..) | Kind::Block(..)
                if self.execution.phase == Phase::Runtime =>
            {
                let value = self.eval(e, None)?;
                if !matches!(value, Symbol::Record(..)) && !matches!(e.kind, Kind::Bytes(_)) {
                    return Err("temporary borrows require a record value".into());
                }
                let ty = value.ty();
                let plane = self.allocate_symbol(value)?;
                let reference = self.storage.memory.borrow(plane)?;
                // Own the temporary slot until this statement finishes. Taking
                // it during cleanup invalidates every loan into that slot.
                self.storage
                    .temporaries
                    .push((Symbol::Unique(Box::new(ty), reference), e.line));
                Ok((reference, Vec::new()))
            }
            _ => Err(format!("line {}: expected a referenceable place", e.line)),
        }
    }

    fn declared_hint(t: &Type) -> Option<Ty> {
        match t {
            Type::Apply(..) => None,
            Type::Int => Some(Ty::Int),
            Type::Nat => Some(Ty::Nat),
            Type::Bool => Some(Ty::Bool),
            Type::Unit => Some(Ty::Unit),
            Type::Machine(t) => Some(Ty::Machine(*t)),
            Type::Named(n) => Some(Ty::Record(n.clone())),
            Type::Ref(t) => Self::declared_hint(t).map(|t| Ty::Ref(Box::new(t))),
            Type::Unique(t) => Self::declared_hint(t).map(|t| Ty::Unique(Box::new(t))),
            Type::Shared(t) => Self::declared_hint(t).map(|t| Ty::Shared(Box::new(t))),
            Type::Array(element, count) => Some(Ty::Array(
                Box::new(Self::declared_hint(element)?),
                Linear::number(crate::compiler::layout::array_length(count).ok()? as i128),
            )),
            Type::Union(members) => {
                let mut members = members
                    .iter()
                    .map(Self::declared_hint)
                    .collect::<Option<Vec<_>>>()?;
                members.sort();
                Some(Ty::Union(members))
            }
            Type::Shape(inner) => Self::declared_hint(inner).map(|ty| Ty::Shape(Box::new(ty))),
        }
    }

    // Read types from already modeled storage without evaluation or proof
    // assumptions. This includes arrays behind record fields and references;
    // dependent extents cannot be reconstructed from a field declaration alone.
    fn stored_hint(&self, expression: &Expr) -> Option<&Symbol> {
        match &expression.kind {
            Kind::Name(name) => {
                if let Some(plane) = self.locals.places.get(name) {
                    self.storage.memory.get(*plane).ok()
                } else {
                    self.locals.values.get(name)
                }
            }
            Kind::Field(base, field) => match self.stored_hint(base)? {
                Symbol::Record(_, fields) => fields.get(field),
                _ => None,
            },
            Kind::Unary(op, base) if op == "*" => match self.stored_hint(base)? {
                Symbol::Ref(_, reference, path) => {
                    project(self.storage.memory.read(*reference).ok()?, path).ok()
                }
                Symbol::Unique(_, reference) => self.storage.memory.read(*reference).ok(),
                Symbol::Shared(_, owner) => self
                    .storage
                    .memory
                    .borrow_owned(*owner)
                    .ok()
                    .and_then(|reference| self.storage.memory.read(reference).ok()),
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
            Kind::Forall { .. } => Some(Ty::Bool),
            Kind::Bytes(bytes) => Self::declared_hint(&Type::bytes(bytes.len(), e.line)),
            Kind::Type(_) => Some(Ty::Type),
            Kind::Call(name, _) if matches!(name.as_str(), "size_of" | "align_of") => {
                Some(Ty::Machine(MachineInt::parse("usize").unwrap()))
            }
            Kind::Call(name, _) if name == "typeof" => Some(Ty::Type),
            Kind::Call(name, args) if name == "shape" && args.len() == 1 => self
                .type_literal(&args[0])
                .map(|ty| Ty::Shape(Box::new(ty))),
            Kind::Bool(_) => Some(Ty::Bool),
            Kind::Call(name, args) if name == "old" && args.len() == 1 => Self::old_key(&args[0])
                .and_then(|key| self.entry.values.get(&key).map(Symbol::ty))
                .or_else(|| self.hint(&args[0])),
            Kind::Call(name, _) if MachineInt::parse(name).is_some() => {
                MachineInt::parse(name).map(Ty::Machine)
            }
            Kind::Call(name, _) if name == "nat" => Some(Ty::Nat),
            Kind::Call(name, _) if name == "owner_count" => Some(Ty::Nat),
            Kind::Call(name, _) if name == "integer" => Some(Ty::Int),
            Kind::Call(name, args) if name == "alloc" && args.len() == 1 => {
                self.hint(&args[0]).map(|t| Ty::Unique(Box::new(t)))
            }
            Kind::Constant(t, _) => Some(Ty::Machine(*t)),
            Kind::Name(n) => self.locals.values.get(n).map(Symbol::ty),
            Kind::Record(n, _) => Some(Ty::Record(n.clone())),
            Kind::Unary(op, x) if op == "&" => self.hint(x).map(|t| Ty::Ref(Box::new(t))),
            Kind::Unary(op, x) if op == "*" => {
                let pointer = self.hint(x)?;
                match pointer.pointer_member()? {
                    Ty::Ref(t) | Ty::Unique(t) | Ty::Shared(t) => Some(*t.clone()),
                    _ => None,
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
                self.declarations
                    .structs
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
            Kind::Block(_, tail) => self.hint(tail),
            Kind::Call(n, _) => self
                .declarations
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
        self.prove_with_subjects(goal, label, line, steps, None)
    }

    fn prove_with_subjects(
        &mut self,
        goal: &Formula,
        label: &str,
        line: usize,
        steps: Option<&[String]>,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<()> {
        if let Some(steps) = steps {
            self.session.clear_diagnostic();
            let node = self
                .proof_script_for(goal, label, line, steps, subjects)
                .inspect_err(|error| {
                    self.session
                        .note_obligation(error, diagnostics::obligation(goal));
                })?;
            self.session.clear_diagnostic();
            self.proof.uses.push(node);
        } else {
            self.prove_subjects(goal, subjects, label, line)?;
        }
        Ok(())
    }

    fn eval(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        if self.work.eval_depth >= 32 || self.work.eval_steps >= 100_000 {
            return Err(format!(
                "line {}: verification evaluation limit reached",
                e.line
            ));
        }
        self.work.eval_depth += 1;
        self.work.eval_steps += 1;
        let result = self.eval_checked(e, expected);
        self.work.eval_depth -= 1;
        result
    }

    fn eval_checked(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let array_member = match (&e.kind, expected) {
            (Kind::Array(items), Some(Ty::Union(members))) => {
                let mut arrays = members.iter().filter(|ty| matches!(ty, Ty::Array(_, length) if length.terms.is_empty() && length.constant == items.len() as i128));
                let first = arrays.next();
                if arrays.next().is_none() {
                    first
                } else {
                    None
                }
            }
            _ => None,
        };
        let moving_member = self.execution.phase == Phase::Runtime
            && expected.is_some_and(|ty| self.ty_is_move_only(ty) && self.union_move_place(e, ty));
        let evaluated = if moving_member {
            self.move_union_member(e, expected.unwrap())
        } else {
            self.eval_inner(e, array_member.or(expected))
        };
        let value = evaluated.map_err(|s| {
            if s.starts_with("line ") {
                s
            } else {
                format!("line {}: {s}", e.line)
            }
        })?;
        let projecting_owner = matches!(&e.kind, Kind::Field(..) | Kind::Index(..))
            || matches!(&e.kind, Kind::Unary(op, _) if op == "*");
        if self.execution.phase != Phase::Specification
            && self.symbol_is_move_only(&value)
            && projecting_owner
            && !moving_member
        {
            return Err(format!("line {}: moving owning fields or borrowed values needs partial-initialization tracking; unsupported", e.line));
        }
        let value = self.coerce_pointer(value, expected, e.line)?;
        let value = self.union_coercion(value, expected, e.line, Some(e))?;
        self.charge_value_work(symbol_weight(&value)?)
            .map_err(|error| format!("line {}: {error}", e.line))?;
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
                "machine integer upper bound",
                e.line,
            )?;
        }
        Ok(value)
    }

    fn symbol_is_move_only(&self, value: &Symbol) -> bool {
        match value {
            Symbol::Union { .. } | Symbol::Shape(_) => true,
            Symbol::Unique(..) => true,
            Symbol::Shared(..) => self.ty_is_move_only(&value.ty()),
            Symbol::Record(n, _) => is_move_only(
                &Type::Named(n.clone()),
                self.declarations.structs,
                self.declarations.drops,
            ),
            Symbol::Array { element, .. } => self.ty_is_move_only(element),
            Symbol::Number(Ty::Machine(integer), _) => self.ty_is_move_only(&Ty::Machine(*integer)),
            Symbol::Bool(_) => self.ty_is_move_only(&Ty::Bool),
            Symbol::Unit => self.ty_is_move_only(&Ty::Unit),
            Symbol::Ref(inner, _, _) | Symbol::RefCases(inner, _) => {
                self.ty_is_move_only(&Ty::Ref(inner.clone()))
            }
            _ => false,
        }
    }

    fn ty_is_move_only(&self, t: &Ty) -> bool {
        match t {
            Ty::Union(_) | Ty::Shape(_) => true,
            Ty::Unique(_) => true,
            Ty::Shared(_) => !crate::shared::target::native()
                .is_ok_and(|target| target.is_copy(&Type::Shared(Box::new(Type::Unit)))),
            Ty::Record(n) => is_move_only(
                &Type::Named(n.clone()),
                self.declarations.structs,
                self.declarations.drops,
            ),
            Ty::Array(t, _) => self.ty_is_move_only(t),
            Ty::Machine(integer) => !crate::shared::target::native()
                .is_ok_and(|target| target.is_copy(&Type::Machine(*integer))),
            Ty::Bool => {
                !crate::shared::target::native().is_ok_and(|target| target.is_copy(&Type::Bool))
            }
            Ty::Unit => {
                !crate::shared::target::native().is_ok_and(|target| target.is_copy(&Type::Unit))
            }
            Ty::Ref(_) => !crate::shared::target::native()
                .is_ok_and(|target| target.is_copy(&Type::Ref(Box::new(Type::Unit)))),
            _ => false,
        }
    }

    // Extensional array histories can compare these values structurally.
    // Reference identity, nested arrays, and owning values need their own rules.
    // Reference-free scalar trees can be havoced without changing storage
    // identity, layouts, or hidden reference provenance. Copy permission is a separate
    // condition: history views do not copy source values or grant moves. Only
    // reference-free trees without runtime cleanup can use structural histories.
    fn scalar_field_value(&self, t: &Ty) -> bool {
        fn fields(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
            match t {
                Type::Named(name) => structs.get(name).is_some_and(|definition| {
                    definition.fields.iter().all(|(_, ty)| fields(ty, structs))
                }),
                Type::Ref(_) | Type::Unique(_) | Type::Shared(_) | Type::Array(..) => false,
                _ => true,
            }
        }
        match t {
            Ty::Union(_) | Ty::Shape(_) | Ty::Type => false,
            Ty::Record(name) => fields(&Type::Named(name.clone()), self.declarations.structs),
            Ty::Ref(_) | Ty::Unique(_) | Ty::Shared(_) | Ty::Array(..) => false,
            _ => true,
        }
    }

    fn history_element(&self, t: &Ty) -> bool {
        !self.has_runtime_cleanup(t) && self.scalar_field_value(t)
    }

    fn ty_has_reference(&self, t: &Ty) -> bool {
        match t {
            Ty::Ref(_) | Ty::Unique(_) | Ty::Shared(_) => true,
            Ty::Union(members) => members.iter().any(|ty| self.ty_has_reference(ty)),
            Ty::Array(element, _) => self.ty_has_reference(element),
            Ty::Record(name) => {
                type_has_reference(&Type::Named(name.clone()), self.declarations.structs)
            }
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
            if self.proof.paths.iter().any(|path| !path.contains(&bound)) {
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
                .declarations
                .structs
                .get(name)
                .cloned()
                .ok_or("unknown array element type")?;
            if let Some(invariant) = definition.invariant {
                let saved_module =
                    std::mem::replace(&mut self.locals.module, definition.module.clone());
                let env = std::mem::replace(&mut self.locals.values, fields.clone());
                let roots = std::mem::take(&mut self.locals.places);
                let facts = std::mem::replace(
                    &mut self.proof.facts,
                    definition.facts.into_iter().collect(),
                );
                self.locals.values.insert("self".into(), value.clone());
                self.assume_declared_invariant(&invariant)?;
                self.locals.values = env;
                self.locals.places = roots;
                self.proof.facts = facts;
                self.locals.module = saved_module;
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
        let origin = if matches!(element, Ty::Union(_)) || self.ty_has_reference(element) {
            self.array_input_origin(identity)?
        } else {
            None
        };
        let canonical;
        let index = if let Some(origin) = &origin {
            canonical = self.input_array_index(origin, index)?;
            &canonical
        } else {
            index
        };
        if matches!(
            self.arrays.history.get(identity),
            Some(ArrayHistory::Uninitialized(_))
        ) {
            return self.read_uninitialized_array(identity, index, cells);
        }
        if origin.is_some() {
            let value = if let Some(value) = cells.get(index) {
                self.charge_value_work(symbol_weight(value)?)?;
                value.clone()
            } else {
                self.read_resource_version(element, identity, index)?
            };
            self.observe_input_slot_types(identity, index, &value)?;
            return Ok(value);
        }
        if self.ty_has_reference(element) {
            if let Some(index) = constant_index(index) {
                if let Some(value) = items.and_then(|items| items.get(index)) {
                    return Ok(value.clone());
                }
            }
            if let Some(value) = cells.get(index) {
                return Ok(value.clone());
            }
            return self.input_array_port(element, identity, index);
        }
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
                if let Some(existing) = self.arrays.reads.get(&key).cloned() {
                    if existing != value {
                        self.assume(&self.symbol_equal(&existing, &value)?)?;
                    }
                } else {
                    self.arrays.reads.insert(key, value);
                }
            }
        }
        self.array_read(element, identity, index)
    }

    fn array_read(&mut self, element: &Ty, identity: &str, index: &Linear) -> Result<Symbol> {
        self.charge_value_work(1)?;
        if self.arrays.read_depth >= 64 {
            return Err("array history read depth limit reached (64)".into());
        }
        self.arrays.read_depth += 1;
        let result = (|| {
            let value = self.array_read_value(element, identity, index)?;
            self.replay_array_history(element, identity, index, &value)?;
            self.observe_array_values(identity, index, &value)?;
            Ok(value)
        })();
        self.arrays.read_depth -= 1;
        result
    }

    fn array_read_value(&mut self, element: &Ty, identity: &str, index: &Linear) -> Result<Symbol> {
        // Stable contents identities give extensional reads across scopes. A
        // reference-bearing selection needs an alias rule, not a fresh plane.
        if self.ty_has_reference(element) {
            return Err("symbolic reads of reference-containing array elements need an alias contract; unsupported".into());
        }
        let key = (identity.to_owned(), index.clone());
        if let Some(value) = self.arrays.reads.get(&key).cloned() {
            // Replay type facts, never facts specific to the first read's path.
            self.assume_history_type(&value, !self.arrays.history.contains_key(identity))?;
            return Ok(value);
        }
        let value = if self.history_element(element) {
            let value = self.history_value(element)?;
            self.assume_history_type(&value, !self.arrays.history.contains_key(identity))?;
            value
        } else {
            self.arbitrary(element)?
        };
        if self.history_element(element) {
            let observations = self
                .arrays
                .reads
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
        self.bind_scalar_array_read(identity, index, &value)?;
        self.arrays.reads.insert(key, value.clone());
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
                if let Some(id) = self.locals.places.get(n) {
                    self.storage.memory.get(*id).cloned()
                } else {
                    self.locals
                        .values
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown storage place {n}"))
                }
            }
            Kind::Field(base, name) => {
                if places::through_pointer(e) {
                    let reference = self.place_reference(e)?;
                    return self.read_reference(&reference, e.line);
                }
                let Symbol::Record(typename, fields) = self.storage(base)? else {
                    return Err("field access requires struct storage".into());
                };
                self.field_access(&typename, name, e.line)?;
                fields
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown field {name}"))
            }
            Kind::Unary(op, pointer) if op == "*" => self.dereference(pointer, e.line),
            Kind::Index(base, index) => {
                // Pure local reads can use the immutable array model without
                // materializing nested places. Effects and pointer paths must
                // observe storage after evaluating the complete index path.
                if e.stored_place() && (places::through_pointer(e) || !e.pure_read()) {
                    let reference = self.place_reference(e)?;
                    return self.read_reference(&reference, e.line);
                }
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
                if self.execution.phase != Phase::Specification
                    && (self.symbol_is_move_only(&value) || self.contains_shared(&value))
                {
                    self.storage.temporaries.push((value.clone(), e.line));
                }
                Ok(value)
            }
        }
    }

    fn fact_at(&mut self, place: &Expr, fact: &str, line: usize) -> Result<Formula> {
        if self.execution.phase != Phase::Specification {
            return Err(format!(
                "line {line}: named type facts are propositions, not runtime values"
            ));
        }
        let value = self.storage(place)?;
        let Symbol::Record(typename, fields) = &value else {
            return Err("type facts require struct storage".into());
        };
        let def = self
            .declarations
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
        let roots = self.locals.places.clone();
        let facts = self.proof.facts.clone();
        self.locals.values = fields.clone();
        self.locals.values.insert("self".into(), value);
        self.locals.places.clear();
        self.proof.facts = def.facts.iter().cloned().collect();
        let saved_module = std::mem::replace(&mut self.locals.module, def.module.clone());
        let result = self.proposition(&expression);
        self.locals.module = saved_module;
        self.locals.values = saved;
        self.locals.places = roots;
        self.proof.facts = facts;
        result
    }

    fn eval_inner(&mut self, e: &Expr, expected: Option<&Ty>) -> Result<Symbol> {
        let shadowed = matches!(&e.kind, Kind::Name(name) if self.locals.values.contains_key(name) || self.proof.facts.contains_key(name) || self.proof.witnesses.contains_key(name));
        if expected == Some(&Ty::Type) && self.execution.phase != Phase::Runtime && !shadowed {
            if let Some(ty) = self.type_literal(e) {
                return Ok(Symbol::Type {
                    members: vec![ty],
                    active: Linear::number(0),
                });
            }
        }
        match &e.kind {
            Kind::Binary(_, _, _)
                if self.locals.quantified_evaluation != 0 && array_values::parts(e).is_some() =>
            {
                self.eval_indexed_value_equality(e)
            }
            Kind::Binary(_, _, _)
                if self
                    .locals
                    .logical_bindings
                    .iter()
                    .any(|binding| binding.quantified)
                    && array_predicates::indexed_type_parts(e).is_some() =>
            {
                self.eval_indexed_type_predicate(e)
            }
            Kind::Forall {
                variable,
                domain,
                body,
            } => self.eval_quantified(variable, domain, body, e.line),
            Kind::Type(ty) if self.execution.phase != Phase::Runtime => Ok(Symbol::Type {
                members: vec![self.resolve(ty)?],
                active: Linear::number(0),
            }),
            Kind::Type(_) => Err("type values are ideal; they have no runtime storage".into()),
            Kind::Generic { .. } => {
                Err("generic expression requires specialization before verification".into())
            }
            Kind::Bytes(bytes) => self.byte_literal(bytes),
            Kind::FactAt(place, name) => Ok(Symbol::Bool(self.fact_at(place, name, e.line)?)),
            Kind::Unit => Ok(Symbol::Unit),
            Kind::Constant(t, n) => Ok(Symbol::Number(Ty::Machine(*t), Linear::number(*n))),
            Kind::Number(n) => Ok(Symbol::Number(
                match Self::union_literal_hint(expected).as_ref() {
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
                if !self.locals.values.contains_key(n) {
                    if let Some(definition) = self.proof.facts.get(n).cloned() {
                        if self.execution.phase != Phase::Specification {
                            return Err(format!(
                                "fact {n} is a proof-only proposition, not a runtime boolean"
                            ));
                        }
                        return self.eval(&definition, Some(&Ty::Bool));
                    }
                    if self.proof.witnesses.contains_key(n) {
                        return Err(format!("{n} is a proof witness; reference it with exact"));
                    }
                    if self.execution.phase != Phase::Runtime {
                        if let Some(ty) = self.type_literal(e) {
                            return Ok(Symbol::Type {
                                members: vec![ty],
                                active: Linear::number(0),
                            });
                        }
                    }
                }

                let value = if let Some(id) = self.locals.places.get(n) {
                    self.storage.memory.get(*id).cloned()
                } else {
                    self.locals
                        .values
                        .get(n)
                        .cloned()
                        .ok_or_else(|| format!("unknown value {n}"))
                }?;
                let moving = self.symbol_is_move_only(&value);
                let selected = if moving {
                    self.union_coercion(value.clone(), expected, e.line, Some(e))?
                } else {
                    // Copy before injecting into a move-only union. Injection
                    // must not suppress the source value's pointer claims.
                    let value = self.copy_pointer_read(value.clone(), e.line)?;
                    self.union_coercion(value, expected, e.line, Some(e))?
                };
                if self.execution.phase != Phase::Specification && self.symbol_is_move_only(&value)
                {
                    if self.execution.phase == Phase::Ideal
                        && !self.execution.ideal_execution
                        && !self.locals.ideal_bindings.contains(n)
                        && !self.erased_value(&value)
                    {
                        return Err("ideal execution cannot consume runtime ownership; use a read-only proof view".into());
                    }
                    if self.execution.phase == Phase::Runtime
                        && !self.storage.opened_planes.is_empty()
                    {
                        return Err(
                            "runtime ownership moves are forbidden while invariants are open"
                                .into(),
                        );
                    }
                    if self.execution.dropping && n == "self" {
                        return Err(
                            "a destructor must use a complete pattern to consume self".into()
                        );
                    }
                    let (r, _) = self.location(e)?;
                    let id = self.storage.memory.plane(r)?;
                    self.take_symbol(id)?;
                }
                Ok(selected)
            }
            Kind::Field(..) | Kind::Index(..) => {
                let value = self.storage(e)?;
                let value = self.select_projected_member(value, expected, e)?;
                self.copy_pointer_read(value, e.line)
            }
            Kind::Record(name, entries) => {
                self.representation_access(name, e.line)?;
                if self.execution.phase == Phase::Ideal
                    && is_move_only(
                        &Type::Named(name.clone()),
                        self.declarations.structs,
                        self.declarations.drops,
                    )
                    && !erased_type(&Type::Named(name.clone()), self.declarations.structs)
                {
                    return Err("ideal execution cannot construct runtime ownership".into());
                }
                let def = self
                    .declarations
                    .structs
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown struct {name}"))?;
                if def.ideal && self.execution.phase == Phase::Runtime {
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
                        _ => Self::declared_hint(ty),
                    };
                    let saved_phase = self.execution.phase;
                    if def.ideal_fields.contains(n) && self.execution.phase == Phase::Runtime {
                        self.execution.phase = Phase::Ideal;
                    }
                    let evaluated = if let Type::Array(element, _) = ty {
                        // Supply the element type now; the complete dependent
                        // field type is checked once all literal fields exist.
                        let element = self.resolve(element)?;
                        self.eval_inner(
                            value,
                            Some(&Ty::Array(Box::new(element), Linear::number(0))),
                        )?
                    } else if matches!(ty, Type::Unique(_) | Type::Union(_) | Type::Shape(_)) {
                        // Dependent field types refer to preceding record fields,
                        // while initializer expressions still use the caller's scope.
                        let caller = self.clone_env()?;
                        let caller_roots = std::mem::take(&mut self.locals.places);
                        self.locals.values = fields.clone();
                        let resolved = self.resolve(ty);
                        self.locals.values = caller;
                        self.locals.places = caller_roots;
                        self.eval(value, Some(&resolved?))?
                    } else {
                        self.eval(value, hint.as_ref())?
                    };
                    self.execution.phase = saved_phase;
                    fields.insert(n.clone(), evaluated);
                }
                self.locals.values = saved;
                let record = Symbol::Record(name.clone(), fields);
                self.record_valid(&record, e.line)?;
                Ok(record)
            }
            Kind::Unary(op, place) if op == "&" => {
                let borrowed = self.place_reference(place)?;
                self.validate_argument(&borrowed, e.line)?;
                Ok(borrowed)
            }
            Kind::Unary(op, pointer) if op == "*" => {
                let value = self.dereference(pointer, e.line)?;
                let value = self.select_projected_member(value, expected, e)?;
                self.copy_pointer_read(value, e.line)
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
                if matches!(ty, Ty::Machine(_)) && !matches!(x.kind, Kind::Number(_)) {
                    self.machine_arithmetic(&ty, n.scale(-1).ok())
                } else {
                    Ok(Symbol::Number(ty, n.scale(-1)?))
                }
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
                let ty = if matches!(op.as_str(), "==" | "!=")
                    && (self.hint(a) == Some(Ty::Type) || self.hint(b) == Some(Ty::Type))
                {
                    Some(Ty::Type)
                } else if matches!(op.as_str(), "+" | "-" | "*") {
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
                if ty == Ty::Type && matches!(op.as_str(), "==" | "!=") {
                    let a = self.eval(a, Some(&Ty::Type))?;
                    let b = self.eval(b, Some(&Ty::Type))?;
                    let same = unions::observations_equal(&a, &b)?;
                    return Ok(Symbol::Bool(if op == "==" { same } else { same.not() }));
                }
                if !matches!(ty, Ty::Int | Ty::Nat | Ty::Machine(_)) {
                    return Err("arithmetic and comparisons require integer operands".into());
                }
                let a = self.eval(a, Some(&ty))?.number()?;
                let b = self.eval(b, Some(&ty))?.number()?;
                if matches!(ty, Ty::Machine(_)) && matches!(op.as_str(), "+" | "-" | "*") {
                    let exact = match op.as_str() {
                        "+" => a.add(&b).ok(),
                        "-" => a.sub(&b).ok(),
                        "*" if a.terms.is_empty() => b.scale(a.constant).ok(),
                        "*" if b.terms.is_empty() => a.scale(b.constant).ok(),
                        _ => None,
                    };
                    return self.machine_arithmetic(&ty, exact);
                }
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
            Kind::Call(name, args) => self.eval_call(name, args, expected, e.line),
            Kind::If(condition, yes, no) => self.eval_conditional(e, condition, yes, no, expected),
            Kind::Block(body, tail) => self.eval_block(body, tail, expected, e.line),
        }
    }
}

#[derive(Debug)]
pub struct VerifiedProgram {
    pub(crate) functions: Vec<Function>,
    pub(crate) structs: BTreeMap<String, Struct>,
    pub obligations: usize,
    pub(crate) drops: BTreeSet<String>,
    trusted: Vec<crate::compiler::certificate::TrustedAssumption>,
    summaries: BTreeMap<String, summaries::Summary>,
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

    /// Known admissions supporting the function's checked runtime obligations.
    /// Aggregate value provenance and frontend state imports remain incomplete.
    pub fn function_safety_assumptions(
        &self,
        name: &str,
    ) -> Option<impl Iterator<Item = &crate::compiler::certificate::TrustedAssumption>> {
        self.summaries
            .get(name)
            .map(|summary| summary.safety.iter().map(|id| &self.trusted[id.index()]))
    }

    /// Known admissions supporting the advertised result, including safety.
    pub fn function_contract_assumptions(
        &self,
        name: &str,
    ) -> Option<impl Iterator<Item = &crate::compiler::certificate::TrustedAssumption>> {
        self.summaries
            .get(name)
            .map(|summary| summary.contract.iter().map(|id| &self.trusted[id.index()]))
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
                Declarations {
                    functions: &functions,
                    summaries: &self.summaries,
                    structs: &self.structs,
                    drops: &self.drops,
                    destructors: &destructors,
                    helpers: &helpers,
                    cleanup_helpers: &helpers,
                },
                &mut session,
            );
            ctx.execution.current = Some("main".into());
            ctx.capture_old(main)?;
            let p = ctx.proposition(pre)?;
            ctx.prove(&p, "entry precondition of main", pre.line)?;
        }
        Ok(())
    }
}

pub fn verify(source: &str) -> Result<VerifiedProgram> {
    verify_diagnostic(source).map_err(|diagnostic| diagnostic.to_string())
}

pub fn verify_diagnostic(
    source: &str,
) -> std::result::Result<VerifiedProgram, crate::shared::diagnostics::Diagnostic> {
    let mut session = Session::search();
    let checked = (|| {
        let source = super::sources::load(source)?;
        let program = verify_using(source.program, &mut session)?;
        session.finish()?;
        Ok(program)
    })();
    checked.map_err(|error| session.report(error))
}

pub fn prove(source: &str) -> Result<(VerifiedProgram, ProofBundle)> {
    prove_diagnostic(source).map_err(|diagnostic| diagnostic.to_string())
}

pub fn prove_diagnostic(
    source: &str,
) -> std::result::Result<(VerifiedProgram, ProofBundle), crate::shared::diagnostics::Diagnostic> {
    let mut session = Session::recording();
    let checked = (|| {
        let source = super::sources::load(source)?;
        let program = verify_using(source.program, &mut session)?;
        session.finish()?;
        Ok((program, source.fingerprint))
    })();
    let (program, fingerprint) = checked.map_err(|error| session.report(error))?;
    let bundle = session
        .bundle(&fingerprint)
        .map_err(crate::shared::diagnostics::Diagnostic::from)?;
    Ok((program, bundle))
}

pub fn verify_with_certificate(source: &str, bundle: &ProofBundle) -> Result<VerifiedProgram> {
    verify_with_certificate_diagnostic(source, bundle).map_err(|diagnostic| diagnostic.to_string())
}

pub fn verify_with_certificate_diagnostic(
    source: &str,
    bundle: &ProofBundle,
) -> std::result::Result<VerifiedProgram, crate::shared::diagnostics::Diagnostic> {
    let mut session = Session::replay(bundle);
    let checked = (|| {
        let source = super::sources::load(source)?;
        bundle.check_source(&source.fingerprint)?;
        let program = verify_using(source.program, &mut session)?;
        session.finish()?;
        Ok(program)
    })();
    checked.map_err(|error| session.report(error))
}

// Bound the unfolded type graph before recursive property checks or symbolic
// record construction. Costs are computed once per declaration using the
// already checked prefix, so repeated fields cannot cause exponential work.
fn check_type_expansion(structs: &[Struct]) -> Result<()> {
    fn cost(t: &Type, known: &BTreeMap<String, (usize, usize)>) -> (usize, usize) {
        let (nodes, depth) = match t {
            Type::Named(n) => known.get(n).copied().unwrap_or((1, 1)),
            Type::Ref(t)
            | Type::Unique(t)
            | Type::Shared(t)
            | Type::Array(t, _)
            | Type::Shape(t) => cost(t, known),
            Type::Union(members) => members.iter().fold((0usize, 0usize), |(nodes, depth), ty| {
                let (child_nodes, child_depth) = cost(ty, known);
                (nodes.saturating_add(child_nodes), depth.max(child_depth))
            }),
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

fn verify_using(parsed: syntax::Program, session: &mut Session) -> Result<VerifiedProgram> {
    crate::shared::worker::run("evergreen-verifier", || program::verify(parsed, session))
}

#[cfg(test)]
mod tests;
