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
        cells: BTreeMap<Linear, Symbol>,
        identity: String,
    },
    Record(String, BTreeMap<String, Symbol>),
    Unit,
    Ref(Box<Ty>, Reference, Vec<Projection<Linear>>),
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
            Node::Formula(Formula::And(a, b) | Formula::Or(a, b), depth) => {
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

// Erased ownership must belong wholly to proof data. A physical owner or a
// reference-bearing resource needs an explicit cross-phase ownership rule.
fn erased_type(t: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match t {
        Type::Ref(_) => false,
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
        Kind::Name(_) | Kind::Number(_) | Kind::Constant(..) => true,
        Kind::Field(base, _) => place_index_expression(base),
        Kind::Index(base, index) => place_index_expression(base) && place_index_expression(index),
        Kind::Unary(op, value) if op == "-" || op == "*" => place_index_expression(value),
        Kind::Binary(op, a, b) if matches!(op.as_str(), "+" | "-" | "*") => {
            place_index_expression(a) && place_index_expression(b)
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
fn effect_origin(expression: &Expr) -> Option<&str> {
    match &expression.kind {
        Kind::Name(name) => Some(name),
        Kind::Unary(_, base) | Kind::Field(base, _) | Kind::Index(base, _) => effect_origin(base),
        _ => None,
    }
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
    opened: BTreeMap<String, BTreeSet<String>>,
    drops: &'a BTreeSet<String>,
    dropping: bool,
    helpers: &'a BTreeSet<String>,
    cleanup_helpers: &'a BTreeSet<String>,
    session: &'a mut Session,
    writable: Vec<WritePlace>,
    old_values: BTreeMap<String, Symbol>,
    ideal_bindings: BTreeSet<String>,
    array_reads: BTreeMap<(String, Linear), Symbol>,
    temporaries: Vec<(Symbol, usize)>,
}

impl<'a> Context<'a> {
    fn write_permitted(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        owned: bool,
    ) -> Result<bool> {
        if owned {
            return Ok(true);
        }
        let plane = self.memory.plane(reference)?;
        let grants = self
            .writable
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
    fn write_places(&mut self, function: &Function) -> Result<Vec<WritePlace>> {
        let phase = std::mem::replace(&mut self.phase, Phase::Specification);
        let mut places: Vec<WritePlace> = Vec::new();
        for expression in &function.modifies {
            let origin = effect_origin(expression)
                .ok_or("modifies requires an incoming reference projection")?
                .to_owned();
            let Some(Symbol::Ref(_, root, root_path)) = self.env.get(&origin).cloned() else {
                return Err("modifies must originate at a reference parameter".into());
            };
            let Symbol::Ref(ty, reference, path) = self.eval(expression, None)? else {
                return Err("modifies entries must denote references".into());
            };
            let scalar_region = match &*ty {
                Ty::Machine(_) | Ty::Bool => true,
                Ty::Array(element, _) => matches!(**element, Ty::Machine(_) | Ty::Bool),
                _ => false,
            };
            if !scalar_region {
                return Err("modifies targets require machine scalars, Booleans, or arrays of those scalars".into());
            }
            if self.memory.plane(root)? != self.memory.plane(reference)?
                || root_path.len() > path.len()
                || !self.paths_equal(&root_path, &path[..root_path.len()])?
            {
                return Err("modifies cannot acquire a different plane's write permission".into());
            }
            // Permissions form a union of places. Two projections from the
            // same input can coincide, including after actual arguments bind
            // symbolic indices. Independent input origins still undergo the
            // separate cross-parameter disjointness check at the call boundary.
            let mut redundant = false;
            for previous in &places {
                if previous.origin == origin
                    && previous.reference == reference
                    && self.paths_equal(&previous.path, &path)?
                {
                    redundant = true;
                    break;
                }
            }
            if redundant {
                continue;
            }
            places.push(WritePlace {
                origin,
                reference,
                path,
                ty,
            });
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
        let cost = values_weight(
            self.memory
                .states()
                .iter()
                .filter_map(|(_, _, value)| *value),
        )?;
        self.charge_value_work(cost)?;
        Ok(self.memory.snapshot())
    }
    fn clone_store(&mut self, store: &Memory<Symbol>) -> Result<Memory<Symbol>> {
        self.charge_value_work(values_weight(
            store.states().iter().filter_map(|(_, _, value)| *value),
        )?)?;
        Ok(store.snapshot())
    }

    fn erased_value(&self, value: &Symbol) -> bool {
        match value.ty() {
            Ty::Record(name) => erased_type(&Type::Named(name), self.structs),
            Ty::Array(element, _) => self.erased_ty(&element),
            Ty::Ref(_) => false,
            _ => true,
        }
    }
    fn erased_ty(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Record(name) => erased_type(&Type::Named(name.clone()), self.structs),
            Ty::Array(element, _) => self.erased_ty(element),
            Ty::Ref(_) => false,
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

    fn follows(&mut self, proposition: &Formula) -> Result<bool> {
        for path in extend(&self.paths, proposition, true)? {
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
        let result = self.arbitrary(&previous.ty())?;
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
            if path.len() == 1
                && matches!(
                    **element,
                    Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
                )
            {
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
                let mut updated = BTreeMap::new();
                for (index, previous) in observed {
                    updated.insert(
                        index.clone(),
                        self.updated_cell(target, &index, &previous, &new)?,
                    );
                }
                updated.insert(target.clone(), new);
                *cells = updated;
                *identity = self.fresh_name();
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
            opened: BTreeMap::new(),
            drops,
            dropping: false,
            helpers,
            cleanup_helpers,
            session,
            writable: Vec::new(),
            old_values: BTreeMap::new(),
            ideal_bindings: BTreeSet::new(),
            array_reads: BTreeMap::new(),
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
    fn capture_old(&mut self) -> Result<()> {
        self.charge_value_work(values_weight(self.env.values())?)?;
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
        if self.phase != Phase::Runtime {
            Ty::Int
        } else {
            Ty::Machine(MachineInt::parse("isize").expect("isize type"))
        }
    }
    fn assume(&mut self, p: &Formula) -> Result<()> {
        let paths = extend(&self.paths, p, false)?;
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
        for path in extend(&self.paths, p, true)? {
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
                cells: BTreeMap::new(),
                identity: name,
            }),
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
                self.module = saved_module;
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
        self.charge_value_work(1)?;
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
        let def = self.structs.get(name).ok_or("unknown struct")?;
        if def.fields.len() != fields.len() {
            return Err(format!("line {line}: wrong fields for {name}"));
        }
        let saved = std::mem::take(&mut self.env);
        let saved_roots = std::mem::take(&mut self.roots);
        let saved_facts = std::mem::take(&mut self.facts);
        let saved_module = std::mem::replace(&mut self.module, def.module.clone());
        let saved_phase = std::mem::replace(&mut self.phase, Phase::Specification);
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
        self.module = saved_module;
        self.phase = saved_phase;
        Ok(())
    }

    fn assign(&mut self, place: &Expr, value: &Expr) -> Result<()> {
        if place.indirect_place() {
            let (reference, fields) = self.location(place)?;
            let id = self.memory.plane(reference)?;
            let owned = self.roots.values().any(|p| *p == id);
            if !self.write_permitted(reference, &fields, owned)? {
                return Err(format!("line {}: writes through reference parameters need an effect contract; unsupported", place.line));
            }
            let old = project(self.memory.read(reference)?, &fields)?.clone();
            if self.symbol_is_affine(&old) {
                return Err("overwriting owned fields through references requires ownership effect proofs; unsupported".into());
            }
            let mut new = self.eval(value, Some(&old.ty()))?;
            let replace_plane = !self.same_layout(&old, &new)?;
            if !replace_plane {
                self.preserve_views(&old, &mut new)?;
            }
            let mut root = self.memory.read(reference)?.clone();
            self.replace_projection(&mut root, &fields, new)?;
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
        let lifted = self.opened.get(&name).cloned().unwrap_or_default();
        self.record_valid_with(&root, place.line, &lifted)?;
        if let Some(id) = self.roots.get(&name) {
            self.memory.write(*id, root.clone(), replace_plane)?;
        }
        self.env.insert(name, root);
        Ok(())
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
                if !matches!(
                    binding.as_ref(),
                    Statement::Let { .. } | Statement::Destructure { .. }
                ) {
                    return Err(
                        "ideal statements require a binding or complete record pattern".into(),
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
                self.helpers.contains(name)
                    && self.functions.get(name).is_some_and(|f| {
                        f.params.len() == args.len()
                            && f.params.iter().zip(args).all(|((parameter, _), e)| {
                                f.ideal_params.contains(parameter) || self.update_expression(e)
                            })
                    })
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
                    .rsplit_once("::")
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
            ) if matches!(
                **element,
                Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
            ) =>
            {
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
                self.representation_access(typename, e.line)?;
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
                    && (literal.is_none()
                        || matches!(
                            *element,
                            Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
                        ))
                {
                    if !matches!(
                        *element,
                        Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
                    ) {
                        return Err("borrowing opaque array elements currently requires a scalar element layout".into());
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
                let Symbol::Ref(_, r, path) = self.eval(x, None)? else {
                    return Err("dereference requires a reference".into());
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
            Type::Array(..) => None,
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
            Kind::Record(n, _) => Some(Ty::Record(n.clone())),
            Kind::Unary(op, x) if op == "&" => self.hint(x).map(|t| Ty::Ref(Box::new(t))),
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
                if let Some(Symbol::Record(_, fields)) = stored(base, &self.env) {
                    return fields.get(field).map(Symbol::ty);
                }
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
    fn read_array(
        &mut self,
        element: &Ty,
        identity: &str,
        index: &Linear,
        items: Option<&[Symbol]>,
        cells: &BTreeMap<Linear, Symbol>,
    ) -> Result<Symbol> {
        if matches!(
            element,
            Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
        ) {
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
        // Stable contents identities give extensional reads across scopes. A
        // reference-bearing selection needs an alias rule, not a fresh plane.
        if self.ty_has_reference(element) {
            return Err("symbolic reads of reference-containing array elements need an alias contract; unsupported".into());
        }
        let key = (identity.to_owned(), index.clone());
        if let Some(value) = self.array_reads.get(&key).cloned() {
            // Replay type facts, never facts specific to the first read's path.
            self.assume_element_type(&value)?;
            return Ok(value);
        }
        let value = self.arbitrary(element)?;
        if matches!(
            element,
            Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
        ) {
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
                self.representation_access(&typename, e.line)?;
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

    fn validate_argument(&mut self, value: &Symbol, line: usize) -> Result<()> {
        if let Symbol::Ref(_, r, path) = value {
            self.charge_value_work(symbol_weight(project(self.memory.read(*r)?, path)?)?)?;
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
                self.representation_access(&typename, e.line)?;
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
                self.charge_value_work(symbol_weight(project(self.memory.read(r)?, &path)?)?)?;
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
            Kind::Binary(op, a, b) if matches!(op.as_str(), "&&" | "||" | "=>") => {
                let a = self.eval(a, Some(&Ty::Bool))?.proposition()?;
                // Logical expressions are pure. Both operands must be well-defined.
                let b = self.eval(b, Some(&Ty::Bool))?.proposition()?;
                Ok(Symbol::Bool(match op.as_str() {
                    "&&" => a.and(b),
                    "=>" => a.not().or(b),
                    _ => a.or(b),
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
                if name == "old" {
                    if self.phase == Phase::Runtime || args.len() != 1 {
                        return Err(
                            "old is proof-only and takes one entry-state parameter expression"
                                .into(),
                        );
                    }
                    let key = Self::old_key(&args[0])?;
                    let value = self
                        .old_values
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| format!("{key} is not a function entry parameter"))?;
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
                    return Ok(if name == "drop" { Symbol::Unit } else { value });
                }
                let f = self.functions.get(name).ok_or_else(|| format!("unknown function {name}; calls require an earlier verified declaration; ideal recursion requires decreases"))?;
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
                let saved_ideal = std::mem::take(&mut self.ideal_bindings);
                let saved_module = std::mem::replace(&mut self.module, f.module.clone());
                self.ideal_bindings = f.ideal_params.iter().cloned().collect();
                self.env.clear();
                self.roots.clear();
                for ((n, t), value) in f.params.iter().zip(actuals) {
                    let saved_specification = self.phase;
                    if f.ideal_params.contains(n) {
                        self.phase = Phase::Specification;
                    }
                    let t = self.resolve(t)?;
                    self.phase = saved_specification;
                    self.compatible(&value.ty(), &t, e.line)?;
                    self.env.insert(n.clone(), value);
                }
                self.capture_old()?;
                if let Some(pre) = &f.pre {
                    let p = self.proposition(pre)?;
                    self.prove(&p, &format!("precondition of {name}"), e.line)?;
                }
                let writes = self.write_places(f)?;
                for write in &writes {
                    for (parameter, _) in &f.params {
                        if parameter == &write.origin {
                            continue;
                        }
                        if let Some(Symbol::Ref(_, reference, path)) =
                            self.env.get(parameter).cloned()
                        {
                            if reference == write.reference
                                && !self.paths_disjoint(&write.path, &path)?
                            {
                                return Err(format!("line {}: writable place from {} overlaps another reference argument or disjointness is unproved", e.line, write.origin));
                            }
                        }
                    }
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
                let value = if let Some(reference) = &f.borrows {
                    let phase = self.phase;
                    self.phase = Phase::Specification;
                    let value = self.eval(reference, Some(&ret))?;
                    self.phase = phase;
                    self.validate_argument(&value, e.line)?;
                    value
                } else {
                    self.arbitrary(&ret)?
                };
                for write in writes {
                    let id = self.memory.plane(write.reference)?;
                    let owned = saved_roots.values().any(|p| *p == id);
                    if !self.write_permitted(write.reference, &write.path, owned)? {
                        return Err(format!("line {}: call to {name} writes through a parameter without a matching modifies contract", e.line));
                    }
                    let mut new = self.arbitrary(&write.ty)?;
                    self.charge_value_work(symbol_weight(self.memory.read(write.reference)?)?)?;
                    let mut root = self.memory.read(write.reference)?.clone();
                    self.preserve_views(project(&root, &write.path)?, &mut new)?;
                    self.replace_projection(&mut root, &write.path, new)?;
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
                // Alias contracts describe entry storage. After applying the
                // checked postcondition, revalidate the saved reference and its
                // current target. Havoced contents need not satisfy nominal
                // invariants until that postcondition has constrained them.
                if f.borrows.is_some() && !f.modifies.is_empty() {
                    self.validate_argument(&value, e.line)?;
                }
                self.env = saved;
                self.roots = saved_roots;
                self.old_values = saved_old;
                self.ideal_bindings = saved_ideal;
                self.module = saved_module;
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
                self.paths = extend(&base, &p, false)?;
                let a = self.scoped_eval(yes, expected)?;
                let a_paths = self.paths.clone();
                let a_store = self.snapshot_memory()?;
                self.paths = extend(&base, &p, true)?;
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
                paths = self.feasible_paths(paths)?;
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
            ) if element == b_element
                && len == b_len
                && matches!(
                    **element,
                    Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
                ) =>
            {
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
                let mut cells = BTreeMap::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for index in indices {
                    let a = a_items
                        .as_ref()
                        .and_then(|items| constant_index(&index).and_then(|i| items.get(i)))
                        .or_else(|| a_cells.get(&index));
                    let b = b_items
                        .as_ref()
                        .and_then(|items| constant_index(&index).and_then(|i| items.get(i)))
                        .or_else(|| b_cells.get(&index));
                    let offset = index.clone();
                    let a = match a {
                        Some(value) => value.clone(),
                        None => self.array_read(element, a_id, &offset)?,
                    };
                    let b = match b {
                        Some(value) => value.clone(),
                        None => self.array_read(element, b_id, &offset)?,
                    };
                    let (value, l, r) = self.join_value(&a, &b)?;
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
    pub(crate) cleanup_helpers: BTreeSet<String>,
    trusted: Vec<crate::certificate::TrustedAssumption>,
    proof_searches: usize,
}

impl VerifiedProgram {
    pub fn trusted_assumptions(&self) -> &[crate::certificate::TrustedAssumption] {
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
        crate::bounded::run("evergreen-entry-checker", || self.check_entry_inner())
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
            let mut session = Session::search();
            let mut ctx = Context::new(
                &functions,
                &self.structs,
                &self.drops,
                &helpers,
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
// Bound the unfolded type graph before recursive property checks or symbolic
// record construction. Costs are computed once per declaration using the
// already checked prefix, so repeated fields cannot cause exponential work.
fn check_type_expansion(structs: &[Struct]) -> Result<()> {
    fn cost(t: &Type, known: &BTreeMap<String, (usize, usize)>) -> (usize, usize) {
        let (nodes, depth) = match t {
            Type::Named(n) => known.get(n).copied().unwrap_or((1, 1)),
            Type::Ref(t) | Type::Array(t, _) => cost(t, known),
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
    crate::bounded::run("evergreen-verifier", || verify_inner(source, session))
}
fn verify_inner(source: &str, session: &mut Session) -> Result<VerifiedProgram> {
    let parsed = syntax::parse(source)?;
    check_type_expansion(&parsed.structs)?;
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
    let mut all_functions = parsed.functions;
    all_functions.extend(parsed.destructors.into_iter().map(|(_, f)| f));
    let mut obligations = 0;
    for f in &mut all_functions {
        f.partial = !f.ideal && f.decreases.is_none() && crate::effects::recursive(f);
        for (name, ty) in &f.params {
            if f.ideal_params.contains(name) && !erased_type(ty, &structs) {
                return Err(format!("line {}: ideal parameters require pure proof data; runtime owners and reference-bearing resources need a cross-phase ownership contract", f.line));
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
            if f.ideal
                || f.modifies.iter().any(|expression| !borrow_expression(expression) || !references.iter().any(|(name, _)| Some(name.as_str()) == effect_origin(expression)))
                || references.iter().any(|(_, ty)| !matches!(ty, Type::Ref(target) if !type_has_reference(target, &structs)))
            {
                return Err(format!("line {}: modifies requires incoming reference projections without nested reference-bearing parameters", f.line));
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
            "move" | "drop" | "int" | "nat" | "old"
        ) {
            return Err(format!("line {}: {} is a reserved builtin", f.line, f.name));
        }
        if let Some(reference) = &f.borrows {
            if f.ideal || !matches!(f.ret, Type::Ref(_)) || !borrow_expression(reference) {
                return Err(format!("line {}: borrows requires a reference return and a checked incoming reference projection", f.line));
            }
        } else if type_has_reference(&f.ret, &structs) {
            return Err(format!("line {}: returning references requires an explicit borrows contract; reference-bearing aggregate returns are unsupported", f.line));
        }
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
        for (n, t) in &f.params {
            if ctx.env.contains_key(n) {
                return Err(format!("line {}: duplicate parameter {n}", f.line));
            }
            ctx.phase = if f.ideal_params.contains(n) {
                Phase::Specification
            } else {
                execution
            };
            let ty = ctx.resolve(t)?;
            let value = ctx.arbitrary(&ty)?;
            ctx.phase = execution;
            ctx.env.insert(n.clone(), value);
        }
        ctx.capture_old()?;
        if let Some(pre) = &f.pre {
            ctx.phase = Phase::Specification;
            let p = ctx.eval(pre, Some(&Ty::Bool))?.proposition()?;
            ctx.assume(&p)?;
            ctx.phase = execution;
        }
        ctx.writable = ctx.write_places(f)?;
        let ret = ctx.resolve(&f.ret)?;
        if let Some(measure) = &f.decreases {
            ctx.phase = Phase::Specification;
            ctx.measure = Some(ctx.nonnegative(measure, "nonnegative recursion measure")?);
            ctx.phase = execution;
        }
        let contract_env = ctx.clone_env()?;
        let borrowed_result = if let Some(reference) = &f.borrows {
            ctx.phase = Phase::Specification;
            let value = ctx.eval(reference, Some(&ret))?;
            ctx.phase = execution;
            let Symbol::Ref(_, expected, _) = &value else {
                return Err("borrows must denote a reference".into());
            };
            let incoming = f.params.iter().any(|(name, ty)| {
                matches!(ty, Type::Ref(_))
                    && matches!(contract_env.get(name), Some(Symbol::Ref(_, r, _)) if r == expected)
            });
            if !incoming {
                return Err(format!("line {}: borrows must refer to caller-owned parameter storage, not a local parameter slot", reference.line));
            }
            Some(value)
        } else {
            None
        };
        for statement in &f.body {
            ctx.statement(statement)?;
        }
        let value = ctx.scoped_eval(&f.result, Some(&ret))?;
        if let Some(Symbol::Ref(_, expected, path)) = &borrowed_result {
            let matches = if let Symbol::Ref(_, actual, actual_path) = &value {
                actual == expected && ctx.paths_equal(actual_path, path)?
            } else {
                false
            };
            if !matches {
                return Err(format!(
                    "line {}: returned reference does not match its borrows contract",
                    f.result.line
                ));
            }
            ctx.validate_argument(&value, f.result.line)?;
        }
        ctx.validate_live(f.result.line)?;
        ctx.finish_scope(f)?;
        if let Some(post) = &f.post {
            ctx.phase = Phase::Specification;
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
        f.partial = ctx.partial_execution;
        if crate::effects::invariant_independent(f, &functions, &helpers) {
            helpers.insert(f.name.clone());
        }
        if crate::effects::ownership_free(f, &functions, &cleanup_helpers) {
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
mod tests {
    #[test]
    fn reference_returns_preserve_incoming_planes_and_reject_local_escapes() {
        let good = include_str!("../examples/borrow_returns.evg");
        assert_eq!(verify(good).unwrap().run().unwrap().to_string(), "42");
        for source in [
            "fn bad(r: &usize) -> &usize borrows(r) {let local = *r; &local}",
            "fn bad(a: &usize, b: &usize) -> &usize borrows(a) {b}",
            "fn bad(r: &usize) -> &&usize borrows(&r) {&r}",
            "fn bad(n: usize) -> &usize borrows(&n) {&n}",
            "fn bad(r: &usize) -> &usize {r}",
            "fn bad(r: &usize) -> usize borrows(r) {*r}",
            "fn bad(r: &usize) -> &usize borrows(if true {r} else {r}) {r}",
        ] {
            assert!(verify(source).is_err(), "{source}");
        }
        let stale = good.replace("    *r", "    drop(pair);\n    *r");
        assert!(verify(&stale).is_err());
        let replaced = good.replace(
            "    *r",
            "    drop(pair);\n    pair = Pair {left: 0, right: 42};\n    *r",
        );
        assert!(verify(&replaced).is_err());
        let array = "fn first(a: &[usize; 2]) -> &usize borrows(&(*a)[0]) {&(*a)[0]} fn main() -> usize {let a: [usize; 2] = [42, 7]; *first(&a)}";
        assert_eq!(verify(array).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn modifying_reference_returns_keep_the_entry_alias_and_replay() {
        let library = include_str!("../stdlib/array.evg");
        let source = format!(
            "{library} {}",
            include_str!("../examples/write_borrows.evg")
        );
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        let replayed = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(replayed.proof_search_count(), 0);
        assert_eq!(replayed.run().unwrap().to_string(), "42");
        let scalar = "fn increment(r: &usize) -> &usize where(*r < usize::MAX) modifies(r) borrows(r) ensures(*result == old(*r) + 1) {*r = *r + 1; r} fn main() -> usize ensures(result == 42) {let n: usize = 41; let original = &n; let updated = increment(&n); proof visible: *original == 42; *updated}";
        assert_eq!(verify(scalar).unwrap().run().unwrap().to_string(), "42");
        let frame = "fn set(a: &[usize; 2]) -> &usize modifies(&(*a)[0]) borrows(&(*a)[0]) ensures(*result == 42) {(*a)[0] = 42; &(*a)[0]} fn main() -> usize ensures(result == 49) {let a: [usize; 2] = [1, 7]; let r = set(&a); *r + a[1]}";
        assert_eq!(verify(frame).unwrap().run().unwrap().to_string(), "49");
        let parent = "type Pair struct {left: usize, right: usize} fn set(p: &Pair) -> &Pair modifies(&(*p).left) borrows(p) ensures((*result).left == 7) {(*p).left = 7; p} fn main() -> usize ensures(result == 42) {let p = Pair {left: 0, right: 42}; let q = set(&p); (*q).right}";
        assert_eq!(verify(parent).unwrap().run().unwrap().to_string(), "42");
        let invariant = "type Fixed struct {value: usize} where(value == 42); fn refresh(r: &Fixed) -> &Fixed modifies(&(*r).value) borrows(r) ensures((*r).value == 42 && (*result).value == 42) {(*r).value = 42; r} fn main() -> usize ensures(result == 42) {let fixed = Fixed {value: 42}; let refreshed = refresh(&fixed); (*refreshed).value}";
        assert_eq!(verify(invariant).unwrap().run().unwrap().to_string(), "42");
        let readonly = "fn set(a: &usize, b: &usize) -> &usize modifies(a) borrows(b) ensures(*a == 7 && *result == old(*b)) {*a = 7; b} fn main() -> usize ensures(result == 42) {let a: usize = 0; let b: usize = 42; *set(&a, &b)}";
        assert_eq!(verify(readonly).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn modifying_returns_cannot_change_aliases_or_bypass_write_permissions() {
        for source in [
            "fn bad(r: &usize) -> &usize modifies(r) borrows(r) {*r = 42; let local: usize = 42; &local}",
            "fn bad(r: &usize, other: &usize) -> &usize modifies(r) borrows(r) {*r = 42; other}",
            "fn bad(a: &[usize; 2], i: usize) -> &usize where(i == 0) modifies(&(*a)[i]) borrows(&(*a)[i]) {(*a)[i] = 42; i = 1; &(*a)[i]}",
            "fn bad(a: &[usize; 2]) -> &usize modifies(a) borrows(&(*a)[0]) {*a = [42]; &(*a)[0]}",
            "fn bad(r: &usize) -> &usize modifies(r) borrows(r) {drop(*r); r}",
            "ideal fn bad(r: &usize) -> &usize modifies(r) borrows(r) {r}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
        let parent = "type Pair struct {left: usize, right: usize} fn set(p: &Pair) -> &Pair modifies(&(*p).left) borrows(p) {(*p).left = 7; p} fn bad(p: &Pair) modifies(&(*p).left) {let wider = set(p); (*wider).right = 42;}";
        assert!(verify(parent).unwrap_err().contains("effect contract"));
        let overlaps = "fn set(a: &usize, b: &usize) -> &usize modifies(a) borrows(b) {*a = 7; b} fn main() -> usize {let n: usize = 42; *set(&n, &n)}";
        assert!(verify(overlaps).unwrap_err().contains("overlaps"));
        let setter = "fn set(r: &usize) -> &usize modifies(r) borrows(r) ensures(*result == 42) {*r = 42; r}";
        for caller in [
            "fn bad(r: &usize) -> &usize borrows(r) {set(r)}",
            "fn bad(r: &usize) {proof cannot_erase_write: *set(r) == 42;}",
            "fn main() -> usize {let n: usize = 1; let r = set(&n); drop(n); *r}",
            "fn main() -> usize {let n: usize = 1; let r = set(&n); drop(n); n = 42; *r}",
            "fn main() -> usize ensures(result == 0) {let n: usize = 0; *set(&n)}",
        ] {
            assert!(
                verify(&format!("{setter} {caller}")).is_err(),
                "accepted {caller}"
            );
        }
    }

    #[test]
    fn computed_place_contracts_capture_checked_entry_expressions() {
        let source = include_str!("../examples/computed_places.evg");
        let (program, bundle) = prove(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        let replayed = verify_with_certificate(source, &bundle).unwrap();
        assert_eq!(replayed.proof_search_count(), 0);
        assert_eq!(replayed.run().unwrap().to_string(), "42");
        let cursor = "fn insert(data: &[usize; 3], cursor: &usize) -> &usize where(*cursor < 2) modifies(cursor, &(*data)[*cursor + 1]) borrows(&(*data)[*cursor + 1]) ensures(*result == 42 && *cursor == old(*cursor) + 1) {let selected = &(*data)[*cursor + 1]; *selected = 42; *cursor = *cursor + 1; selected} fn main() -> usize ensures(result == 42) {let data: [usize; 3] = [7, 8, 9]; let cursor: usize = 1; let selected = insert(&data, &cursor); proof cursor_changed: cursor == 2; *selected}";
        assert_eq!(verify(cursor).unwrap().run().unwrap().to_string(), "42");
        let math = "fn next(data: &[usize; 3], i: usize) -> &usize where(i < 2) borrows(&(*data)[int(i) + 1]) {&(*data)[i + 1]} fn main() -> usize {let a: [usize; 3] = [7, 8, 42]; *next(&a, 1)}";
        assert_eq!(verify(math).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn computed_place_contracts_reject_overflow_bounds_and_retargeting() {
        for source in [
            "fn bad(a: &[usize; 2], i: usize) -> &usize where(i < 2) borrows(&(*a)[i + 1]) {&(*a)[i + 1]}",
            "fn bad(a: &[usize; 3], i: usize) -> &usize where(i == usize::MAX) borrows(&(*a)[i + 1]) {&(*a)[0]}",
            "fn bad(a: &[usize; 3], i: usize) -> &usize where(i < 2) borrows(&(*a)[i - 1]) {&(*a)[0]}",
            "fn bad(a: &[usize; 3], i: usize) -> &usize where(i == 0) borrows(&(*a)[i + 1]) {i = 1; &(*a)[i + 1]}",
            "fn bad(a: &[usize; 3], i: usize) where(i == 0) modifies(&(*a)[i + 1]) {i = 1; (*a)[i + 1] = 42;}",
            "fn bad(a: &[usize; 3], cursor: &usize) where(*cursor == 0) modifies(cursor, &(*a)[*cursor + 1]) {*cursor = 1; (*a)[*cursor + 1] = 42;}",
            "fn set(i: &usize) -> usize modifies(i) {*i = 0; 0} fn bad(a: &[usize; 3], i: &usize) -> &usize borrows(&(*a)[set(i)]) {&(*a)[0]}",
        ] {
            assert!(verify(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn later_call_arguments_cannot_invalidate_earlier_borrows() {
        let source = "type Owner struct {tag: usize} impl Drop for Owner {fn drop(self){}} fn read_then_consume(r: &usize, owner: Owner) -> usize {*r} fn main() -> usize {let owner = Owner {tag: 42}; read_then_consume(&owner.tag, owner)}";
        assert!(verify(source).is_err());
    }

    #[test]
    fn expanding_value_copies_are_rejected_before_unbounded_materialization() {
        let mut arrays = "fn main() -> usize {let a0: [usize; 1] = [1];".to_owned();
        for i in 1..40 {
            arrays.push_str(&format!("let a{i} = [a{}, a{}];", i - 1, i - 1));
        }
        arrays.push_str("42}");
        let error = verify(&arrays).unwrap_err();
        assert!(error.contains("symbolic value"), "{error}");
        let mut formulas = "fn f(flag: bool) -> usize {let p0 = flag;".to_owned();
        for i in 1..40 {
            formulas.push_str(&format!("let p{i} = p{} && !p{};", i - 1, i - 1));
        }
        formulas.push_str("42}");
        let error = match verify(&formulas) {
            Err(error) => error,
            Ok(_) => panic!("expanded formulas must hit a checked work limit"),
        };
        assert!(error.contains("symbolic value"), "{error}");
        let mut snapshots = format!(
            "fn main() -> usize {{let a: [usize; 256] = [{}]; let r = &a;",
            vec!["1"; 256].join(",")
        );
        for _ in 0..512 {
            snapshots.push_str("if true {()} else {()};");
        }
        snapshots.push_str("42}");
        let error = match verify(&snapshots) {
            Err(error) => error,
            Ok(_) => panic!("branch snapshots must be charged"),
        };
        assert!(error.contains("work limit"), "{error}");
        let ordinary = "fn main() -> usize {let a: [usize; 2] = [7, 42]; let b = [a, a]; let c = [b, b]; c[1][0][1]}";
        assert_eq!(verify(ordinary).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn compact_type_graphs_and_fact_chains_have_checked_work_limits() {
        let mut source = "type Node0 struct {value: usize}\n".to_owned();
        for i in 1..20 {
            source.push_str(&format!(
                "type Node{i} struct {{left: Node{}, right: Node{}}}\n",
                i - 1,
                i - 1
            ));
        }
        source.push_str("fn main() -> usize {42}");
        assert!(verify(&source)
            .unwrap_err()
            .contains("type expansion limit"));
        let mut source = "fn main() -> usize {fact f0 = true;".to_owned();
        for i in 1..150 {
            source.push_str(&format!("fact f{i} = f{};", i - 1));
        }
        source.push_str("42}");
        assert!(verify(&source)
            .unwrap_err()
            .contains("verification evaluation limit"));
        assert!(verify("type Pair struct {left: usize, right: usize} fn main() -> usize {let p = Pair {left: 7, right: 42}; p.right}").is_ok());
    }

    #[test]
    fn borrowed_temporaries_keep_their_drop_receiver_valid_until_scope_exit() {
        let declarations = "type Owner struct {tag: usize} where (tag == 7); impl Drop for Owner {fn drop(self){}} type Holder struct {reference: &usize, tag: usize} where (fact live = *reference == 7; live); impl Drop for Holder {fn drop(self){proof receiver_valid: self::live;}} fn consume(owner: Owner) -> usize ensures (result == 0) {0}";
        let bad = "fn main() -> usize {let owner = Owner {tag: 7}; let value = Holder {reference: &owner.tag, tag: 42}.tag + consume(owner); value}";
        assert!(verify(&format!("{declarations}\n{bad}"))
            .unwrap_err()
            .contains("implicit temporary cleanup"));
        let good = "fn main() -> usize ensures (result == 42) {let owner = Owner {tag: 7}; let value = Holder {reference: &owner.tag, tag: 42}.tag; drop(owner); value}";
        let (value, events) = verify(&format!("{declarations}\n{good}"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events, ["drop Holder", "drop Owner"]);
    }

    #[test]
    fn array_read_facts_survive_contracts_and_branch_scope_changes() {
        let source = include_str!("../examples/array_contracts.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert!(verify(&source.replace("{data}", "{[data[1], data[0]]}")).is_err());
        let branch = "fn select(data: [usize; 2], index: usize, flag: bool) -> usize where (index < 2) ensures (result == data[index]) {if flag {data[index]} else {data[index]}}";
        assert!(verify(branch).is_ok());
        let record = "type Positive struct {value: usize} where (value > 0); fn select(data: [Positive; 1], flag: bool) -> Positive ensures (result.value == data[0].value) {if flag {data[0]} else {data[0]}} fn main() -> usize ensures (result == 42) {let input: [Positive; 1] = [Positive {value: 42}]; let answer = select(input, false); answer.value}";
        assert_eq!(verify(record).unwrap().run().unwrap().to_string(), "42");
        let nested = "fn read(data: [[usize; 2]; 1]) -> usize ensures (result == data[0][1]) {data[0][1]} fn main() -> usize ensures (result == 42) {let data: [[usize; 2]; 1] = [[7, 42]]; read(data)}";
        assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
        let false_fact = "type Item struct {value: usize} where (fact lie = 1 == 2; true); fn bad(data: [Item; 1]) -> usize ensures (result == 1) {let first = data[0]; let second = data[0]; 0}";
        assert!(verify(false_fact).is_err());
        let branch_fact = "fn bad(data: [usize; 1]) -> usize ensures (result == 0) {if data[0] == 0 {data[0]} else {data[0]}}";
        assert!(verify(branch_fact).is_err());
        let literal = "fn first(n: usize, data: [u8; n]) -> u8 where (n > 0) ensures (result == data[0]) {data[0]} fn main() -> u8 ensures (result == 7) {let n: usize = 1; first(2, [7, 42])}";
        assert_eq!(verify(literal).unwrap().run().unwrap().to_string(), "7");
        assert!(verify(&literal.replace("first(2, [7, 42])", "first(2, [7])")).is_err());
        assert!(verify(&literal.replace("first(2, [7, 42])", "first(2, [256, 42])")).is_err());
    }

    #[test]
    fn field_assignment_cannot_resurrect_siblings_consumed_by_its_rhs() {
        let declarations = "type Left struct {} impl Drop for Left {fn drop(self){}} type Right struct {} impl Drop for Right {fn drop(self){}} type Pair struct {left: Left, right: Right} fn take(pair: Pair) -> Left {let Pair {left, right} = pair; left}";
        let bad = "fn main() -> usize {let pair = Pair {left: Left {}, right: Right {}}; pair.left = take(pair); 0}";
        assert!(verify(&format!("{declarations}\n{bad}"))
            .unwrap_err()
            .contains("field assignment cannot restore shape"));
        let good = "fn main() -> usize {let pair = Pair {left: Left {}, right: Right {}}; pair = Pair {left: take(pair), right: Right {}}; 0}";
        let (_, events) = verify(&format!("{declarations}\n{good}"))
            .unwrap()
            .run_with_events()
            .unwrap();
        assert_eq!(events, ["drop Right", "drop Left", "drop Right"]);
        let explicit_move = "type Plain struct {left: usize, right: usize} fn take(p: Plain) -> usize {p.left} fn main() -> usize {let p = Plain {left: 1, right: 2}; p.left = take(move(p)); p.left}";
        assert!(verify(explicit_move).is_err());
    }

    #[test]
    fn ideal_parameters_are_checked_and_erased_without_runtime_access() {
        let source = include_str!("../examples/ideal_parameters.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert!(verify(&source.replace("countdown(5, 5)", "countdown(5, 6)")).is_err());
        assert!(verify(&source.replace(
            "checked_value(42, expected_answer())",
            "checked_value(41, expected_answer())"
        ))
        .is_err());
        for body in [
            "n",
            "let x = n; x",
            "let r = &n; *r",
            "n = 1; 0",
            "if n > 0 {1} else {0}",
            "move(n)",
        ] {
            assert!(
                verify(&format!("fn bad(ideal n: usize) -> usize {{{body}}}")).is_err(),
                "{body}"
            );
        }
        let interleaved = "fn sum(ideal a: nat, x: usize, ideal b: nat, y: usize) -> usize where (x <= 10 && y <= 10 && a == nat(x) && b == nat(y)) ensures (nat(result) == a + b) {x + y} fn main() -> usize ensures (result == 3) {sum(1, 1, 2, 2)}";
        assert_eq!(verify(interleaved).unwrap().run().unwrap().to_string(), "3");
        let only_ideal = "fn answer(ideal expected: nat) -> usize where (expected == 42) ensures (nat(result) == expected) {42} fn main() -> usize {answer(42)}";
        assert_eq!(verify(only_ideal).unwrap().run().unwrap().to_string(), "42");
        let affine =
            "ideal affine type Ticket struct {tag: nat} fn bad(ideal t: Ticket) -> usize {0}";
        assert!(verify(affine).is_ok());
        let effect = "fn write(r: &usize) -> usize modifies(r) ensures (result == 1) {*r = 1; 1} fn metadata(ideal n: nat) -> usize {0} fn main() -> usize {let x: usize = 0; metadata(nat(write(&x)))}";
        assert!(verify(effect).unwrap_err().contains("modifying calls"));
        let declarations = source.split("fn main()").next().unwrap();
        let update = "type Pair struct {left: usize, right: usize} where (fact balanced = left == right; balanced); fn main() -> usize ensures (result == 42) {let p = Pair {left: 0, right: 0}; update(p) lifts balanced {p.left = checked_value(42, expected_answer()); p.right = p.left;} p.right}";
        assert_eq!(
            verify(&format!("{declarations}\n{update}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
    }

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
        let executed = format!("{source}\n{}", include_str!("../examples/rc_count.evg"));
        let program = verify(&executed).unwrap();
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(program.run().unwrap().to_string(), "0");
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
    fn ideal_bindings_are_erased_and_keep_affine_ownership() {
        let source = include_str!("../examples/ideal_bindings.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        for body in [
            "ideal let n: usize = 42; n",
            "ideal let n: usize = 1; if n == 1 {42} else {0}",
            "ideal let n: usize = 1; let r = &n; *r",
            "ideal let n: usize = 1; n = 2; 42",
            "ideal let n = false; proof unsound: n; 42",
            "ideal let n: usize = usize::MAX + 1; 42",
        ] {
            assert!(
                verify(&format!("fn main() -> usize {{{body}}}")).is_err(),
                "{body}"
            );
        }
        let library = include_str!("../stdlib/credits.evg");
        let client = include_str!("../proofs/ideal_credit_bindings.evg");
        assert!(verify(&format!("{library} {client}")).is_ok());
        assert!(verify(&format!(
            "{library} {}",
            client.replace("spend_credit(right, value)", "spend_credit(left, value)")
        ))
        .is_err());
        assert!(verify(&format!(
            "{library} {}",
            client.replace(
                "ideal let credits::Split {left, right} = parts;",
                "let credits::Split {left, right} = parts;"
            )
        ))
        .is_err());
        let bad = "fn steal(ideal c: credits::Credit) -> usize {ideal let credits::Credit {units} = c; 42}";
        assert!(verify(&format!("{library} {bad}")).is_err());
        let observer = "type Resource struct {tag: usize} where(tag == 42); impl Drop for Resource {fn drop(self){}} ideal fn observe(r: &Resource) -> nat ensures(result == nat((*r).tag)) {nat((*r).tag)} fn main() -> usize {let r = Resource {tag: 42}; ideal let saved = observe(&r); proof correct: saved == 42; r.tag}";
        let (value, events) = verify(observer).unwrap().run_with_events().unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events, ["drop Resource"]);
        assert!(verify(&observer.replace("observe(&r)", "drop(r)")).is_err());
    }

    #[test]
    fn erased_affine_resources_move_without_runtime_values_or_effects() {
        let source = include_str!("../examples/erased_resources.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let declarations = source.split("fn main").next().unwrap();
        for bad in [
            "fn duplicate(ideal t: tickets::Ticket) -> usize {let a = consume(t, 0); consume(t, 42)}",
            "fn restore(ideal t: tickets::Ticket) -> usize {let a = consume(t, 0); consume(old(t), 42)}",
            "fn leak(ideal t: tickets::Ticket) -> usize {t}",
            "fn branch(ideal t: tickets::Ticket) -> usize {if t.tag == 1 {42} else {0}}",
        ] {assert!(verify(&format!("{declarations} {bad}")).is_err(), "{bad}");}
        let proof_view = "ideal fn inspect(t: tickets::Ticket) -> nat {1} fn caller(ideal t: tickets::Ticket) -> usize {proof stable: inspect(t) == inspect(t); consume(t, 42)}";
        // A missing postcondition cannot prove equality of arbitrary summaries.
        assert!(verify(&format!("{declarations} {proof_view}")).is_err());
        let proof_view = proof_view.replace("-> nat {1}", "-> nat ensures(result == 1) {1}");
        assert!(verify(&format!("{declarations} {proof_view}")).is_ok());
        let old_scalar = "fn answer(ideal expected: nat) -> usize where(expected == 42) ensures(result == 42) {42} fn caller(n: usize) -> usize where(n == 42) ensures(result == 42) {n = 0; answer(nat(old(n)))} fn main() -> usize {caller(42)}";
        assert_eq!(verify(old_scalar).unwrap().run().unwrap().to_string(), "42");
        let library = include_str!("../stdlib/credits.evg");
        let bridge = "fn spend(ideal credit: credits::Credit, value: usize) -> usize ensures(result == value) {value} fn forward(ideal credit: credits::Credit, value: usize) -> usize ensures(result == value) {spend(credit, value)}";
        assert!(verify(&format!("{library} {bridge}")).is_ok());
        let borrow = "ideal affine type WithRef struct {r: &usize} fn bad(ideal resource: WithRef) -> usize {0}";
        assert!(verify(borrow).unwrap_err().contains("cross-phase"));
        let resource = "type Resource struct {} impl Drop for Resource {fn drop(self){}}";
        for bad in [
            "ideal fn consume_resource(resource: Resource) -> nat {1}",
            "ideal fn make_resource() -> Resource {Resource {}}",
            "ideal fn make_hidden() -> nat {let r = Resource {}; 1}",
            "fn metadata(ideal u: ()) -> usize {0} fn main() -> usize {let r = Resource {}; metadata(drop(r))}",
            "fn metadata(ideal n: usize) -> usize {0} fn main() -> usize {let n: usize = 42; metadata(move(n))}",
        ] {assert!(verify(&format!("{resource} {bad}")).is_err(), "{bad}");}
    }

    #[test]
    fn opaque_module_representations_are_checked_without_client_privileges() {
        let source = include_str!("../examples/opaque_values.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let declarations = source.split("fn main").next().unwrap();
        for body in [
            "let p = permits::Permit {tag: 42}; 42",
            "let p = permits::issue(); p.tag",
            "let p = permits::issue(); p.tag = 42; 42",
            "let p = permits::issue(); let r = &p.tag; *r",
            "let p = permits::issue(); let permits::Permit {tag} = p; tag",
            "let p = permits::issue(); let x = permits::read(&p); p.tag",
            "let p = permits::issue(); proof hidden: p.tag == 42; 42",
        ] {
            let error =
                verify(&format!("{declarations} fn main() -> usize {{{body}}}")).unwrap_err();
            assert!(error.contains("opaque representation"), "{error}: {body}");
        }
        assert!(verify(&format!(
            "{declarations} module permits {{fn forge() -> Permit {{Permit {{tag: 42}}}}}}"
        ))
        .is_err());
        assert!(verify(&format!("{declarations} module other {{fn forge() -> permits::Permit {{permits::Permit {{tag: 42}}}}}}" )).is_err());
        assert!(verify(&format!(
            "{declarations} impl Drop for permits::Permit {{fn drop(self){{}}}}"
        ))
        .unwrap_err()
        .contains("defining module"));
        let self_fact = source.replace("tag == 42", "self.tag == 42");
        assert_eq!(verify(&self_fact).unwrap().run().unwrap().to_string(), "42");
        let wrap = "type Wrapper struct {p: permits::Permit} where (p::valid); fn main() -> usize {let wrapper = Wrapper {p: permits::issue()}; permits::read(&wrapper.p)}";
        assert_eq!(
            verify(&format!("{declarations} {wrap}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
        assert!(verify(&format!(
            "{declarations} {}",
            wrap.replace("p::valid", "p.tag == 42")
        ))
        .is_err());
    }

    #[test]
    fn opaque_affine_credits_can_be_rearranged_but_not_forged_or_duplicated() {
        let library = include_str!("../stdlib/credits.evg");
        assert!(verify(&format!(
            "{library} {}",
            include_str!("../proofs/opaque_credits.evg")
        ))
        .is_ok());
        for client in [
            "ideal fn forge() -> credits::Credit {credits::Credit {units: 7}}",
            "ideal fn steal(c: credits::Credit) -> nat {c.units}",
            "ideal fn duplicate(c: credits::Credit) -> credits::Split {credits::Split {left: c, right: c}}",
            "ideal fn extract(c: credits::Credit) -> nat {let credits::Credit {units} = c; units}",
            "ideal fn forge(c: credits::Credit) -> credits::Credit {credits::join(credits::Credit {units: 7}, c)}",
            "ideal fn mint(c: credits::Credit) -> credits::Credit {c.units = 7; c}",
            "ideal fn copy(c: &credits::Credit) -> credits::Credit {*c}",
        ] {assert!(verify(&format!("{library} {client}")).is_err(), "{client}");}
    }

    #[test]
    fn dynamic_array_projections_preserve_aliasing_and_prove_disjointness() {
        let source = include_str!("../examples/indexed_borrows.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        assert_eq!(
            verify(
                &source
                    .replace("may_alias(data, 1, 1)", "may_alias(data, 0, 1)")
                    .replace(
                        "ensures (result == 42) {\n    let data",
                        "ensures (result == 1) {\n    let data"
                    )
            )
            .unwrap()
            .run()
            .unwrap()
            .to_string(),
            "1"
        );
        let definitions = source.split("fn may_alias").next().unwrap();
        let equal_reads = "fn same(data: [usize; 2], i: usize, j: usize) -> usize where (i < 2 && j < 2 && i == j) ensures(result == 0) {data[i] - data[j]}";
        assert!(verify(equal_reads).is_ok());
        let fake = "fn bad(data: [usize; 2], i: usize, j: usize) -> usize where (i < 2 && j < 2) ensures(result == 42) {let a = &data[i]; let b = &data[j]; set_42(a); *b}";
        assert!(verify(&format!("{definitions} {fake}")).is_err());
        let fake = "fn bad(data: [usize; 2], i: usize) -> usize where(i < 2) ensures(result == data[i]) {let r = &data[i]; set_42(r); *r}";
        assert!(verify(&format!("{definitions} {fake}")).is_err());
        let contract = "fn same(data: &[usize; 2], i: usize, j: usize) -> &usize where(i < 2 && j < 2 && i == j) borrows(&(*data)[i]) {&(*data)[j]}";
        assert!(verify(contract).is_ok());
        assert!(verify(&contract.replace(" && i == j", "")).is_err());
        let snapshot = "fn snapshot(data: [usize; 2], i: usize) -> usize where(i == 0) ensures(result == 42) {let r = &data[i]; i = 1; set_42(r); data[0]} fn main() -> usize {let data: [usize; 2] = [7, 1]; snapshot(data, 0)}";
        assert_eq!(
            verify(&format!("{definitions} {snapshot}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
        let swap = include_str!("../stdlib/swap.evg");
        let wrapper = "fn dynamic_swap(data: [usize; 2], i: usize, j: usize) -> usize where(i < 2 && j < 2 && i != j) ensures(result == data[j]) {swap_usize(&data[i], &data[j]); data[i]} fn main() -> usize ensures(result == 42) {dynamic_swap([7, 42], 0, 1)}";
        assert_eq!(
            verify(&format!("{swap} {wrapper}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
        assert!(
            verify(&format!("{swap} {}", wrapper.replace(" && i != j", "")))
                .unwrap_err()
                .contains("disjointness")
        );
        let no_bound =
            "fn bad(data: &[usize; 2], i: usize) -> &usize borrows(&(*data)[i]) {&(*data)[i]}";
        assert!(verify(no_bound).is_err());
        let signed = "fn bad(data: &[usize; 2], i: isize) -> &usize where(i < 2) borrows(&(*data)[i]) {&(*data)[i]}";
        assert!(verify(signed).is_err());
    }

    #[test]
    fn implication_and_unlifted_weaker_invariants_check_each_store() {
        let source = include_str!("../examples/weak_invariant.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let bad = source.replace("ledger.count = 42;", "ledger.count = 0;");
        assert!(verify(&bad).is_err());
        let bad = source.replace(
            "ledger::reference_count_is_0_implies_no_owners;",
            "ledger::reference_count_is_accurate;",
        );
        assert!(verify(&bad).is_err());
        let release = "fn release() -> usize {let ledger = Ledger {count: 1, owners: 1}; update(ledger) lifts reference_count_is_accurate {ledger.owners = 0; proof still_safe: ledger::reference_count_is_0_implies_no_owners; ledger.count = 0;} ledger.count}";
        assert!(verify(&format!(
            "{} {release}",
            source.split("fn main").next().unwrap()
        ))
        .is_ok());
        for a in [false, true] {
            for b in [false, true] {
                let program = verify(&format!(
                    "fn main() -> bool ensures(result == {}) {{{a} => {b}}}",
                    !a || b
                ))
                .unwrap();
                assert_eq!(program.run().unwrap().to_string(), (!a || b).to_string());
            }
        }
        // Implication binds below || and associates to the right.
        assert_eq!(
            verify("fn main() -> bool ensures(result == true) {false => true => false}")
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "true"
        );
        assert!(verify("fn bad() -> bool ensures(result == true) {true => false}").is_err());
        assert!(verify("fn bad() -> bool {1 => true}").is_err());
    }

    #[test]
    fn opaque_array_borrows_share_cells_bounds_and_branch_state() {
        let source = include_str!("../examples/array_borrows.evg");
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
        let declarations = source.split("fn main").next().unwrap();
        let branch = "fn choose(data: &[usize; 2], flag: bool) -> usize ensures(result == (*data)[0]) {if flag {*first(2, data)} else {(*data)[0]}} fn main() -> usize ensures(result == 42) {let data: [usize; 2] = [42, 7]; choose(&data, true)}";
        assert_eq!(
            verify(&format!("{declarations} {branch}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
        for bad in [
            source.replace("where (n > 0)", ""),
            source.replace("    *right\n}", "    drop(data);\n    *right\n}"),
            source.replace("first(2, &data)", "first(0, &data)"),
        ] {
            assert!(verify(&bad).is_err());
        }
        let frame = "fn set(r: &usize) modifies(r) ensures(*r == 42) {*r = 42;} fn change(data: [usize; 2], flag: bool) -> usize ensures(result == data[1]) {let r = &data[0]; let before = data[1]; let x = if flag {set(r)} else {()}; data[1]} fn main() -> usize ensures(result == 42) {change([7, 42], true)}";
        assert_eq!(verify(frame).unwrap().run().unwrap().to_string(), "42");
        let bad = "fn local(data: [usize; 1]) -> &usize borrows(&data[0]) {&data[0]}";
        assert!(verify(bad).is_err());
        let fake = "fn bad(data: &[usize; 2]) -> usize ensures(result == 0) {if *first(2, data) == 0 {*first(2, data)} else {*first(2, data)}}";
        assert!(verify(&format!("{declarations} {fake}")).is_err());
    }

    #[test]
    fn projected_effects_frame_siblings_and_preserve_array_views() {
        let helper = "fn set(data: &[usize; 2], i: usize) where(i < 2) modifies(&(*data)[i]) ensures((*data)[i] == 42) {(*data)[i] = 42;}";
        let source = format!("{helper} fn main() -> usize ensures(result == 49) {{let a: [usize; 2] = [1, 7]; set(&a, 0); a[0] + a[1]}}");
        assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "49");
        let bad = helper.replace("(*data)[i] = 42", "(*data)[1] = 42");
        assert!(verify(&bad).is_err());
        let source = "fn read(i: usize) -> usize where(i < 2) ensures(result == 42) {let a: [usize; 2] = [1, 7]; let r = &a[i]; a = [42, 42]; *r} fn main() -> usize {read(1)}";
        assert_eq!(verify(source).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn scalar_array_regions_preserve_aliases_and_replay_without_search() {
        let library = include_str!("../stdlib/array.evg");
        let source = format!(
            "{library} {}",
            include_str!("../examples/array_updates.evg")
        );
        let (program, bundle) = prove(&source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        let replayed = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(replayed.proof_search_count(), 0);
        assert_eq!(replayed.run().unwrap().to_string(), "42");

        // Both a constant cell and a symbolic cell retain their storage paths
        // when the call summary replaces known contents with an opaque array.
        let caller = "fn check(i: usize) -> usize where(i < 2) ensures(result == 42) {let a: [usize; 2] = [7, 9]; let constant = &a[0]; let dynamic = &a[i]; arrays::replace_pair(&a, 42, 42); proof constant_live: *constant == 42; *dynamic} fn main() -> usize {check(1)}";
        assert_eq!(
            verify(&format!("{library} {caller}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
        let nested = "fn read(i: usize) -> usize where(i < 2) ensures(result == 42) {let a: [[usize; 2]; 1] = [[7, 9]]; let r = &a[0][i]; a = [[42, 42]]; *r} fn main() -> usize {read(1)}";
        assert_eq!(verify(nested).unwrap().run().unwrap().to_string(), "42");
        let sibling = "type WithTag struct {data: [usize; 2], tag: usize} fn read(i: usize) -> usize where(i < 2) ensures(result == 42) {let p = WithTag {data: [42, 42], tag: 7}; let r = &p.data[i]; p.tag = 9; *r} fn main() -> usize {read(1)}";
        assert_eq!(verify(sibling).unwrap().run().unwrap().to_string(), "42");
        let caller = "type WithTag struct {data: [usize; 2], tag: usize} fn main() -> usize ensures(result == 42) {let p = WithTag {data: [7, 9], tag: 42}; arrays::replace_pair(&p.data, 1, 2); p.tag}";
        assert_eq!(
            verify(&format!("{library} {caller}"))
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
    }

    #[test]
    fn array_effects_do_not_gain_permissions_or_keep_old_contents() {
        let library = include_str!("../stdlib/array.evg");
        for caller in [
            // A projected grant cannot authorize an entire-array write.
            "fn bad(a: &[usize; 2]) modifies(&(*a)[0]) {arrays::replace_pair(a, 1, 2);}",
            // Writes follow entry indices even if the index variable is rebound.
            "fn bad(a: &[usize; 2], i: usize) where(i == 0) modifies(&(*a)[i]) {i = 1; (*a)[i] = 42;}",
            // Broad regions forget all contents outside the checked postcondition.
            "fn change(a: &[usize; 2]) modifies(a) {(*a)[1] = 9;} fn main() -> usize ensures(result == 42) {let a: [usize; 2] = [42, 7]; change(&a); a[0]}",
            // An independent readonly parameter cannot alias a written region.
            "fn change(a: &[usize; 2], r: &usize) modifies(a) {(*a)[0] = *r;} fn main() {let a: [usize; 2] = [42, 7]; change(&a, &a[1]);}",
            // A whole-array grant does not authorize writes to another parameter.
            "fn bad(a: &[usize; 2], b: &usize) modifies(a) {*b = 42;}",
            // Reference-containing elements require separate ownership semantics.
            "fn bad(a: &[&usize; 2]) modifies(a) {}",
        ] {
            assert!(verify(&format!("{library} {caller}")).is_err(), "accepted {caller}");
        }
    }

    #[test]
    fn multiple_scalar_writes_require_disjoint_actual_storage() {
        let library = include_str!("../stdlib/swap.evg");
        let source = format!(
            "{library}\n{}",
            include_str!("../examples/disjoint_writes.evg")
        );
        assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
        for body in [
            "let n: usize = 1; swap_usize(&n, &n); n",
            "let n: usize = 1; let r = &n; swap_usize(&n, r); n",
            "let a: [usize; 2] = [1, 2]; swap_usize(&a[0], &a[0]); a[0]",
        ] {
            let error = verify(&format!("{library} fn main() -> usize {{{body}}}")).unwrap_err();
            assert!(error.contains("overlaps"), "{error}");
        }
        for body in [
            "let a: [usize; 2] = [7, 42]; swap_usize(&a[0], &a[1]); a[0]",
            "let a: usize = usize::MAX; let b: usize = 42; swap_usize(&a, &b); a",
            "let p = Equal {left: 42, right: 42}; swap_usize(&p.left, &p.right); p.right",
        ] {
            let source = format!("{library} type Equal struct {{left: usize, right: usize}} where(left == right); fn main() -> usize ensures(result == 42) {{{body}}}");
            assert_eq!(verify(&source).unwrap().run().unwrap().to_string(), "42");
        }
        let copy = "fn copy(to: &usize, from: &usize) modifies(to) ensures(*to == old(*from) && *from == old(*from)) {*to = *from;}";
        assert!(verify(&format!(
            "{copy} fn main() -> usize {{let n: usize = 42; copy(&n, &n); n}}"
        ))
        .unwrap_err()
        .contains("overlaps"));
        assert!(verify(&format!("{copy} fn main() -> usize ensures(result == 42) {{let a: usize = 0; let b: usize = 42; copy(&a, &b); a}}")).is_ok());
        assert!(
            verify("fn duplicate(r: &usize) modifies(r, r) ensures(*r == 0) {*r = 0;}").is_ok()
        );
        assert!(verify("fn missing(r: &usize) modifies(no_such_param) {*r = 0;}").is_err());
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
            "fn wrapper(r: &usize, other: &usize) modifies(r) {*other = 1;}",
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
    fn runtime_divergence_is_inferred_and_cannot_become_proof_evidence() {
        let source = include_str!("../examples/partial_recursion.evg");
        let program = verify(source).unwrap();
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            program
                .potentially_diverging_functions()
                .collect::<Vec<_>>(),
            ["countdown", "main"]
        );
        assert!(program.trusted_assumptions().is_empty());
        let spin = "fn spin() -> usize ensures(false) {spin()}";
        assert!(verify(spin).is_ok());
        let chain = "fn first() -> usize ensures(false) {first()} fn second() -> usize ensures(false) {first()} fn third() -> usize ensures(false) {second()}";
        assert_eq!(
            verify(chain)
                .unwrap()
                .potentially_diverging_functions()
                .count(),
            3
        );
        let measured = "fn relay(n: usize) -> usize decreases(n) {spin()}";
        assert_eq!(
            verify(&format!("{spin} {measured}"))
                .unwrap()
                .potentially_diverging_functions()
                .count(),
            2
        );
        assert!(verify(include_str!("../examples/reject_divergent_proof.evg")).is_err());
        for observer in [
            "ideal fn unsound() -> nat {nat(spin())}",
            "fn unsound() -> usize {proof lie: spin() == 0; 0}",
            "fn unsound() -> usize {ideal let lie = spin(); 0}",
            "fn unsound() -> usize where(spin() == 0) {0}",
        ] {
            let error = verify(&format!("{spin} {observer}")).unwrap_err();
            assert!(error.contains("potentially divergent"), "{error}");
        }
        assert!(verify("ideal fn spin() -> nat {spin()}").is_err());
        assert!(verify("fn lie() -> usize ensures(false) {0}").is_err());
        assert!(verify(
            "fn lie(n: usize) -> usize ensures(false) {if n == 0 {0} else {lie(n - 1)}}"
        )
        .is_err());
        let namespaced = "fn spin() -> usize ensures(result == 42) {42} module looping {fn spin() -> usize ensures(false) {spin()}} ideal fn observe() -> nat ensures(result == 42) {nat(spin())}";
        assert_eq!(
            verify(namespaced)
                .unwrap()
                .potentially_diverging_functions()
                .collect::<Vec<_>>(),
            ["looping::spin"]
        );
        assert!(verify(&format!(
            "{namespaced} ideal fn bad() -> nat {{nat(looping::spin())}}"
        ))
        .is_err());
        assert!(verify("fn unsafe_loop(n: usize) -> usize {unsafe_loop(n + 1)}").is_err());
        let run = verify("fn spin() -> usize ensures(false) {spin()} fn main() -> usize {spin()}")
            .unwrap();
        assert!(run.run().unwrap_err().contains("execution"));
        // A proved decreasing, pure runtime function is usable as ideal data.
        let total = "fn count(n: usize) -> usize ensures(result == n) decreases(n) {if n == 0 {0} else {count(n - 1) + 1}} fn main() -> usize ensures(result == 42) {ideal let expected = nat(count(42)); proof established: expected == 42; 42}";
        let program = verify(total).unwrap();
        assert_eq!(program.potentially_diverging_functions().count(), 0);
        assert_eq!(program.run().unwrap().to_string(), "42");
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
    fn destructors_use_checked_scalar_helpers_without_gaining_external_effects() {
        let source = format!(
            "{} {}",
            include_str!("../stdlib/counter.evg"),
            include_str!("../examples/drop_helpers.evg")
        );
        let (program, bundle) = prove(&source).unwrap();
        let (value, events) = program.run_with_events().unwrap();
        assert_eq!(value.to_string(), "42");
        assert_eq!(events, ["drop Resource"]);
        let replayed = verify_with_certificate(&source, &bundle).unwrap();
        assert_eq!(replayed.proof_search_count(), 0);
        assert_eq!(replayed.run().unwrap().to_string(), "42");
        let swaps = format!("{} type Pair struct {{left: usize, right: usize}} impl Drop for Pair {{fn drop(self) {{let left = self.left; let right = self.right; swap_usize(&self.left, &self.right); proof swapped: self.left == right && self.right == left;}}}} fn main() -> usize {{let pair = Pair {{left: 1, right: 2}}; 42}}", include_str!("../stdlib/swap.evg"));
        assert_eq!(verify(&swaps).unwrap().run().unwrap().to_string(), "42");
        let returned = "fn reset(r: &usize) -> &usize modifies(r) borrows(r) ensures(*result == 0) {*r = 0; r} type Resource struct {value: usize} impl Drop for Resource {fn drop(self){let r = reset(&self.value); proof updated: *r == 0 && self.value == 0;}} fn main() -> usize {let r = Resource {value: 42}; 42}";
        assert_eq!(verify(returned).unwrap().run().unwrap().to_string(), "42");
    }

    #[test]
    fn destructor_helper_summaries_reject_hidden_cleanup_divergence_and_external_writes() {
        for source in [
            "type Resource struct {} fn hidden() -> usize {let another = Resource {}; 0} impl Drop for Resource {fn drop(self){let n = hidden();}}",
            "type Resource struct {} fn hidden() -> usize {let another = Resource {}; 0} fn wrapper() -> usize {hidden()} impl Drop for Resource {fn drop(self){let n = wrapper();}}",
            "fn forever() -> usize {forever()} type Resource struct {} impl Drop for Resource {fn drop(self){let n = forever();}}",
            "fn observe(r: &Resource) -> usize {0} type Resource struct {} impl Drop for Resource {fn drop(self){let n = observe(&self);}}",
        ] {
            let error = verify(source).unwrap_err();
            assert!(error.contains("ownership-free"), "{error}: {source}");
        }
        let library = include_str!("../stdlib/counter.evg");
        for body in [
            "let zero = counter_decrement(self.target);",
            "*self.target = 0;",
        ] {
            let source = format!("{library} type Resource struct {{target: &usize}} where(*target > 0); impl Drop for Resource {{fn drop(self){{{body}}}}}");
            let error = verify(&source).unwrap_err();
            assert!(
                error.contains("effect contract") || error.contains("modifies contract"),
                "{error}"
            );
        }
        let broken = format!("{library} type Resource struct {{value: usize}} where(value == 1); impl Drop for Resource {{fn drop(self){{let zero = counter_decrement(&self.value);}}}}");
        assert!(verify(&broken).is_err());
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
