//! Collect proof and value dependencies while keeping lexical variable names
//! separate from nominal type names. No declaration becomes an assumption here.

use super::*;
use crate::syntax::{Expr, Kind, Statement};

#[derive(Default)]
pub(super) struct Uses {
    pub(super) types: Names,
    pub(super) calls: Names,
    pub(super) owned: Names,
    work: usize,
}

impl Uses {
    fn tick(&mut self, depth: usize) -> Result<()> {
        self.work += 1;
        if depth >= 128 || self.work > 262_144 {
            return Err("declaration dependency expansion limit reached".into());
        }
        Ok(())
    }

    fn ty(&mut self, ty: &Type, bound: &Names, depth: usize) -> Result<()> {
        self.tick(depth)?;
        match ty {
            Type::Named(name) => {
                self.types.insert(name.clone());
            }
            Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) | Type::Shape(inner) => {
                self.ty(inner, bound, depth + 1)?
            }
            Type::Array(inner, count) => {
                self.ty(inner, bound, depth + 1)?;
                self.expression(count, bound, false, depth + 1)?;
            }
            Type::Union(members) => {
                for member in members {
                    self.ty(member, bound, depth + 1)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn owned_type(&mut self, ty: &Type, depth: usize) -> Result<()> {
        self.tick(depth)?;
        match ty {
            Type::Named(name) => {
                self.owned.insert(name.clone());
            }
            Type::Unique(inner) | Type::Shared(inner) | Type::Array(inner, _) => {
                self.owned_type(inner, depth + 1)?
            }
            Type::Union(members) => {
                for member in members {
                    self.owned_type(member, depth + 1)?;
                }
            }
            _ => {} // A reference or a shape does not own its pointee.
        }
        Ok(())
    }

    fn expression(
        &mut self,
        expression: &Expr,
        bound: &Names,
        runtime: bool,
        depth: usize,
    ) -> Result<()> {
        self.tick(depth)?;
        match &expression.kind {
            Kind::Type(ty) => self.ty(ty, bound, depth + 1)?,
            Kind::Name(name) if !bound.contains(name) => {
                self.types.insert(name.clone());
            }
            Kind::Call(name, args) => {
                self.calls.insert(name.clone());
                if matches!(name.as_str(), "shape" | "unique") && args.len() == 1 {
                    if let Some(ty) = args[0].literal_type() {
                        self.ty(&ty, bound, depth + 1)?;
                    }
                }
                for arg in args {
                    self.expression(arg, bound, runtime, depth + 1)?;
                }
            }
            Kind::Record(name, fields) => {
                self.types.insert(name.clone());
                if runtime {
                    self.owned.insert(name.clone());
                }
                for (_, value) in fields {
                    self.expression(value, bound, runtime, depth + 1)?;
                }
            }
            Kind::Unary(_, value) | Kind::Field(value, _) | Kind::FactAt(value, _) => {
                self.expression(value, bound, runtime, depth + 1)?
            }
            Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                self.expression(a, bound, runtime, depth + 1)?;
                self.expression(b, bound, runtime, depth + 1)?;
            }
            Kind::If(c, a, b) => {
                self.expression(c, bound, runtime, depth + 1)?;
                self.expression(a, bound, runtime, depth + 1)?;
                self.expression(b, bound, runtime, depth + 1)?;
            }
            Kind::Block(body, tail) => {
                let mut local = bound.clone();
                self.statements(body, &mut local, runtime, depth + 1)?;
                self.expression(tail, &local, runtime, depth + 1)?;
            }
            Kind::Array(items) => {
                for item in items {
                    self.expression(item, bound, runtime, depth + 1)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn statements(
        &mut self,
        statements: &[Statement],
        bound: &mut Names,
        runtime: bool,
        depth: usize,
    ) -> Result<()> {
        self.tick(depth)?;
        for statement in statements {
            match statement {
                Statement::Ideal(inner) => {
                    self.statements(std::slice::from_ref(inner), bound, false, depth + 1)?
                }
                Statement::Let { name, ty, value } => {
                    if let Some(ty) = ty {
                        self.ty(ty, bound, depth + 1)?;
                        if runtime {
                            self.owned_type(ty, depth + 1)?;
                        }
                    }
                    self.expression(value, bound, runtime, depth + 1)?;
                    bound.insert(name.clone());
                }
                Statement::Destructure {
                    record,
                    fields,
                    value,
                    ..
                } => {
                    self.types.insert(record.clone());
                    if runtime {
                        self.owned.insert(record.clone());
                    }
                    self.expression(value, bound, runtime, depth + 1)?;
                    bound.extend(fields.iter().map(|(_, name)| name.clone()));
                }
                Statement::Fact { name, value } => {
                    self.expression(value, bound, false, depth + 1)?;
                    bound.insert(name.clone());
                }
                Statement::Proof {
                    name, proposition, ..
                } => {
                    self.expression(proposition, bound, false, depth + 1)?;
                    bound.insert(name.clone());
                }
                Statement::Assign { target, value } => {
                    self.expression(target, bound, runtime, depth + 1)?;
                    self.expression(value, bound, runtime, depth + 1)?;
                }
                Statement::Effect(value) => self.expression(value, bound, runtime, depth + 1)?,
                Statement::While {
                    condition,
                    invariant,
                    modifies,
                    decreases,
                    body,
                    ..
                } => {
                    self.expression(condition, bound, runtime, depth + 1)?;
                    self.expression(invariant, bound, false, depth + 1)?;
                    if let Some(measure) = decreases {
                        self.expression(measure, bound, false, depth + 1)?;
                    }
                    for place in modifies {
                        self.expression(place, bound, false, depth + 1)?;
                    }
                    self.statements(body, &mut bound.clone(), runtime, depth + 1)?;
                }
                Statement::Update { places, body, .. } => {
                    for place in places {
                        self.expression(place, bound, false, depth + 1)?;
                    }
                    self.statements(body, &mut bound.clone(), runtime, depth + 1)?;
                }
            }
        }
        Ok(())
    }
}

pub(super) fn function(function: &Function) -> Result<Uses> {
    let mut uses = Uses::default();
    let mut bound = function
        .params
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<Names>();
    for (name, ty) in &function.params {
        uses.ty(ty, &bound, 0)?;
        if !function.ideal && !function.ideal_params.contains(name) {
            uses.owned_type(ty, 0)?;
        }
    }
    uses.ty(&function.ret, &bound, 0)?;
    if !function.ideal {
        uses.owned_type(&function.ret, 0)?;
    }
    let mut contracts = bound.clone();
    contracts.insert("result".into());
    for expression in function
        .pre
        .iter()
        .chain(function.post.iter())
        .chain(function.decreases.iter())
        .chain(function.modifies.iter())
    {
        uses.expression(expression, &contracts, false, 0)?;
    }
    for borrow in &function.borrows {
        uses.expression(&borrow.reference, &contracts, false, 0)?;
    }
    uses.statements(&function.body, &mut bound, !function.ideal, 0)?;
    uses.expression(&function.result, &bound, !function.ideal, 0)?;
    Ok(uses)
}

pub(super) fn record(record: &Struct) -> Result<Uses> {
    let mut uses = Uses::default();
    let mut bound = record
        .fields
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<Names>();
    bound.insert("self".into());
    for (_, ty) in &record.fields {
        uses.ty(ty, &bound, 0)?;
    }
    for (name, fact) in &record.facts {
        uses.expression(fact, &bound, false, 0)?;
        bound.insert(name.clone());
    }
    if let Some(invariant) = &record.invariant {
        uses.expression(invariant, &bound, false, 0)?;
    }
    Ok(uses)
}
