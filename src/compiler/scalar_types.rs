//! Resolve checked scalar type aliases to the backend's supported primitives.
//! Representation construction is literal; it cannot manufacture pointer access.

use crate::syntax::{Expr, Kind, MachineInt, Program, Statement, Type};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

pub(super) fn lower(program: &mut Program) -> Result<()> {
    let mut aliases = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let profile = program.functions.is_empty()
        && program.structs.is_empty()
        && program.destructors.is_empty();
    for definition in &program.scalar_types {
        definition.validate()?;
        let qualified = definition.module.as_ref().map_or_else(
            || definition.name.clone(),
            |m| format!("{m}::{}", definition.name),
        );
        if !seen.insert(qualified.clone())
            || program.structs.iter().any(|s| s.name == qualified)
            || program.functions.iter().any(|f| f.name == qualified)
        {
            return Err(format!(
                "line {}: duplicate type {qualified}",
                definition.line
            ));
        }
        let ty = super::target::representation_type(&definition.represents)?;
        let Some(ty) = ty else {
            if profile
                && definition.module.as_deref() == Some("x86_64")
                && definition.name == "pointer"
            {
                continue;
            }
            return Err("pointer representations describe target storage; make_type cannot fabricate reference or allocation authority".into());
        };
        if let Some(integer) = MachineInt::parse(&definition.name) {
            if ty != Type::Machine(integer) {
                return Err(format!(
                    "{} has a different declared integer representation",
                    definition.name
                ));
            }
        } else if definition.name == "bool" {
            if ty != Type::Bool {
                return Err("bool requires repr::Boolean".into());
            }
        } else if definition.name == "unit" {
            if ty != Type::Unit {
                return Err("unit requires repr::Unit".into());
            }
        } else if !definition
            .name
            .starts_with(|c: char| c.is_ascii_uppercase())
        {
            return Err("custom scalar alias names must begin with an uppercase letter".into());
        }
        if !profile {
            let layout = super::target::native()?.scalar(&ty)?;
            if layout.size != definition.size || layout.align != definition.align {
                return Err(format!(
                    "{qualified}: scalar representation does not match the active target layout"
                ));
            }
        }
        aliases.insert(qualified, ty);
    }
    let aliases = Aliases(aliases);
    for structure in &mut program.structs {
        for (_, ty) in &mut structure.fields {
            aliases.ty(ty, structure.module.as_deref());
        }
        for (_, fact) in &mut structure.facts {
            aliases.expr(fact, structure.module.as_deref());
        }
        if let Some(invariant) = &mut structure.invariant {
            aliases.expr(invariant, structure.module.as_deref());
        }
    }
    for function in program
        .functions
        .iter_mut()
        .chain(program.destructors.iter_mut().map(|(_, f)| f))
    {
        let module = function.module.as_deref();
        for (_, ty) in &mut function.params {
            aliases.ty(ty, module);
        }
        aliases.ty(&mut function.ret, module);
        for expression in function
            .pre
            .iter_mut()
            .chain(function.post.iter_mut())
            .chain(function.decreases.iter_mut())
            .chain(function.modifies.iter_mut())
        {
            aliases.expr(expression, module);
        }
        for borrow in &mut function.borrows {
            aliases.expr(&mut borrow.reference, module);
        }
        for statement in &mut function.body {
            aliases.statement(statement, module);
        }
        aliases.expr(&mut function.result, module);
    }
    Ok(())
}

struct Aliases(BTreeMap<String, Type>);

impl Aliases {
    fn lookup(&self, name: &str, module: Option<&str>) -> Option<&Type> {
        module
            .and_then(|module| self.0.get(&format!("{module}::{name}")))
            .or_else(|| self.0.get(name))
    }

    fn ty(&self, ty: &mut Type, module: Option<&str>) {
        match ty {
            Type::Named(name) => {
                if let Some(value) = self.0.get(name) {
                    *ty = value.clone();
                }
            }
            Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) | Type::Shape(inner) => {
                self.ty(inner, module)
            }
            Type::Union(members) => {
                for member in members {
                    self.ty(member, module);
                }
            }
            Type::Array(inner, count) => {
                self.ty(inner, module);
                self.expr(count, module);
            }
            _ => {}
        }
    }

    fn expr(&self, expr: &mut Expr, module: Option<&str>) {
        match &mut expr.kind {
            Kind::Call(name, args) => {
                for arg in args {
                    self.expr(arg, module);
                }
                if let Some(Type::Machine(integer)) = self.lookup(name, module) {
                    *name = format!("{}{}", if integer.signed { 'i' } else { 'u' }, integer.bits);
                }
            }
            Kind::FactAt(base, field) => {
                self.expr(base, module);
                if let Kind::Name(name) = &base.kind {
                    if let Some(Type::Machine(integer)) = self.lookup(name, module) {
                        let (low, high) = integer.bounds();
                        let value = match field.as_str() {
                            "MAX" | "max" => high,
                            "MIN" | "min" => low,
                            _ => return,
                        };
                        expr.kind = Kind::Constant(*integer, value);
                    }
                }
            }
            Kind::Unary(_, value) | Kind::Field(value, _) => self.expr(value, module),
            Kind::Binary(_, left, right) | Kind::Index(left, right) => {
                self.expr(left, module);
                self.expr(right, module);
            }
            Kind::If(condition, left, right) => {
                self.expr(condition, module);
                self.expr(left, module);
                self.expr(right, module);
            }
            Kind::Block(body, tail) => {
                for statement in body {
                    self.statement(statement, module);
                }
                self.expr(tail, module);
            }
            Kind::Array(values) => {
                for value in values {
                    self.expr(value, module);
                }
            }
            Kind::Record(_, fields) => {
                for (_, value) in fields {
                    self.expr(value, module);
                }
            }
            _ => {}
        }
    }

    fn statement(&self, statement: &mut Statement, module: Option<&str>) {
        match statement {
            Statement::Ideal(inner) => self.statement(inner, module),
            Statement::Let { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty, module);
                }
                self.expr(value, module);
            }
            Statement::Destructure { value, .. }
            | Statement::Fact { value, .. }
            | Statement::Effect(value) => self.expr(value, module),
            Statement::Proof { proposition, .. } => self.expr(proposition, module),
            Statement::Assign { target, value } => {
                self.expr(target, module);
                self.expr(value, module);
            }
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                ..
            } => {
                self.expr(condition, module);
                self.expr(invariant, module);
                if let Some(measure) = decreases {
                    self.expr(measure, module);
                }
                for effect in modifies {
                    self.expr(effect, module);
                }
                for item in body {
                    self.statement(item, module);
                }
            }
            Statement::Update { places, body, .. } => {
                for place in places {
                    self.expr(place, module);
                }
                for statement in body {
                    self.statement(statement, module);
                }
            }
        }
    }
}
