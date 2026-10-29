//! Resolve checked scalar type aliases to the backend's supported primitives.
//! Representation construction is literal; it cannot manufacture pointer access.

use crate::syntax::{Expr, Kind, Program, Statement, Type};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

pub(super) fn lower(program: &mut Program, target: crate::compiler::TargetKind) -> Result<()> {
    let mut aliases = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let profile = program.functions.is_empty()
        && program.structs.is_empty()
        && program.destructors.is_empty()
        && program.generics.is_empty();
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
        let Some(mut ty) = ty else {
            if profile
                && definition.module.as_deref() == Some(target.module())
                && definition.name == "pointer"
            {
                continue;
            }
            return Err("pointer representations describe target storage; make_type cannot fabricate reference or allocation authority".into());
        };
        if let Some(integer) = target.integer(&definition.name) {
            if ty != Type::Machine(integer.representation()) {
                return Err(format!(
                    "{} has a different declared integer representation",
                    definition.name
                ));
            }
            ty = Type::Machine(integer);
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
            let layout = target.profile()?.scalar(&ty)?;
            if layout.size != definition.size || layout.align != definition.align {
                return Err(format!(
                    "{qualified}: scalar representation does not match the active target layout"
                ));
            }
        }
        aliases.insert(qualified, ty);
    }
    let aliases = Aliases {
        values: &aliases,
        bound: BTreeSet::new(),
    };
    for structure in &mut program.structs {
        aliases.record(structure);
    }
    for function in program
        .functions
        .iter_mut()
        .chain(program.destructors.iter_mut().map(|(_, f)| f))
    {
        aliases.function(function);
    }
    for declaration in &mut program.generics {
        let placeholder_self = matches!(
            declaration,
            crate::syntax::GenericDeclaration::Implementation(_)
        );
        let parameters = declaration.parameters_mut();
        let mut scope = Aliases {
            values: aliases.values,
            bound: parameters.iter().map(|p| p.name().to_owned()).collect(),
        };
        if placeholder_self {
            scope.bound.insert("Self".into());
        }
        for parameter in parameters {
            match parameter {
                crate::syntax::GenericParameter::Type { default, .. } => {
                    if let Some(ty) = default {
                        scope.ty(ty, None);
                    }
                }
                crate::syntax::GenericParameter::Const { ty, default, .. } => {
                    scope.ty(ty, None);
                    if let Some(value) = default {
                        scope.expr(value, None);
                    }
                }
            }
        }
        match declaration {
            crate::syntax::GenericDeclaration::Implementation(implementation) => {
                scope.ty(&mut implementation.target, implementation.module.as_deref());
                for function in &mut implementation.functions {
                    scope.function(function);
                }
            }
            crate::syntax::GenericDeclaration::Record { definition, .. } => {
                scope.record(definition)
            }
            crate::syntax::GenericDeclaration::Function { definition, .. } => {
                scope.function(definition)
            }
        }
    }
    Ok(())
}

struct Aliases<'a> {
    values: &'a BTreeMap<String, Type>,
    bound: BTreeSet<String>,
}

impl Aliases<'_> {
    fn record(&self, structure: &mut crate::syntax::Struct) {
        for (_, ty) in &mut structure.fields {
            self.ty(ty, structure.module.as_deref());
        }
        for (_, fact) in &mut structure.facts {
            self.expr(fact, structure.module.as_deref());
        }
        if let Some(invariant) = &mut structure.invariant {
            self.expr(invariant, structure.module.as_deref());
        }
    }

    fn function(&self, function: &mut crate::syntax::Function) {
        let module = function.module.as_deref();
        for (_, ty) in &mut function.params {
            self.ty(ty, module);
        }
        self.ty(&mut function.ret, module);
        for expression in function
            .pre
            .iter_mut()
            .chain(function.post.iter_mut())
            .chain(function.decreases.iter_mut())
            .chain(function.modifies.iter_mut())
        {
            self.expr(expression, module);
        }
        for borrow in &mut function.borrows {
            self.expr(&mut borrow.reference, module);
        }
        for statement in &mut function.body {
            self.statement(statement, module);
        }
        self.expr(&mut function.result, module);
    }

    fn arguments(&self, arguments: &mut [crate::syntax::GenericArgument], module: Option<&str>) {
        for argument in arguments {
            match argument {
                crate::syntax::GenericArgument::Type(ty) => self.ty(ty, module),
                crate::syntax::GenericArgument::Const(value) => self.expr(value, module),
            }
        }
    }
    fn lookup(&self, name: &str, module: Option<&str>) -> Option<&Type> {
        if self.bound.contains(name) {
            return None;
        }
        module
            .and_then(|module| self.values.get(&format!("{module}::{name}")))
            .or_else(|| self.values.get(name))
    }

    fn ty(&self, ty: &mut Type, module: Option<&str>) {
        match ty {
            Type::Apply(_, arguments) => self.arguments(arguments, module),
            Type::Named(name) => {
                if self.bound.contains(name) {
                    return;
                }
                if let Some(value) = self.values.get(name) {
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
            Kind::Type(ty) => self.ty(ty, module),
            Kind::Generic {
                arguments, value, ..
            } => {
                self.arguments(arguments, module);
                self.expr(value, module);
            }
            Kind::Call(name, args) => {
                for arg in args {
                    self.expr(arg, module);
                }
                if let Some(Type::Machine(integer)) = self.lookup(name, module) {
                    *name = integer.primitive_name();
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
            Statement::Destructure {
                arguments, value, ..
            } => {
                self.arguments(arguments, module);
                self.expr(value, module);
            }
            Statement::Fact { value, .. } | Statement::Effect(value) => self.expr(value, module),
            Statement::Proof { proposition, .. } => self.expr(proposition, module),
            Statement::Assign {
                target,
                value,
                starts,
            } => {
                self.expr(target, module);
                self.expr(value, module);
                for source in starts {
                    self.expr(source, module);
                }
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
