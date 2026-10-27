//! Resolve lexical module names once, before type/proof checking. Modules do not
//! load files or supply trusted declarations; their functions are checked normally.

use crate::syntax::{Expr, Function, Kind, Program, Statement, Type};
use std::collections::BTreeSet;

fn defined(module: Option<&str>, name: &str) -> String {
    if module == Some("main") && name == "main" {
        return "main".into();
    }
    module.map_or_else(|| name.to_owned(), |m| format!("{m}::{name}"))
}

fn resolve(module: Option<&str>, name: &str, names: &BTreeSet<String>) -> String {
    if name.contains("::") {
        return name.to_owned();
    }
    let local = defined(module, name);
    if names.contains(&local) {
        local
    } else {
        name.to_owned()
    }
}

struct Scope<'a> {
    self_type: Option<&'a str>,
    module: Option<&'a str>,
    types: &'a BTreeSet<String>,
    functions: &'a BTreeSet<String>,
}

impl Scope<'_> {
    fn ty(&self, ty: &mut Type) {
        match ty {
            Type::Named(name) => {
                if name == "Self" {
                    if let Some(target) = self.self_type {
                        *name = target.to_owned();
                        return;
                    }
                }
                *name = resolve(self.module, name, self.types);
            }
            Type::Ref(ty) | Type::Unique(ty) | Type::Shared(ty) | Type::Shape(ty) => self.ty(ty),
            Type::Union(members) => {
                for member in members {
                    self.ty(member);
                }
            }
            Type::Array(ty, len) => {
                self.ty(ty);
                self.expr(len);
            }
            _ => {}
        }
    }

    fn expr(&self, expression: &mut Expr) {
        match &mut expression.kind {
            Kind::Record(name, fields) => {
                if name == "Self" {
                    if let Some(target) = self.self_type {
                        *name = target.to_owned();
                    }
                }
                *name = resolve(self.module, name, self.types);
                for (_, value) in fields {
                    self.expr(value);
                }
            }
            Kind::Call(name, args) => {
                if name == "shape" {
                    for argument in args {
                        self.type_expression(argument);
                    }
                    return;
                }
                if let Some((base, member)) = name.rsplit_once("::") {
                    let target = if base == "Self" {
                        self.self_type.map(str::to_owned)
                    } else {
                        let target = resolve(self.module, base, self.types);
                        self.types.contains(&target).then_some(target)
                    };
                    if let Some(target) = target {
                        *name = format!("{target}::{member}");
                    }
                }
                *name = resolve(self.module, name, self.functions);
                for arg in args {
                    self.expr(arg);
                }
            }
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => self.expr(e),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => {
                self.expr(a);
                self.expr(b);
            }
            Kind::If(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            Kind::Block(body, tail) => {
                for statement in body {
                    self.statement(statement);
                }
                self.expr(tail);
            }
            Kind::Array(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            _ => {}
        }
    }

    fn type_expression(&self, expression: &mut Expr) {
        match &mut expression.kind {
            Kind::Name(name) => {
                let mut ty = Type::Named(name.clone());
                self.ty(&mut ty);
                if let Type::Named(qualified) = ty {
                    *name = qualified;
                }
            }
            Kind::Unary(_, inner) => self.type_expression(inner),
            Kind::Call(_, arguments) => {
                for argument in arguments {
                    self.type_expression(argument);
                }
            }
            _ => {}
        }
    }

    fn statement(&self, statement: &mut Statement) {
        match statement {
            Statement::Ideal(binding) => self.statement(binding),
            Statement::Let { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.expr(value);
            }
            Statement::Destructure { record, value, .. } => {
                let mut ty = Type::Named(record.clone());
                self.ty(&mut ty);
                if let Type::Named(name) = ty {
                    *record = name;
                }
                self.expr(value);
            }
            Statement::Fact { value, .. } | Statement::Effect(value) => self.expr(value),
            Statement::Proof { proposition, .. } => self.expr(proposition),
            Statement::Assign { target, value } => {
                self.expr(target);
                self.expr(value);
            }
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                ..
            } => {
                self.expr(condition);
                self.expr(invariant);
                if let Some(measure) = decreases {
                    self.expr(measure);
                }
                for effect in modifies {
                    self.expr(effect);
                }
                for item in body {
                    self.statement(item);
                }
            }
            Statement::Update {
                places,
                lifts,
                body,
                ..
            } => {
                for place in places {
                    self.expr(place);
                }
                for selector in lifts {
                    if let Some((ty, fact)) = selector.rsplit_once("::") {
                        *selector = format!("{}::{fact}", resolve(self.module, ty, self.types));
                    }
                }
                for statement in body {
                    self.statement(statement);
                }
            }
        }
    }

    fn function(&self, function: &mut Function) {
        for (_, ty) in &mut function.params {
            self.ty(ty);
        }
        self.ty(&mut function.ret);
        for effect in &mut function.modifies {
            self.expr(effect);
        }
        for alias in &mut function.borrows {
            self.expr(&mut alias.reference);
        }
        for e in [
            &mut function.pre,
            &mut function.post,
            &mut function.decreases,
        ]
        .into_iter()
        .flatten()
        {
            self.expr(e);
        }
        for statement in &mut function.body {
            self.statement(statement);
        }
        self.expr(&mut function.result);
    }
}

pub(crate) fn qualify(program: &mut Program) {
    let types = program
        .structs
        .iter()
        .map(|s| defined(s.module.as_deref(), &s.name))
        .chain(
            program
                .scalar_types
                .iter()
                .map(|s| defined(s.module.as_deref(), &s.name)),
        )
        .collect::<BTreeSet<_>>();
    let functions = program
        .functions
        .iter()
        .map(|f| {
            f.impl_target.as_ref().map_or_else(
                || defined(f.module.as_deref(), &f.name),
                |target| {
                    format!(
                        "{}::{}",
                        resolve(f.module.as_deref(), target, &types),
                        f.name
                    )
                },
            )
        })
        .chain(
            program
                .scalar_types
                .iter()
                .map(|s| defined(s.module.as_deref(), &s.name)),
        )
        .collect::<BTreeSet<_>>();
    for implementation in &mut program.copy_impls {
        implementation.target = resolve(
            implementation.module.as_deref(),
            &implementation.target,
            &types,
        );
    }
    for structure in &mut program.structs {
        let scope = Scope {
            self_type: None,
            module: structure.module.as_deref(),
            types: &types,
            functions: &functions,
        };
        structure.name = defined(scope.module, &structure.name);
        for (_, ty) in &mut structure.fields {
            scope.ty(ty);
        }
        for (_, fact) in &mut structure.facts {
            scope.expr(fact);
        }
        if let Some(invariant) = &mut structure.invariant {
            scope.expr(invariant);
        }
    }
    for function in &mut program.functions {
        let module = function.module.clone();
        let target = function
            .impl_target
            .as_ref()
            .map(|target| resolve(module.as_deref(), target, &types));
        let scope = Scope {
            self_type: target.as_deref(),
            module: module.as_deref(),
            types: &types,
            functions: &functions,
        };
        function.name = target.as_ref().map_or_else(
            || defined(scope.module, &function.name),
            |target| format!("{target}::{}", function.name),
        );
        function.impl_target = target.clone();
        scope.function(function);
    }
    for (target, function) in &mut program.destructors {
        let module = function.module.clone();
        *target = resolve(module.as_deref(), target, &types);
        let scope = Scope {
            self_type: Some(target.as_str()),
            module: module.as_deref(),
            types: &types,
            functions: &functions,
        };
        function.name = format!("evg_drop_{target}");
        function.drop_target = Some(target.clone());
        scope.function(function);
    }
}
