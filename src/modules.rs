//! Resolve lexical module names once, before type/proof checking. Modules do not
//! load files or supply trusted declarations; their functions are checked normally.
use crate::syntax::{Expr, Function, Kind, Program, Statement, Type};
use std::collections::BTreeSet;
fn defined(module: Option<&str>, name: &str) -> String {
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
    module: Option<&'a str>,
    types: &'a BTreeSet<String>,
    functions: &'a BTreeSet<String>,
}
impl Scope<'_> {
    fn ty(&self, ty: &mut Type) {
        match ty {
            Type::Named(name) => *name = resolve(self.module, name, self.types),
            Type::Ref(ty) => self.ty(ty),
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
                *name = resolve(self.module, name, self.types);
                for (_, value) in fields {
                    self.expr(value);
                }
            }
            Kind::Call(name, args) => {
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
            Kind::Array(items) => {
                for item in items {
                    self.expr(item);
                }
            }
            _ => {}
        }
    }
    fn statement(&self, statement: &mut Statement) {
        match statement {
            Statement::Let { ty, value, .. } => {
                if let Some(ty) = ty {
                    self.ty(ty);
                }
                self.expr(value);
            }
            Statement::Destructure { record, value, .. } => {
                *record = resolve(self.module, record, self.types);
                self.expr(value);
            }
            Statement::Fact { value, .. } | Statement::Effect(value) => self.expr(value),
            Statement::Proof { proposition, .. } => self.expr(proposition),
            Statement::Assign { target, value } => {
                self.expr(target);
                self.expr(value);
            }
            Statement::Update { lifts, body, .. } => {
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
        for e in [
            &mut function.pre,
            &mut function.post,
            &mut function.decreases,
            &mut function.borrows,
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
        .collect::<BTreeSet<_>>();
    let functions = program
        .functions
        .iter()
        .map(|f| defined(f.module.as_deref(), &f.name))
        .collect::<BTreeSet<_>>();
    for structure in &mut program.structs {
        let scope = Scope {
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
        let scope = Scope {
            module: module.as_deref(),
            types: &types,
            functions: &functions,
        };
        function.name = defined(scope.module, &function.name);
        scope.function(function);
    }
    for (target, function) in &mut program.destructors {
        let module = function.module.clone();
        let scope = Scope {
            module: module.as_deref(),
            types: &types,
            functions: &functions,
        };
        *target = resolve(scope.module, target, &types);
        function.name = format!("evg_drop_{target}");
        function.drop_target = Some(target.clone());
        scope.function(function);
    }
}
