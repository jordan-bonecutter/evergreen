//! Elaborate field autodereferencing into ordinary checked dereferences.
//! Shape inference here grants no authority: the verifier checks the result.

use crate::syntax::{Expr, Function, Kind, MachineInt, Program, Statement, Type};
use std::collections::BTreeMap;

type Scope = BTreeMap<String, Type>;

pub(super) fn expand(program: &mut Program) {
    let shapes = Shapes {
        records: program
            .structs
            .iter()
            .map(|s| (s.name.clone(), s.fields.clone()))
            .collect(),
        returns: program
            .functions
            .iter()
            .map(|f| (f.name.clone(), f.ret.clone()))
            .collect(),
    };
    for record in &mut program.structs {
        let mut scope: Scope = record.fields.iter().cloned().collect();
        scope.insert("self".into(), Type::Named(record.name.clone()));
        for (_, ty) in &mut record.fields {
            shapes.ty(ty, &scope);
        }
        for (_, fact) in &mut record.facts {
            shapes.expr(fact, &scope, None);
        }
        if let Some(invariant) = &mut record.invariant {
            shapes.expr(invariant, &scope, None);
        }
    }
    for function in &mut program.functions {
        shapes.function(function);
    }
    for (_, function) in &mut program.destructors {
        shapes.function(function);
    }
}

struct Shapes {
    records: BTreeMap<String, Vec<(String, Type)>>,
    returns: Scope,
}

impl Shapes {
    fn ty(&self, ty: &mut Type, scope: &Scope) {
        match ty {
            Type::Ref(inner) | Type::Plane(inner) => self.ty(inner, scope),
            Type::Array(inner, count) => {
                self.ty(inner, scope);
                self.expr(count, scope, None);
            }
            _ => {}
        }
    }

    fn function(&self, function: &mut Function) {
        let mut scope: Scope = function.params.iter().cloned().collect();
        for (_, ty) in &mut function.params {
            self.ty(ty, &scope);
        }
        self.ty(&mut function.ret, &scope);
        for expr in function.pre.iter_mut().chain(function.decreases.iter_mut()) {
            self.expr(expr, &scope, None);
        }
        for expr in &mut function.modifies {
            self.expr(expr, &scope, None);
        }
        let mut contracts = scope.clone();
        contracts.insert("result".into(), function.ret.clone());
        if let Some(post) = &mut function.post {
            self.expr(post, &contracts, None);
        }
        for borrow in &mut function.borrows {
            self.expr(&mut borrow.reference, &contracts, None);
        }
        for statement in &mut function.body {
            self.statement(statement, &mut scope);
        }
        self.expr(&mut function.result, &scope, Some(&function.ret));
    }

    fn statement(&self, statement: &mut Statement, scope: &mut Scope) {
        match statement {
            Statement::Ideal(inner) => self.statement(inner, scope),
            Statement::Let { name, ty, value } => {
                if let Some(ty) = ty {
                    self.ty(ty, scope);
                }
                let inferred = self.expr(value, scope, ty.as_ref());
                if let Some(ty) = ty.clone().or(inferred) {
                    scope.insert(name.clone(), ty);
                }
            }
            Statement::Destructure {
                record,
                fields,
                value,
            } => {
                self.expr(value, scope, Some(&Type::Named(record.clone())));
                if let Some(record) = self.records.get(record) {
                    for (field, name) in fields {
                        if let Some((_, ty)) = record.iter().find(|(n, _)| n == field) {
                            scope.insert(name.clone(), ty.clone());
                        }
                    }
                }
            }
            Statement::Assign { target, value } => {
                let ty = self.expr(target, scope, None);
                self.expr(value, scope, ty.as_ref());
            }
            Statement::Effect(value) | Statement::Fact { value, .. } => {
                self.expr(value, scope, None);
            }
            Statement::Proof { proposition, .. } => {
                self.expr(proposition, scope, None);
            }
            Statement::Update { places, body, .. } => {
                for place in places {
                    self.expr(place, scope, None);
                }
                let mut local = scope.clone();
                for statement in body {
                    self.statement(statement, &mut local);
                }
            }
        }
    }

    fn expr(&self, expr: &mut Expr, scope: &Scope, expected: Option<&Type>) -> Option<Type> {
        match &mut expr.kind {
            Kind::Name(name) => scope.get(name).cloned(),
            Kind::Record(name, fields) => {
                for (field, value) in fields {
                    let hint = self
                        .records
                        .get(name)
                        .and_then(|r| r.iter().find(|(n, _)| n == field))
                        .map(|(_, t)| t);
                    self.expr(value, scope, hint);
                }
                Some(Type::Named(name.clone()))
            }
            Kind::Field(base, name) => {
                let mut ty = self.expr(base, scope, None)?;
                while let Type::Ref(inner) | Type::Plane(inner) = ty {
                    let operand = (**base).clone();
                    **base = Expr {
                        line: operand.line,
                        kind: Kind::Unary("*".into(), Box::new(operand)),
                    };
                    ty = *inner;
                }
                let Type::Named(record) = ty else {
                    return None;
                };
                self.records
                    .get(&record)?
                    .iter()
                    .find(|(n, _)| n == name)
                    .map(|(_, t)| t.clone())
            }
            Kind::Unary(op, value) => {
                let ty = self.expr(value, scope, None)?;
                match (op.as_str(), ty) {
                    ("&", ty) => Some(Type::Ref(Box::new(ty))),
                    ("*", Type::Ref(inner) | Type::Plane(inner)) => Some(*inner),
                    ("!", _) => Some(Type::Bool),
                    (_, ty) => Some(ty),
                }
            }
            Kind::Index(base, index) => {
                let ty = self.expr(base, scope, None);
                self.expr(index, scope, None);
                match ty {
                    Some(Type::Array(inner, _)) => Some(*inner),
                    _ => None,
                }
            }
            Kind::Call(name, args) => {
                let mut first = None;
                for (i, arg) in args.iter_mut().enumerate() {
                    let ty = self.expr(arg, scope, None);
                    if i == 0 {
                        first = ty;
                    }
                }
                if let Some(machine) = MachineInt::parse(name) {
                    return Some(Type::Machine(machine));
                }
                match name.as_str() {
                    "old" | "move" => first,
                    "int" => Some(Type::Int),
                    "nat" => Some(Type::Nat),
                    "alloc" => expected.cloned().or_else(|| {
                        let payload = if args.len() == 2 {
                            let element = self.expr(&mut args[1], scope, None)?;
                            Type::Array(Box::new(element), Box::new(args[0].clone()))
                        } else {
                            first?
                        };
                        Some(Type::Plane(Box::new(payload)))
                    }),
                    _ => self.returns.get(name).cloned(),
                }
            }
            Kind::Array(items) => {
                let hint = match expected {
                    Some(Type::Array(inner, _)) => Some(inner.as_ref()),
                    _ => None,
                };
                let mut element = hint.cloned();
                for item in items.iter_mut() {
                    let ty = self.expr(item, scope, hint);
                    if element.is_none() {
                        element = ty;
                    }
                }
                element.map(|t| {
                    Type::Array(
                        Box::new(t),
                        Box::new(Expr {
                            kind: Kind::Number(items.len() as i128),
                            line: expr.line,
                        }),
                    )
                })
            }
            Kind::If(condition, left, right) => {
                self.expr(condition, scope, Some(&Type::Bool));
                let ty = self.expr(left, scope, expected);
                self.expr(right, scope, expected);
                ty
            }
            Kind::Binary(op, left, right) => {
                let ty = self.expr(left, scope, None);
                self.expr(right, scope, None);
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "=>"
                ) {
                    Some(Type::Bool)
                } else {
                    ty
                }
            }
            Kind::FactAt(place, _) => {
                self.expr(place, scope, None);
                Some(Type::Bool)
            }
            Kind::Constant(machine, _) => Some(Type::Machine(*machine)),
            Kind::Number(_) => expected.cloned(),
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Unit => Some(Type::Unit),
        }
    }
}
