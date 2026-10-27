//! Elaborate field autodereferencing into ordinary checked dereferences.
//! Shape inference here grants no authority: the verifier checks the result.

use crate::syntax::{Expr, Function, Kind, MachineInt, MethodReceiver, Program, Statement, Type};
use std::collections::BTreeMap;

type Scope = BTreeMap<String, Type>;

pub(super) fn expand(program: &mut Program) {
    let shapes = Shapes {
        records: program
            .structs
            .iter()
            .map(|s| (s.name.clone(), s.fields.clone()))
            .collect(),
        methods: program
            .functions
            .iter()
            .filter_map(|f| {
                Some((
                    (
                        f.impl_target.clone()?,
                        f.name.rsplit("::").next()?.to_owned(),
                    ),
                    (f.name.clone(), f.ret.clone(), f.receiver?),
                ))
            })
            .collect(),
        parameters: program
            .functions
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    f.params
                        .iter()
                        .filter(|(name, _)| !f.ideal_params.contains(name))
                        .cloned()
                        .collect(),
                )
            })
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
    parameters: BTreeMap<String, Vec<(String, Type)>>,
    methods: BTreeMap<(String, String), (String, Type, MethodReceiver)>,
}

impl Shapes {
    // Fill runtime lengths from the actual array's type. This only proposes
    // ordinary expressions; the verifier still proves every dependent bound.
    fn infer_lengths(
        &self,
        name: &str,
        args: &mut Vec<Expr>,
        types: &[Option<Type>],
        scope: &Scope,
    ) {
        fn extent(ty: &Type) -> Option<&Expr> {
            match ty {
                Type::Array(_, count) => Some(count),
                Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) => extent(inner),
                _ => None,
            }
        }
        fn stable(e: &Expr, scope: &Scope) -> bool {
            match &e.kind {
                Kind::Name(n) => scope.contains_key(n),
                Kind::Number(_) | Kind::Constant(..) => true,
                Kind::Field(base, _) => stable(base, scope),
                Kind::Unary(op, base) if op == "*" => stable(base, scope),
                Kind::Binary(op, a, b) if matches!(op.as_str(), "+" | "-" | "*") => {
                    stable(a, scope) && stable(b, scope)
                }
                _ => false,
            }
        }
        let Some(parameters) = self.parameters.get(name) else {
            return;
        };
        if args.len() >= parameters.len() {
            return;
        }
        let inferred = parameters.iter().filter(|(name, ty)| {
            *ty == Type::Machine(MachineInt::parse("usize").expect("usize")) && parameters.iter().any(|(_, t)| matches!(extent(t).map(|e| &e.kind), Some(Kind::Name(n)) if n == name))
        }).map(|(n, _)| n.clone()).collect::<Vec<_>>();
        if args.len() + inferred.len() != parameters.len() {
            return;
        }
        let supplied = parameters
            .iter()
            .filter(|(n, _)| !inferred.contains(n))
            .zip(types);
        let mut lengths = BTreeMap::new();
        for ((_, parameter), actual) in supplied {
            let Some(Kind::Name(n)) = extent(parameter).map(|e| &e.kind) else {
                continue;
            };
            if !inferred.contains(n) {
                continue;
            }
            let Some(actual) = actual.as_ref().and_then(extent) else {
                continue;
            };
            if stable(actual, scope) {
                lengths.entry(n.clone()).or_insert_with(|| actual.clone());
            }
        }
        if inferred.iter().any(|n| !lengths.contains_key(n)) {
            return;
        }
        let mut original = std::mem::take(args).into_iter();
        for (n, _) in parameters {
            args.push(if let Some(length) = lengths.get(n) {
                length.clone()
            } else {
                original.next().expect("matched supplied arity")
            });
        }
    }

    fn ty(&self, ty: &mut Type, scope: &Scope) {
        match ty {
            Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) | Type::Shape(inner) => {
                self.ty(inner, scope)
            }
            Type::Union(members) => {
                for member in members {
                    self.ty(member, scope);
                }
            }
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
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                ..
            } => {
                self.expr(condition, scope, Some(&Type::Bool));
                self.expr(invariant, scope, Some(&Type::Bool));
                if let Some(measure) = decreases {
                    self.expr(measure, scope, None);
                }
                for effect in modifies {
                    self.expr(effect, scope, None);
                }
                let mut local = scope.clone();
                for item in body {
                    self.statement(item, &mut local);
                }
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
            Kind::Bytes(bytes) => Some(Type::bytes(bytes.len(), expr.line)),
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
                while let Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) = ty {
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
                    ("*", Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner)) => {
                        Some(*inner)
                    }
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
                let mut types = Vec::new();
                for (i, arg) in args.iter_mut().enumerate() {
                    let ty = self.expr(arg, scope, None);
                    if i == 0 {
                        first = ty.clone();
                    }
                    types.push(ty);
                }
                self.infer_lengths(name, args, &types, scope);
                if let Some(method) = name.strip_prefix("evg_method_") {
                    let mut ty = first?;
                    let mut receiver = args.first()?.clone();
                    while let Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) = ty {
                        let line = receiver.line;
                        receiver = Expr {
                            line,
                            kind: Kind::Unary("*".into(), Box::new(receiver)),
                        };
                        ty = *inner;
                    }
                    let Type::Named(target) = ty else {
                        return None;
                    };
                    let (function, result, kind) =
                        self.methods.get(&(target, method.to_owned()))?;
                    if *kind == MethodReceiver::Reference {
                        receiver = Expr {
                            line: receiver.line,
                            kind: Kind::Unary("&".into(), Box::new(receiver)),
                        };
                    }
                    args[0] = receiver;
                    *name = function.clone();
                    self.infer_lengths(name, args, &types, scope);
                    return Some(result.clone());
                }
                if let Some(machine) = MachineInt::parse(name) {
                    return Some(Type::Machine(machine));
                }
                match name.as_str() {
                    "owner_count" => Some(Type::Nat),
                    "old" | "move" => first,
                    "integer" => Some(Type::Int),
                    "nat" => Some(Type::Nat),
                    "alloc" => expected.cloned().or_else(|| {
                        let payload = if args.len() == 2 {
                            let element = self.expr(&mut args[1], scope, None)?;
                            Type::Array(Box::new(element), Box::new(args[0].clone()))
                        } else {
                            first?
                        };
                        Some(Type::Unique(Box::new(payload)))
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
            Kind::Block(body, tail) => {
                let mut local = scope.clone();
                for statement in body {
                    self.statement(statement, &mut local);
                }
                self.expr(tail, &local, expected)
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
