//! Fallible syntax traversal for frontend transformations. Overrides choose
//! when a replacement should itself be visited.

use super::*;

pub(crate) type Result<T = ()> = std::result::Result<T, String>;

pub(crate) trait Visitor: Sized {
    fn ty(&mut self, ty: &mut Type) -> Result {
        walk_type(self, ty)
    }
    fn expr(&mut self, expr: &mut Expr) -> Result {
        walk_expr(self, expr)
    }
    fn statement(&mut self, statement: &mut Statement) -> Result {
        walk_statement(self, statement)
    }

    fn argument(&mut self, argument: &mut GenericArgument) -> Result {
        match argument {
            GenericArgument::Type(ty) => self.ty(ty),
            GenericArgument::Const(value) => self.expr(value),
        }
    }

    fn function(&mut self, function: &mut Function) -> Result {
        for (_, ty) in &mut function.params {
            self.ty(ty)?;
        }
        self.ty(&mut function.ret)?;
        for expression in function
            .pre
            .iter_mut()
            .chain(function.post.iter_mut())
            .chain(function.decreases.iter_mut())
            .chain(function.modifies.iter_mut())
        {
            self.expr(expression)?;
        }
        for alias in &mut function.borrows {
            self.expr(&mut alias.reference)?;
        }
        for statement in &mut function.body {
            self.statement(statement)?;
        }
        self.expr(&mut function.result)
    }

    fn record(&mut self, record: &mut Struct) -> Result {
        for (_, ty) in &mut record.fields {
            self.ty(ty)?;
        }
        for (_, fact) in &mut record.facts {
            self.expr(fact)?;
        }
        if let Some(invariant) = &mut record.invariant {
            self.expr(invariant)?;
        }
        Ok(())
    }
}

pub(crate) fn walk_type(v: &mut impl Visitor, ty: &mut Type) -> Result {
    match ty {
        Type::Apply(_, arguments) => {
            for argument in arguments {
                v.argument(argument)?;
            }
        }
        Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) | Type::Shape(inner) => {
            v.ty(inner)?
        }
        Type::Union(members) => {
            for member in members {
                v.ty(member)?;
            }
        }
        Type::Array(element, count) => {
            v.ty(element)?;
            v.expr(count)?;
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn walk_expr(v: &mut impl Visitor, expression: &mut Expr) -> Result {
    match &mut expression.kind {
        Kind::Type(ty) => v.ty(ty)?,
        Kind::Generic {
            arguments, value, ..
        } => {
            for argument in arguments {
                v.argument(argument)?;
            }
            v.expr(value)?;
        }
        Kind::Call(_, arguments) | Kind::Array(arguments) => {
            for argument in arguments {
                v.expr(argument)?;
            }
        }
        Kind::Record(_, fields) => {
            for (_, value) in fields {
                v.expr(value)?;
            }
        }
        Kind::Unary(_, value) | Kind::Field(value, _) | Kind::FactAt(value, _) => v.expr(value)?,
        Kind::Binary(_, a, b) | Kind::Index(a, b) => {
            v.expr(a)?;
            v.expr(b)?;
        }
        Kind::If(condition, yes, no) => {
            v.expr(condition)?;
            v.expr(yes)?;
            v.expr(no)?;
        }
        Kind::Block(body, tail) => {
            for statement in body {
                v.statement(statement)?;
            }
            v.expr(tail)?;
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn walk_statement(v: &mut impl Visitor, statement: &mut Statement) -> Result {
    match statement {
        Statement::Ideal(inner) => v.statement(inner)?,
        Statement::Let { ty, value, .. } => {
            if let Some(ty) = ty {
                v.ty(ty)?;
            }
            v.expr(value)?;
        }
        Statement::Destructure {
            arguments, value, ..
        } => {
            for argument in arguments {
                v.argument(argument)?;
            }
            v.expr(value)?;
        }
        Statement::Fact { value, .. } | Statement::Effect(value) => v.expr(value)?,
        Statement::Proof { proposition, .. } => v.expr(proposition)?,
        Statement::Assign { target, value } => {
            v.expr(target)?;
            v.expr(value)?;
        }
        Statement::Update { places, body, .. } => {
            for place in places {
                v.expr(place)?;
            }
            for statement in body {
                v.statement(statement)?;
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
            v.expr(condition)?;
            v.expr(invariant)?;
            for place in modifies {
                v.expr(place)?;
            }
            if let Some(measure) = decreases {
                v.expr(measure)?;
            }
            for statement in body {
                v.statement(statement)?;
            }
        }
    }
    Ok(())
}
