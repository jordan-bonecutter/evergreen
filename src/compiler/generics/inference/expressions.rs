//! Elaborate arguments before selecting their enclosing generic instance.

use super::*;

impl Engine {
    pub(in crate::compiler::generics) fn expression(
        &mut self,
        expression: &mut Expr,
    ) -> Result<Option<Type>> {
        charge(&mut self.work)?;
        if self.depth >= 128 {
            return Err("generic expansion depth limit reached".into());
        }
        self.depth += 1;
        let result = self.expression_inner(expression);
        self.depth -= 1;
        result
    }

    fn expression_inner(&mut self, expression: &mut Expr) -> Result<Option<Type>> {
        self.explicit_arguments(expression)?;
        let line = expression.line;
        match &mut expression.kind {
            Kind::Call(name, args) => self.infer_call(name, args, line),
            Kind::Record(name, fields) => {
                let mut actual = Vec::new();
                for (field, value) in fields.iter_mut() {
                    actual.push((Some(field.as_str()), self.expression(value)?));
                }
                if self.templates.contains_key(name) {
                    let arguments = self.inferred_arguments(name, &actual, line)?;
                    *name = self.specialize(name, arguments, true)?;
                }
                Ok(Some(Type::Named(name.clone())))
            }
            Kind::Name(name) => {
                let hint = self
                    .inference
                    .scopes
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(name))
                    .cloned()
                    .flatten();
                self.read_hint(hint)
            }
            Kind::Field(base, name) => match self.expression(base)? {
                Some(ty) => self.field_hint(ty, name),
                None => Ok(None),
            },
            Kind::Unary(op, value) => {
                let ty = self.expression(value)?;
                Ok(match (op.as_str(), ty) {
                    ("&", Some(ty)) => Some(Type::Ref(Box::new(ty))),
                    ("*", Some(Type::Ref(t) | Type::Unique(t) | Type::Shared(t))) => Some(*t),
                    ("*", _) => None,
                    ("!", _) => Some(Type::Bool),
                    (_, ty) => ty,
                })
            }
            Kind::Binary(op, a, b) => {
                let a = self.expression(a)?;
                let b = self.expression(b)?;
                Ok(
                    if matches!(
                        op.as_str(),
                        "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "=>"
                    ) {
                        Some(Type::Bool)
                    } else {
                        compatible(a, b)
                    },
                )
            }
            Kind::Index(base, index) => {
                let base = self.expression(base)?;
                self.expr(index)?;
                Ok(match base {
                    Some(Type::Array(t, _)) => Some(*t),
                    _ => None,
                })
            }
            Kind::Array(items) => {
                let mut element = None;
                let mut conflict = false;
                for item in items.iter_mut() {
                    let ty = self.expression(item)?;
                    if element.is_some() && ty.is_some() && element != ty {
                        conflict = true;
                    }
                    if element.is_none() {
                        element = ty;
                    }
                }
                Ok(if conflict {
                    None
                } else {
                    element.map(|t| {
                        Type::Array(
                            Box::new(t),
                            Box::new(Expr {
                                kind: Kind::Number(items.len() as i128),
                                line,
                            }),
                        )
                    })
                })
            }
            Kind::If(condition, yes, no) => {
                self.expr(condition)?;
                let yes = self.expression(yes)?;
                let no = self.expression(no)?;
                Ok(compatible(yes, no))
            }
            Kind::Block(body, tail) => self.with_scope(|engine| {
                for statement in body {
                    engine.statement(statement)?;
                }
                engine.expression(tail)
            }),
            Kind::Forall {
                variable,
                domain,
                body,
            } => self.with_scope(|engine| {
                engine
                    .inference
                    .bind(variable, Some(Type::Int), &mut engine.work)?;
                engine.expr(domain)?;
                engine.expr(body)?;
                Ok(Some(Type::Bool))
            }),
            Kind::Type(ty) => {
                self.ty(ty)?;
                Ok(None)
            }
            Kind::FactAt(base, _) => {
                self.expr(base)?;
                Ok(Some(Type::Bool))
            }
            Kind::Bytes(bytes) => Ok(Some(Type::bytes(bytes.len(), line))),
            Kind::Constant(machine, _) => Ok(Some(Type::Machine(*machine))),
            Kind::Bool(_) => Ok(Some(Type::Bool)),
            Kind::Unit => Ok(Some(Type::Unit)),
            // A literal can take its type from a call parameter. Picking a type
            // here would defeat that context (and declared generic defaults).
            Kind::Number(_) | Kind::Generic { .. } => Ok(None),
        }
    }
}

fn compatible(a: Option<Type>, b: Option<Type>) -> Option<Type> {
    match (a, b) {
        (Some(a), Some(b)) if a == b => Some(a),
        (Some(a), None) | (None, Some(a)) => Some(a),
        _ => None,
    }
}
