//! Substitute syntax without capturing a runtime binding with the same name.

use super::*;

pub(super) struct Substitution<'a> {
    pub bindings: &'a BTreeMap<String, GenericArgument>,
    pub work: &'a mut usize,
}

impl Visitor for Substitution<'_> {
    fn ty(&mut self, ty: &mut Type) -> Result<()> {
        charge(self.work)?;
        if let Type::Named(name) = ty {
            if let Some(argument) = self.bindings.get(name) {
                let GenericArgument::Type(value) = argument else {
                    return Err(format!("const parameter {name} cannot be used as a type"));
                };
                // Meter the replacement before cloning its tree.
                charge_type(self.work, value)?;
                *ty = value.clone();
                return Ok(());
            }
        }
        visit::walk_type(self, ty)
    }

    fn expr(&mut self, expression: &mut Expr) -> Result<()> {
        charge(self.work)?;
        if let Kind::Name(name) = &expression.kind {
            if let Some(argument) = self.bindings.get(name) {
                if let GenericArgument::Type(ty) = argument {
                    charge_type(self.work, ty)?;
                }
                expression.kind = match argument {
                    GenericArgument::Type(ty) => Kind::Type(ty.clone()),
                    GenericArgument::Const(value) => value.kind.clone(),
                };
                return Ok(());
            }
        }
        visit::walk_expr(self, expression)
    }

    fn statement(&mut self, statement: &mut Statement) -> Result<()> {
        let named = match statement {
            Statement::Fact { name, .. } | Statement::Proof { name, .. } => Some(name.as_str()),
            _ => None,
        };
        if named.is_some_and(|name| self.bindings.contains_key(name)) {
            return Err("local facts and proofs cannot shadow generic parameters".into());
        }
        if statement
            .bindings()
            .iter()
            .any(|name| self.bindings.contains_key(*name))
        {
            return Err("runtime bindings cannot shadow generic parameters".into());
        }
        visit::walk_statement(self, statement)
    }
}
