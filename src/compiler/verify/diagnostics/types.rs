//! Diagnostic-only reconstruction. Internal type identities remain unchanged.

use super::super::{Context, Ty};
use crate::syntax::{Expr, GenericArgument, Kind, Type};

impl Context<'_> {
    pub(crate) fn diagnostic_type(&self, ty: &Ty) -> String {
        let syntax = self.diagnostic_type_syntax(ty, &mut 80);
        crate::syntax::display::expression(&Expr {
            kind: Kind::Type(syntax),
            line: 0,
        })
    }

    fn diagnostic_type_syntax(&self, ty: &Ty, budget: &mut usize) -> Type {
        if *budget == 0 {
            return Type::Named("…".into());
        }
        *budget -= 1;
        match ty {
            Ty::Int => Type::Int,
            Ty::Nat => Type::Nat,
            Ty::Bool => Type::Bool,
            Ty::Fact => Type::Fact,
            Ty::Unit => Type::Unit,
            Ty::Type => Type::Named("type".into()),
            Ty::Machine(integer) => self.diagnostic_source_type(&Type::Machine(*integer), budget),
            Ty::Record(name) => self.diagnostic_source_type(&Type::Named(name.clone()), budget),
            Ty::Ref(inner) => Type::Ref(Box::new(self.diagnostic_type_syntax(inner, budget))),
            Ty::Unique(inner) => Type::Unique(Box::new(self.diagnostic_type_syntax(inner, budget))),
            Ty::Shared(inner) => Type::Shared(Box::new(self.diagnostic_type_syntax(inner, budget))),
            Ty::Shape(inner) => Type::Shape(Box::new(self.diagnostic_type_syntax(inner, budget))),
            Ty::Union(members) => Type::Union(
                members
                    .iter()
                    .take(9)
                    .map(|ty| self.diagnostic_type_syntax(ty, budget))
                    .collect(),
            ),
            Ty::Array(element, extent) => Type::Array(
                Box::new(self.diagnostic_type_syntax(element, budget)),
                Box::new(Expr {
                    kind: if extent.terms.is_empty() {
                        Kind::Number(extent.constant)
                    } else {
                        Kind::Name("<runtime length>".into())
                    },
                    line: 0,
                }),
            ),
        }
    }

    fn diagnostic_source_type(&self, ty: &Type, budget: &mut usize) -> Type {
        if *budget == 0 {
            return Type::Named("…".into());
        }
        *budget -= 1;
        match ty {
            Type::Named(name) => self
                .declarations
                .structs
                .get(name)
                .and_then(|record| record.display_type.as_ref())
                .map(|ty| self.diagnostic_source_type(ty, budget))
                .unwrap_or_else(|| ty.clone()),
            Type::Machine(integer) => {
                let name = if integer.domain == crate::syntax::IntegerDomain::Zero {
                    "Null".into()
                } else if integer.bits == self.declarations.target.word_bits() {
                    if integer.signed { "isize" } else { "usize" }.into()
                } else {
                    integer.primitive_name()
                };
                Type::Named(name)
            }
            Type::Apply(name, arguments) => Type::Apply(
                name.clone(),
                arguments
                    .iter()
                    .take(9)
                    .map(|arg| match arg {
                        GenericArgument::Type(ty) => {
                            GenericArgument::Type(self.diagnostic_source_type(ty, budget))
                        }
                        GenericArgument::Const(value) => GenericArgument::Const(value.clone()),
                    })
                    .collect(),
            ),
            Type::Ref(inner) => Type::Ref(Box::new(self.diagnostic_source_type(inner, budget))),
            Type::Unique(inner) => {
                Type::Unique(Box::new(self.diagnostic_source_type(inner, budget)))
            }
            Type::Shared(inner) => {
                Type::Shared(Box::new(self.diagnostic_source_type(inner, budget)))
            }
            Type::Shape(inner) => Type::Shape(Box::new(self.diagnostic_source_type(inner, budget))),
            Type::Array(inner, count) => Type::Array(
                Box::new(self.diagnostic_source_type(inner, budget)),
                count.clone(),
            ),
            Type::Union(members) => Type::Union(
                members
                    .iter()
                    .take(9)
                    .map(|ty| self.diagnostic_source_type(ty, budget))
                    .collect(),
            ),
            _ => ty.clone(),
        }
    }
}
