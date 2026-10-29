//! Scalar refinements lower to ordinary invariant-bearing storage. Conversion
//! proposes construction or projection; the verifier still checks every value,
//! borrow, enclosing invariant, and write footprint using its existing rules.

use super::*;
use crate::syntax::Struct;

impl Shapes {
    pub(super) fn refined_base(&self, ty: &Type) -> Option<&Type> {
        let Type::Named(name) = ty else { return None };
        self.refinements.get(name)
    }

    pub(super) fn refine_expression(
        &self,
        expr: &mut Expr,
        actual: Option<Type>,
        expected: Option<&Type>,
    ) -> Option<Type> {
        if actual.as_ref() == expected || expected.is_none() {
            return actual;
        }
        if let Some(base) = actual.as_ref().and_then(|ty| self.refined_base(ty)) {
            let base = base.clone();
            project(expr);
            return self.refine_expression(expr, Some(base), expected);
        }
        if let Some(Type::Named(name)) = expected {
            if self.refinements.contains_key(name) {
                let value = expr.clone();
                expr.kind = Kind::Record(name.clone(), vec![(Struct::SCALAR_VALUE.into(), value)]);
                return expected.cloned();
            }
        }
        if let (Some(Type::Ref(actual)), Some(Type::Ref(expected))) = (&actual, expected) {
            if self
                .refined_base(actual)
                .is_some_and(|base| base == expected.as_ref())
            {
                let pointer = expr.clone();
                let mut value = Expr {
                    kind: Kind::Unary("*".into(), Box::new(pointer)),
                    line: expr.line,
                };
                project(&mut value);
                expr.kind = Kind::Unary("&".into(), Box::new(value));
                return Some(Type::Ref(expected.clone()));
            }
        }
        actual
    }

    pub(super) fn scalar_expression(
        &self,
        expr: &mut Expr,
        scope: &Scope,
        expected: Option<&Type>,
    ) -> Option<Type> {
        let actual = self.expr(expr, scope, expected);
        if let Some(base) = actual.as_ref().and_then(|ty| self.refined_base(ty)) {
            project(expr);
            return Some(base.clone());
        }
        actual
    }

    pub(super) fn refine_arguments(&self, name: &str, args: &mut [Expr], actuals: &[Option<Type>]) {
        // An inferred extent changes argument positions. Those arguments retain
        // ordinary verifier checks; never rerun recursive expression lowering.
        if args.len() != actuals.len() {
            return;
        }
        let Some(all) = self.all_parameters.get(name) else {
            return;
        };
        let parameters = if args.len() == all.len() {
            all
        } else {
            let Some(runtime) = self.parameters.get(name) else {
                return;
            };
            if args.len() != runtime.len() {
                return;
            }
            runtime
        };
        for ((arg, (_, ty)), actual) in args.iter_mut().zip(parameters).zip(actuals) {
            self.refine_expression(arg, actual.clone(), Some(ty));
        }
    }
}

fn project(expr: &mut Expr) {
    let value = expr.clone();
    expr.kind = Kind::Field(Box::new(value), Struct::SCALAR_VALUE.into());
}
