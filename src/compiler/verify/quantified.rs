//! Elaborate total scalar quantifiers without evaluating an arbitrary memory
//! selection or hiding a bound argument inside an opaque predicate identity.

use super::*;

mod checks;
pub(super) use checks::Check;

#[cfg(test)]
mod call_tests;
#[cfg(test)]
mod precondition_tests;
#[cfg(test)]
mod tests;

impl Context<'_> {
    pub(super) fn quantified_argument(
        &mut self,
        text: &str,
        line: usize,
    ) -> Result<(Linear, subjects::Snapshot)> {
        let kind = if text.starts_with('-')
            || text.as_bytes().first().is_some_and(u8::is_ascii_digit)
        {
            Kind::Number(text.parse().map_err(|_| format!("line {line}: specialization integer exceeds the checked bootstrap numeric range"))?)
        } else {
            if !self.locals.values.contains_key(text) {
                return Err(format!(
                    "line {line}: specialization argument {text} is not a local integer value"
                ));
            }
            Kind::Name(text.into())
        };
        let expression = Expr { kind, line };
        let saved = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let value = self.eval(&expression, None);
        self.execution.phase = saved;
        let value = value?;
        let Symbol::Number(ty, term) = value else {
            return Err(format!(
                "line {line}: specialization requires an integer value"
            ));
        };
        let mut snapshot = self.claim_subjects(&expression)?;
        if ty != Ty::Int {
            if let Some(key) = snapshot.key.take() {
                snapshot = subjects::Snapshot::from_key(subjects::ClaimKey::Unary(
                    "integer".into(),
                    Box::new(key),
                ));
            }
        }
        Ok((term, snapshot))
    }

    pub(super) fn with_logical_binding<T>(
        &mut self,
        name: &str,
        variable: &str,
        quantified: bool,
        check: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let previous = self.locals.values.insert(
            name.into(),
            Symbol::Number(Ty::Int, Linear::variable(variable)),
        );
        let place = self.locals.places.remove(name);
        let ideal = self.locals.ideal_bindings.insert(name.into());
        self.locals.logical_bindings.push(context::LogicalBinding {
            name: name.into(),
            variable: variable.into(),
            quantified,
        });
        let result = check(self);
        self.locals.logical_bindings.pop();
        self.locals.values.remove(name);
        if let Some(previous) = previous {
            self.locals.values.insert(name.into(), previous);
        }
        if let Some(place) = place {
            self.locals.places.insert(name.into(), place);
        }
        if ideal {
            self.locals.ideal_bindings.remove(name);
        }
        result
    }

    pub(super) fn logical_key(&self, name: &str) -> Option<subjects::ClaimKey> {
        let mut depth = 0;
        for binding in self.locals.logical_bindings.iter().rev() {
            if binding.name == name {
                let expected = Symbol::Number(Ty::Int, Linear::variable(&binding.variable));
                // A callee or nominal invariant may have installed a new scope.
                if self.locals.places.contains_key(name)
                    || self.locals.values.get(name) != Some(&expected)
                {
                    return None;
                }
                return Some(if binding.quantified {
                    subjects::ClaimKey::Bound(depth)
                } else {
                    subjects::ClaimKey::LogicalVariable(binding.variable.clone())
                });
            }
            depth += usize::from(binding.quantified);
        }
        None
    }

    pub(super) fn quantified_name(&self) -> String {
        format!(
            "evg_bound_{}",
            self.locals
                .logical_bindings
                .iter()
                .filter(|b| b.quantified)
                .count()
        )
    }

    pub(super) fn eval_quantified(
        &mut self,
        name: &str,
        domain: &Expr,
        body: &Expr,
        line: usize,
    ) -> Result<Symbol> {
        if self.execution.phase != Phase::Specification {
            return Err(format!("line {line}: universal propositions are proof-only; they have no executable Boolean value"));
        }
        let variable = self.quantified_name();
        self.with_logical_binding(name, &variable, true, |ctx| {
            ctx.check_quantified_expression(domain, 0)?;
            ctx.check_quantified_expression(body, 0)?;
            // The domain cannot justify its own definedness. Its calls must be
            // valid for every binder value, subject only to enclosing domains.
            ctx.locals.quantified_checks.push(Vec::new());
            let domain = ctx.eval_quantified_expression(domain).and_then(|value| value.proposition());
            let domain_checks = ctx.locals.quantified_checks.pop().ok_or("missing quantified domain scope")?;
            let domain = domain?;
            if !domain.is_arithmetic() {
                return Err(format!("line {line}: a universal domain currently requires an unquantified scalar proposition"));
            }
            ctx.finish_quantified_checks(&variable, &Formula::True, domain_checks)?;
            ctx.locals.quantified_checks.push(Vec::new());
            let body = ctx.eval_quantified_expression(body).and_then(|body| body.proposition());
            let checks = ctx.locals.quantified_checks.pop().ok_or("missing quantified well-formedness scope")?;
            let body = body?;
            ctx.finish_quantified_checks(&variable, &domain, checks)?;
            Ok(Symbol::Bool(Formula::Forall {
                variable: variable.clone(), domain: Box::new(domain), body: Box::new(body),
            }))
        })
    }

    fn eval_quantified_expression(&mut self, expression: &Expr) -> Result<Symbol> {
        self.locals.quantified_evaluation += 1;
        let result = self.eval(expression, Some(&Ty::Bool));
        self.locals.quantified_evaluation -= 1;
        result
    }

    fn check_quantified_expression(&mut self, expression: &Expr, depth: usize) -> Result<()> {
        self.charge_value_work(1)?;
        if depth >= 32 {
            return Err("quantified expression nesting limit reached".into());
        }
        if let Some((base, index, target, _)) = array_predicates::indexed_type_parts(expression) {
            self.check_quantified_place(base)?;
            self.check_quantified_expression(index, depth + 1)?;
            if array_predicates::literal_target(self, target).is_none() {
                return Err("indexed type comparisons require a literal member type".into());
            }
            return Ok(());
        }
        let operands = array_values::parts(expression)
            .map(|(a, b, _)| (a, b))
            .or_else(|| match &expression.kind {
                Kind::Call(name, args) if name == "same_value" && args.len() == 2 => {
                    Some((&args[0], &args[1]))
                }
                _ => None,
            });
        if let Some((a, b)) = operands {
            for operand in [a, b] {
                if let Some((base, index)) = array_values::indexed_base(operand) {
                    self.check_quantified_place(base)?;
                    self.check_quantified_expression(index, depth + 1)?;
                } else {
                    self.check_quantified_expression(operand, depth + 1)?;
                }
            }
            return Ok(());
        }
        let error = || {
            format!("line {}: quantified propositions currently support total scalar arithmetic; indexed reads and opaque computations need structured bound-dependent terms", expression.line)
        };
        match &expression.kind {
            Kind::Number(_) | Kind::Constant(..) | Kind::Bool(_) => Ok(()),
            Kind::Name(name) if self.locals.values.contains_key(name) => Ok(()),
            Kind::Name(name) if self.proof.facts.contains_key(name) => {
                let fact = self.proof.facts[name].clone();
                self.check_quantified_expression(&fact, depth + 1)
            }
            Kind::Field(..) => {
                self.check_quantified_place(expression)?;
                if matches!(
                    self.hint(expression),
                    Some(Ty::Int | Ty::Nat | Ty::Machine(_) | Ty::Bool)
                ) {
                    Ok(())
                } else {
                    Err(error())
                }
            }
            Kind::Unary(op, value) if matches!(op.as_str(), "-" | "!") => {
                self.check_quantified_expression(value, depth + 1)?;
                if op == "-" && self.hint(value).unwrap_or(Ty::Int) != Ty::Int {
                    return Err(format!("line {}: quantified arithmetic uses integer values; use integer(value) for a machine or natural value", expression.line));
                }
                Ok(())
            }
            Kind::Binary(op, a, b) => {
                self.check_quantified_expression(a, depth + 1)?;
                self.check_quantified_expression(b, depth + 1)?;
                if matches!(op.as_str(), "+" | "-" | "*")
                    && [a, b]
                        .iter()
                        .any(|part| self.hint(part).unwrap_or(Ty::Int) != Ty::Int)
                {
                    return Err(format!("line {}: quantified arithmetic uses integer values; use integer(value) for a machine or natural value", expression.line));
                }
                Ok(())
            }
            Kind::Call(name, args) if name == "integer" && args.len() == 1 => {
                self.check_quantified_expression(&args[0], depth + 1)
            }
            Kind::Call(name, args) if self.declarations.functions.contains_key(name) => {
                self.quantified_scalar_function(name, expression.line)?;
                for argument in args {
                    self.check_quantified_expression(argument, depth + 1)?;
                }
                Ok(())
            }
            Kind::Forall { .. } => Ok(()), // Its own elaborator checks its lexical scope.
            _ => Err(error()),
        }
    }

    fn check_quantified_place(&self, expression: &Expr) -> Result<()> {
        match &expression.kind {
            Kind::Name(name)
                if self.logical_key(name).is_none() && self.locals.values.contains_key(name) =>
            {
                Ok(())
            }
            Kind::Field(base, _) => self.check_quantified_place(base),
            Kind::Call(name, args) if name == "old" && args.len() == 1 => {
                self.check_quantified_place(&args[0])
            }
            Kind::Unary(op, base) if op == "*" => self.check_quantified_place(base),
            _ => Err(format!(
                "line {}: quantified memory reads must be independent of the bound index",
                expression.line
            )),
        }
    }
}
