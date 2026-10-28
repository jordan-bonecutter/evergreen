//! A quantified call must compute an explicit scalar term/formula. It cannot
//! substitute a fresh unknown result or import a contract mentioning the binder.

use super::*;

fn scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Int | Type::Nat | Type::Bool | Type::Unit | Type::Machine(_)
    )
}

impl<'a> Context<'a> {
    pub(in crate::compiler::verify) fn is_verified_scalar_definition(
        &self,
        function: &Function,
    ) -> bool {
        function.ideal
            && eligible(self, function)
            && scalar(&function.ret)
            && function.params.iter().all(|(_, ty)| scalar(ty))
            && self
                .declarations
                .summaries
                .get(&function.name)
                .is_some_and(|summary| summary.safety.is_empty())
    }

    pub(in crate::compiler::verify) fn quantified_scalar_function(
        &self,
        name: &str,
        line: usize,
    ) -> Result<&'a Function> {
        let function = self
            .declarations
            .functions
            .get(name)
            .ok_or_else(|| format!("line {line}: unknown quantified function {name}"))?;
        if !self.is_verified_scalar_definition(function) {
            return Err(format!("line {line}: quantified calls currently require a verified ideal scalar definition with no trusted safety dependency; {name} does not meet that requirement"));
        }
        Ok(function)
    }

    pub(in crate::compiler::verify) fn eval_quantified_call(
        &mut self,
        name: &str,
        args: &[Expr],
        line: usize,
    ) -> Result<Symbol> {
        let function = self.quantified_scalar_function(name, line)?;
        if args.len() != function.params.len() {
            return Err(format!(
                "line {line}: quantified scalar call to {name} requires all {} arguments",
                function.params.len()
            ));
        }
        let mut actuals = BTreeMap::new();
        for ((parameter, ty), expression) in function.params.iter().zip(args) {
            let ty = Self::declared_hint(ty).ok_or("missing quantified scalar type")?;
            let value = self.eval(expression, Some(&ty))?;
            actuals.insert(parameter.clone(), value);
        }
        let (value, precondition, spent) = {
            let mut budget = Budget::new(MAX_VALUE_WORK.saturating_sub(self.work.value_work));
            let mut importer = Importer::new(self, &mut budget);
            let mut arguments = BTreeMap::new();
            for (parameter, value) in &actuals {
                arguments.insert(
                    parameter.clone(),
                    importer
                        .value(value, 0)?
                        .ok_or("quantified call has a nonscalar argument")?,
                );
            }
            let precondition = if function.pre.is_some() {
                let value = evaluate::precondition(self, function, arguments.clone(), &mut budget)?
                    .ok_or_else(|| format!("line {line}: precondition of quantified call to {name} did not reduce to an exact scalar proposition"))?;
                budget.spend(symbolic::weight(&value)?)?;
                let proposition = value
                    .scalar()
                    .ok_or("quantified precondition is not scalar")?
                    .proposition()?;
                if !proposition.is_arithmetic() {
                    return Err(format!("line {line}: precondition of quantified call to {name} requires an arithmetic proposition"));
                }
                Some(proposition)
            } else {
                None
            };
            let value = evaluate::run(self, function, arguments, &mut budget)?;
            if let Some(value) = &value {
                budget.spend(symbolic::weight(value)?)?;
            }
            (value.and_then(Value::scalar), precondition, budget.spent)
        };
        self.charge_value_work(spent)?;
        if let Some(condition) = precondition {
            self.defer_quantified_check(
                condition,
                format!("precondition of quantified call to {name}"),
                line,
            )?;
        }
        // Deliberately bypass the ordinary unknown-result cache and postcondition
        // import. All bound dependence must remain visible to substitution and
        // universal introduction in the exact value returned by the evaluator.
        value.ok_or_else(|| format!("line {line}: quantified call to {name} did not reduce to an exact scalar expression; opaque computations need structured bound-dependent terms"))
    }
}
