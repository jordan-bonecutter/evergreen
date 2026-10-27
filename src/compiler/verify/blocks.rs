//! Lexical expression scopes share ordinary statement checking and cleanup.
//! Storage effects and immutable proof evidence survive; local names do not.

use super::*;

impl Context<'_> {
    pub(super) fn eval_block(
        &mut self,
        body: &[Statement],
        tail: &Expr,
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        if self.execution.phase != Phase::Runtime {
            return Err(format!("line {line}: statement blocks are runtime expressions; use pure expressions in specifications and ideal computations"));
        }
        let facts = self.proof.facts.keys().cloned().collect::<BTreeSet<_>>();
        let proofs = self
            .proof
            .witnesses
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>();
        let names = body
            .iter()
            .flat_map(Statement::bindings)
            .map(str::to_owned)
            .collect::<Vec<_>>();
        for statement in body {
            self.statement(statement)?;
        }
        let value = self.scoped_eval(tail, expected)?;
        // The pending result owns its allocations while local destructors run,
        // just as a function's return value does. Nested blocks need distinct
        // reserved bindings so neither can hide the other's live authority.
        let result_name = self.fresh_name();
        self.charge_value_work(symbol_weight(&value)?)?;
        self.locals
            .values
            .insert(result_name.clone(), value.clone());
        self.finish_bindings(names.clone(), false, line)?;
        self.locals.values.remove(&result_name);
        for name in names {
            self.locals.values.remove(&name);
            self.locals.places.remove(&name);
            self.locals.ideal_bindings.remove(&name);
        }
        self.proof.facts.retain(|name, _| facts.contains(name));
        self.proof.witnesses.retain(|name, _| proofs.contains(name));
        Ok(value)
    }
}
