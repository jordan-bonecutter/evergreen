//! Calls with overlapping ports or open invariants use actual shared storage.
//! Their modular summary cannot hide aliasing or intermediate writes.

use super::*;

impl Context<'_> {
    pub(super) fn check_actual_body(
        &mut self,
        function: &Function,
        result_type: &Ty,
        writes: Vec<WritePlace>,
        inputs: Vec<InputReference>,
    ) -> Result<Symbol> {
        // The caller has already bound arguments, checked preconditions and
        // authorized every declared write. Isolate lexical proof state and give
        // the body only its own grants, retaining actual plane identities.
        let facts = std::mem::take(&mut self.proof.facts);
        let proofs = std::mem::take(&mut self.proof.witnesses);
        // Keep opened_planes: their unlifted requirements apply after every
        // actual write, including writes in further nested helper calls.
        let temporaries = std::mem::take(&mut self.storage.temporaries);
        let current = self.execution.current.replace(function.name.clone());
        let measure = self.execution.measure.take();
        let writable = std::mem::replace(&mut self.storage.writable, writes);
        let input_references = std::mem::replace(&mut self.storage.inputs, inputs);
        let dropping = std::mem::replace(&mut self.execution.dropping, false);
        let declaring = self.locals.declaring.take();
        let ideal_execution =
            std::mem::replace(&mut self.execution.ideal_execution, function.ideal);
        let execution = if function.ideal {
            Phase::Ideal
        } else {
            Phase::Runtime
        };
        let phase = std::mem::replace(&mut self.execution.phase, execution);
        let checked = (|| {
            if let Some(decreases) = &function.decreases {
                self.execution.phase = Phase::Specification;
                self.execution.measure =
                    Some(self.nonnegative(decreases, "nonnegative recursion measure")?);
                self.execution.phase = execution;
            }
            let inputs = self.storage.inputs.clone();
            let (value, post) = self.check_function_body(function, result_type, &inputs, false)?;
            if let Some(proposition) = post {
                // Publish only a checked theorem for this alias configuration.
                // An explicit trustme remains recorded in the proof manifest.
                self.assume(&proposition)?;
            }
            Ok(value)
        })();
        self.proof.facts = facts;
        self.proof.witnesses = proofs;
        self.storage.temporaries = temporaries;
        self.execution.current = current;
        self.execution.measure = measure;
        self.storage.writable = writable;
        self.storage.inputs = input_references;
        self.execution.dropping = dropping;
        self.locals.declaring = declaring;
        self.execution.ideal_execution = ideal_execution;
        self.execution.phase = phase;
        checked
    }

    /// Shared body obligations for declarations and actual-alias rechecks.
    pub(super) fn check_function_body(
        &mut self,
        function: &Function,
        result_type: &Ty,
        inputs: &[InputReference],
        declaration: bool,
    ) -> Result<(Symbol, Option<Formula>)> {
        let entry = self.clone_env()?;
        // Only the independent entry configuration of a heap declaration may
        // be discharged as impossible. Actual calls and main always require
        // concrete provenance, even if a later trustme proves false.
        let infeasible_entry = declaration
            && function.name != "main"
            && !function.borrows.is_empty()
            && heap::function_uses_planes(function, self.declarations.structs)
            && self.follows(&Formula::False)?;
        // Entry aliases must precede stores and parameter rebinding.
        let aliases = self.return_aliases(function, Some(inputs))?;
        for statement in &function.body {
            self.statement(statement)?;
        }
        let value = self.scoped_eval(&function.result, Some(result_type))?;
        self.validate_live(function.result.line)?;
        // The return value owns its allocations while local destructors run.
        // This reserved binding is not a source name or a cleanup binding, and
        // normal calls isolate it in the caller environment as usual.
        if heap::owns_planes_type(&function.ret, self.declarations.structs) {
            self.charge_value_work(symbol_weight(&value)?)?;
            self.locals
                .values
                .insert("evg_return_value".into(), value.clone());
        }
        self.finish_scope(function)?;
        self.locals.values.remove("evg_return_value");
        // Cleanup may change fields used to select a result-owned view.
        // Check provenance against the final returned storage, not a state
        // preceding destructor effects.
        self.check_return_aliases(&value, &aliases, function.result.line, infeasible_entry)?;
        if self.ty_has_reference(result_type) {
            self.validate_argument(&value, function.result.line)?;
        }
        let post = if let Some(post) = &function.post {
            self.execution.phase = Phase::Specification;
            self.locals.values = entry;
            self.locals.places.clear();
            self.charge_value_work(symbol_weight(&value)?)?;
            self.locals.values.insert("result".into(), value.clone());
            let local_facts = std::mem::take(&mut self.proof.facts);
            let proposition = self.proposition(post)?;
            self.proof.facts = local_facts;
            self.prove_with(
                &proposition,
                &format!("postcondition of {}", function.name),
                post.line,
                function.proof.as_deref(),
            )?;
            Some(proposition)
        } else if function.proof.is_some() {
            return Err(format!(
                "line {}: a function proof block requires an ensures proposition",
                function.line
            ));
        } else {
            None
        };
        Ok((value, post))
    }
}
