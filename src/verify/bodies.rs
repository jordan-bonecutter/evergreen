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
        let facts = std::mem::take(&mut self.facts);
        let proofs = std::mem::take(&mut self.proofs);
        let opened = std::mem::take(&mut self.opened);
        // Keep opened_planes: their unlifted requirements apply after every
        // actual write, including writes in further nested helper calls.
        let temporaries = std::mem::take(&mut self.temporaries);
        let current = self.current.replace(function.name.clone());
        let measure = self.measure.take();
        let writable = std::mem::replace(&mut self.writable, writes);
        let input_references = std::mem::replace(&mut self.input_references, inputs);
        let dropping = std::mem::replace(&mut self.dropping, false);
        let declaring = self.declaring.take();
        let ideal_execution = std::mem::replace(&mut self.ideal_execution, function.ideal);
        let execution = if function.ideal {
            Phase::Ideal
        } else {
            Phase::Runtime
        };
        let phase = std::mem::replace(&mut self.phase, execution);
        let checked = (|| {
            if let Some(decreases) = &function.decreases {
                self.phase = Phase::Specification;
                self.measure = Some(self.nonnegative(decreases, "nonnegative recursion measure")?);
                self.phase = execution;
            }
            let inputs = self.input_references.clone();
            let (value, post) = self.check_function_body(function, result_type, &inputs)?;
            if let Some(proposition) = post {
                // Publish only a checked theorem for this alias configuration.
                // An explicit trustme remains recorded in the proof manifest.
                self.assume(&proposition)?;
            }
            Ok(value)
        })();
        self.facts = facts;
        self.proofs = proofs;
        self.opened = opened;
        self.temporaries = temporaries;
        self.current = current;
        self.measure = measure;
        self.writable = writable;
        self.input_references = input_references;
        self.dropping = dropping;
        self.declaring = declaring;
        self.ideal_execution = ideal_execution;
        self.phase = phase;
        checked
    }
    /// Shared body obligations for declarations and actual-alias rechecks.
    pub(super) fn check_function_body(
        &mut self,
        function: &Function,
        result_type: &Ty,
        inputs: &[InputReference],
    ) -> Result<(Symbol, Option<Formula>)> {
        let entry = self.clone_env()?;
        // Entry aliases must precede stores and parameter rebinding.
        let aliases = self.return_aliases(function, Some(inputs))?;
        for statement in &function.body {
            self.statement(statement)?;
        }
        let value = self.scoped_eval(&function.result, Some(result_type))?;
        self.check_return_aliases(&value, &aliases, function.result.line)?;
        self.validate_live(function.result.line)?;
        self.finish_scope(function)?;
        if self.ty_has_reference(result_type) {
            self.validate_argument(&value, function.result.line)?;
        }
        let post = if let Some(post) = &function.post {
            self.phase = Phase::Specification;
            self.env = entry;
            self.roots.clear();
            self.charge_value_work(symbol_weight(&value)?)?;
            self.env.insert("result".into(), value.clone());
            let local_facts = std::mem::take(&mut self.facts);
            let proposition = self.proposition(post)?;
            self.facts = local_facts;
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
