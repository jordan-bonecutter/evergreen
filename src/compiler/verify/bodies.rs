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
        logical_precondition: Option<(Formula, subjects::Snapshot)>,
    ) -> Result<Symbol> {
        self.execution.rechecking += 1;
        // The caller has already bound arguments, checked preconditions and
        // authorized every declared write. Isolate lexical proof state and give
        // the body only its own grants, retaining actual plane identities.
        let facts = std::mem::take(&mut self.proof.facts);
        let proofs = std::mem::take(&mut self.proof.witnesses);
        let claims = std::mem::take(&mut self.proof.claims);
        let value_claims = std::mem::take(&mut self.proof.value_claims);
        let contract_uses = std::mem::take(&mut self.proof.contract_uses);
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
        let results = self.proof.results.len();
        let mut returned_claims = Vec::new();
        let checked = (|| {
            if let Some((proposition, subjects)) = logical_precondition {
                self.import_logical_contract(
                    proposition,
                    subjects,
                    self.proof.contract_parents.clone(),
                )?;
            }
            if let Some(decreases) = &function.decreases {
                self.execution.phase = Phase::Specification;
                self.execution.measure =
                    Some(self.nonnegative(decreases, "nonnegative recursion measure")?);
                self.execution.phase = execution;
            }
            let inputs = self.storage.inputs.clone();
            let (value, post) = self.check_function_body(function, result_type, &inputs, false)?;
            // Only this function's advertised postcondition crosses its call
            // boundary. Inner calls cannot masquerade as its returned value.
            self.proof.results.truncate(results);
            if let Some((proposition, checked)) = post {
                // This body was checked against the actual arguments. Export
                // its proof, rather than replacing it with an opaque contract.
                let node = self
                    .proof
                    .evidence
                    .derive(proposition.clone(), evidence::Rule::Reuse(checked))?;
                if proposition.is_arithmetic()
                    && self.evidence_dependencies(node)?.admissions.is_empty()
                {
                    self.assume_from(&proposition, paths::Origin::Evidence(node))?;
                } else {
                    if let Some(post) = &function.post {
                        let snapshot = self.claim_subjects(post)?;
                        returned_claims
                            .extend(self.publish_call_contract(node, snapshot, &value, post.line)?);
                    }
                }
            }
            Ok(value)
        })();
        self.proof.facts = facts;
        self.proof.witnesses = proofs;
        self.proof.claims = claims;
        self.proof.value_claims = value_claims;
        self.proof.claims.extend(returned_claims);
        self.proof.contract_uses = contract_uses;
        self.storage.temporaries = temporaries;
        self.execution.current = current;
        self.execution.measure = measure;
        self.storage.writable = writable;
        self.storage.inputs = input_references;
        self.execution.dropping = dropping;
        self.locals.declaring = declaring;
        self.execution.ideal_execution = ideal_execution;
        self.execution.phase = phase;
        self.execution.rechecking -= 1;
        checked
    }

    /// Shared body obligations for declarations and actual-alias rechecks.
    pub(super) fn check_function_body(
        &mut self,
        function: &Function,
        result_type: &Ty,
        inputs: &[InputReference],
        declaration: bool,
    ) -> Result<(Symbol, Option<(Formula, evidence::NodeId)>)> {
        self.session.clear_diagnostic();
        let checked = self.check_function_body_inner(function, result_type, inputs, declaration);
        if checked.is_ok() {
            self.session.clear_diagnostic();
        }
        checked.inspect_err(|error| {
            self.session
                .note_source(error, function.source, function.line);
        })
    }

    fn check_function_body_inner(
        &mut self,
        function: &Function,
        result_type: &Ty,
        inputs: &[InputReference],
        declaration: bool,
    ) -> Result<(Symbol, Option<(Formula, evidence::NodeId)>)> {
        let owner_scope = self.storage.memory.owner_scope();
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
        let return_source = if function.post.is_some() && !self.proof.claims.is_empty() {
            Some(self.claim_subjects(&function.result)?)
        } else {
            None
        };
        let value = self.scoped_eval(&function.result, Some(result_type))?;
        let return_subjects = if function.post.is_some() {
            self.charge_value_work(symbol_weight(&value)?)?;
            let return_world = self.proof.subjects.save_world()?;
            subjects::Snapshot::saved_scalar(return_world, return_source.as_ref(), &value)
        } else {
            None
        };
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
        self.storage.memory.require_owner_scope(&owner_scope)?;
        // Cleanup may change fields used to select a result-owned view.
        // Check provenance against the final returned storage, not a state
        // preceding destructor effects.
        self.check_return_aliases(&value, &aliases, function.result.line, infeasible_entry)?;
        if self.ty_has_reference(result_type) {
            self.validate_argument(&value, function.result.line)?;
        }
        let safety_end = self.proof.uses.len();
        let post = if let Some(post) = &function.post {
            self.execution.phase = Phase::Specification;
            self.locals.values = entry;
            self.locals.places.clear();
            self.charge_value_work(symbol_weight(&value)?)?;
            self.locals.values.insert("result".into(), value.clone());
            let mut post_subjects = self.claim_subjects(post)?;
            if let Some(saved) = &return_subjects {
                let result = self.claim_subjects(&Expr {
                    kind: Kind::Name("result".into()),
                    line: post.line,
                })?;
                post_subjects.replace_read(&result, saved);
            }
            for (name, _) in &function.params {
                let old = self.entry.values.get(name).cloned();
                if let Some(saved) = old.as_ref().and_then(|value| {
                    subjects::Snapshot::saved_scalar(self.entry.world, None, value)
                }) {
                    let parameter = self.claim_subjects(&Expr {
                        kind: Kind::Name(name.clone()),
                        line: post.line,
                    })?;
                    post_subjects.replace_read(&parameter, &saved);
                }
            }
            let local_facts = std::mem::take(&mut self.proof.facts);
            let proposition = self.proposition(post)?;
            self.proof.facts = local_facts;
            let checked = self
                .prove_with_subjects(
                    &proposition,
                    &format!("postcondition of {}", function.name),
                    post.line,
                    function.proof.as_deref(),
                    Some(&post_subjects),
                )
                .map_err(|error| {
                    self.requirement_error(error, post, function.source, "postcondition")
                })?;
            Some((proposition, checked))
        } else if function.proof.is_some() {
            return Err(format!(
                "line {}: a function proof block requires an ensures proposition",
                function.line
            ));
        } else {
            None
        };
        let post_uses = self.proof.uses.split_off(safety_end);
        self.proof.contract_uses.extend(post_uses);
        Ok((value, post))
    }
}
