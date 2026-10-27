//! Calls: builtin operations, phase permissions, argument evaluation, and
//! checked contract application. Callee environments never replace heap identity.

use super::*;

struct ArgumentOrigin {
    subjects: subjects::Snapshot,
    world: state::WorldId,
}

struct Arguments {
    values: Vec<Symbol>,
    subjects: BTreeMap<String, ArgumentOrigin>,
}

impl<'a> Context<'a> {
    pub(super) fn eval_call(
        &mut self,
        name: &str,
        args: &[Expr],
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        if name == "typeof" || name == "shape" {
            return self.eval_type_operation(name, args, expected, line);
        }
        if let Some(target) = MachineInt::parse(name) {
            return self.convert_integer(target, args, line);
        }
        if name == "alloc" {
            return self.allocate_owned(args, expected, line);
        }
        if name == "old" {
            if self.execution.phase == Phase::Runtime || args.len() != 1 {
                return Err(
                    "old is proof-only and takes one entry-state parameter expression".into(),
                );
            }
            let value = self.old_expression(&args[0], expected)?;
            if self.execution.phase == Phase::Ideal && self.symbol_is_move_only(&value) {
                return Err(
                    "old ownership snapshots are proof views, not new ideal resources".into(),
                );
            }
            return Ok(value);
        }
        if name == "integer" || name == "nat" {
            if self.execution.phase == Phase::Runtime {
                return Err("mathematical views are proof-only".into());
            }
            if args.len() != 1 {
                return Err(format!("{name} expects one integer"));
            }
            let n = self.eval(&args[0], None)?.number()?;
            if name == "nat" {
                self.prove(&Formula::Ge(n.clone()), "nonnegative natural view", line)?;
            }
            return Ok(Symbol::Number(
                if name == "nat" { Ty::Nat } else { Ty::Int },
                n,
            ));
        }
        if self.execution.phase == Phase::Specification
            && self.execution.current.as_deref() == Some(name)
        {
            return Err("recursive calls are forbidden in specifications".into());
        }
        if name == "move" || name == "drop" {
            return self.eval_ownership_call(name, args, line);
        }
        let function = self.function_for_call(name, line)?;
        let actuals = self.evaluate_arguments(function, args, line)?;
        self.apply_call(name, function, actuals, line)
    }

    fn eval_ownership_call(&mut self, name: &str, args: &[Expr], line: usize) -> Result<Symbol> {
        if self.execution.phase == Phase::Runtime && !self.storage.opened_planes.is_empty() {
            return Err("moves and drops are forbidden while invariants are open".into());
        }
        if self.execution.dropping
            && !matches!(args, [argument] if matches!(&argument.kind, Kind::Name(name) if name != "self"))
        {
            return Err(
                "destructor moves and drops require a complete local binding; decompose self first"
                    .into(),
            );
        }
        if self.execution.phase == Phase::Specification {
            return Err("specifications and facts cannot move or drop values".into());
        }
        if args.len() != 1 {
            return Err(format!("{name} expects one place"));
        }
        if self.execution.phase == Phase::Ideal
            && !self.execution.ideal_execution
            && !matches!(&args[0].kind, Kind::Name(n) if self.locals.ideal_bindings.contains(n))
        {
            return Err("erased execution cannot move or drop a runtime place".into());
        }
        let (r, path) = self.location(&args[0])?;
        if !path.is_empty() {
            return Err(
                "moving individual fields requires partial-shape tracking; unsupported".into(),
            );
        }
        let id = self.storage.memory.plane(r)?;
        if !self.locals.places.values().any(|p| *p == id) {
            return Err("cannot move or drop a borrowed parameter plane".into());
        }
        let stored = self.storage.memory.read(r)?.clone();
        self.record_valid(&stored, line)?;
        let value = self.take_symbol(id)?;
        self.validate_argument(&value, line)?;
        if name == "drop" {
            self.cleanup_value(value, line)?;
            return Ok(Symbol::Unit);
        }
        Ok(value)
    }

    fn function_for_call(&mut self, name: &str, line: usize) -> Result<&'a Function> {
        let f = self.declarations.functions.get(name).ok_or_else(|| {
            if let Some(method) = name.strip_prefix("evg_method_") {
                return format!(
                    "line {}: unknown method {method} or unresolved receiver type",
                    line
                );
            }
            if self.execution.current.as_deref() == Some(name) {
                format!(
                    "line {}: recursive ideal function {name} requires a decreases clause",
                    line
                )
            } else {
                format!("line {}: unknown function {name}", line)
            }
        })?;
        if self.execution.phase == Phase::Runtime
            && !self.storage.opened_planes.is_empty()
            && !self.declarations.cleanup_helpers.contains(name)
        {
            return Err(
                "calls while invariants are open require checked scalar ownership-free effects"
                    .into(),
            );
        }
        if self.execution.dropping
            && self.execution.phase == Phase::Runtime
            && !self.declarations.cleanup_helpers.contains(name)
            && !crate::compiler::effects::disposes_parameters(f)
        {
            return Err(
                "destructor calls require checked ownership-free effects or a parameter-disposal helper".into(),
            );
        }
        if f.partial {
            if self.execution.phase != Phase::Runtime {
                return Err(
                    "potentially divergent functions cannot be used in proofs or ideal execution"
                        .into(),
                );
            }
            self.execution.partial_execution = true;
        }
        if self.execution.phase == Phase::Specification
            && (heap::owns_planes_type(&f.ret, self.declarations.structs)
                || f.params
                    .iter()
                    .any(|(_, ty)| heap::owns_planes_type(ty, self.declarations.structs)))
        {
            return Err("proof calls must borrow heap owners; ownership transfers and owning results cannot be erased".into());
        }
        if !f.modifies.is_empty() && self.execution.phase == Phase::Specification {
            return Err("modifying calls are forbidden in proof expressions".into());
        }
        if self.execution.phase == Phase::Ideal
            && !f.ideal
            && !self.declarations.helpers.contains(name)
        {
            return Err("modifying calls and runtime effects cannot be erased; an ideal expression needs ideal code or a checked pure scalar helper".into());
        }
        if f.ideal && self.execution.phase == Phase::Runtime {
            return Err(format!(
                "{name} is ideal code and cannot be called at runtime"
            ));
        }
        Ok(f)
    }

    fn evaluate_arguments(
        &mut self,
        f: &Function,
        args: &[Expr],
        line: usize,
    ) -> Result<Arguments> {
        let supplied = f
            .supplied_parameters(args.len())
            .map_err(|error| format!("line {}: {error}", line))?;
        // Evaluate actuals in the caller; dependent parameter types in an
        // isolated callee environment. Restore the caller on completion.
        let mut actuals = BTreeMap::new();
        let mut subjects = BTreeMap::new();
        for ((parameter, t), arg) in supplied.into_iter().zip(args) {
            let hint = match t {
                Type::Nat => Some(Ty::Nat),
                Type::Int => Some(Ty::Int),
                Type::Bool => Some(Ty::Bool),
                Type::Machine(t) => Some(Ty::Machine(*t)),
                Type::Union(_) | Type::Shape(_) => Self::declared_hint(t),
                Type::Plane(_) => self.literal_element_hint(t)?,
                _ => Self::declared_hint(t),
            };
            if f.pre.is_some()
                || !self.proof.claims.is_empty()
                || self
                    .declarations
                    .summaries
                    .get(&f.name)
                    .is_some_and(|s| !s.contract.is_empty())
            {
                let observed = self.claim_subjects(arg)?;
                let world = self.proof.subjects.save_world()?;
                subjects.insert(
                    parameter.clone(),
                    ArgumentOrigin {
                        subjects: observed,
                        world,
                    },
                );
            }
            let saved_specification = self.execution.phase;
            if f.ideal_params.contains(parameter) && self.execution.phase != Phase::Specification {
                self.execution.phase = Phase::Ideal;
            }
            let value = if let (Type::Array(element, _), Kind::Array(_)) = (t, &arg.kind) {
                if let Some(element) = self.literal_element_hint(element)? {
                    // Infer literal elements now; defer its length check
                    // to the isolated, fully bound callee environment.
                    self.eval_inner(arg, Some(&Ty::Array(Box::new(element), Linear::number(0))))?
                } else {
                    self.eval(arg, hint.as_ref())?
                }
            } else {
                self.eval(arg, hint.as_ref())?
            };
            self.execution.phase = saved_specification;
            if subjects
                .get(parameter)
                .is_some_and(|origin| !origin.subjects.complete)
            {
                let world = self.proof.subjects.save_world()?;
                if let Some(observed) = subjects::Snapshot::saved_scalar(world, None, &value) {
                    subjects.insert(
                        parameter.clone(),
                        ArgumentOrigin {
                            subjects: observed,
                            world,
                        },
                    );
                }
            }
            self.validate_argument(&value, line)?;
            actuals.insert(parameter.clone(), value);
        }
        // A later argument can consume storage borrowed by an earlier
        // argument. Recheck the complete actual list at the call boundary.
        for value in actuals.values() {
            self.validate_argument(value, line)?;
        }
        Ok(Arguments {
            values: self.complete_arguments(f, actuals, line)?,
            subjects,
        })
    }

    fn call_subjects(
        &mut self,
        expression: &Expr,
        origins: &BTreeMap<String, ArgumentOrigin>,
        line: usize,
        force: bool,
    ) -> Result<Option<subjects::Snapshot>> {
        if !force && origins.is_empty() && self.proof.claims.is_empty() {
            return Ok(None);
        }
        let mut goal = self.claim_subjects(expression)?;
        for (parameter, origin) in origins {
            let scalar = matches!(
                self.locals.values.get(parameter),
                Some(
                    Symbol::Number(..)
                        | Symbol::Bool(_)
                        | Symbol::Unit
                        | Symbol::Union { .. }
                        | Symbol::Shape(_)
                )
            );
            let available = if scalar {
                self.proof
                    .subjects
                    .historical(&origin.subjects, origin.world)?
            } else {
                self.proof
                    .subjects
                    .current(&origin.subjects, &self.storage.memory)?
            };
            if available {
                let local = self.claim_subjects(&Expr {
                    kind: Kind::Name(parameter.clone()),
                    line,
                })?;
                let replacement = if scalar {
                    origin.subjects.old_at(origin.world)
                } else {
                    origin.subjects.clone()
                };
                goal.replace_read(&local, &replacement);
            }
        }
        Ok(Some(goal))
    }

    fn apply_call(
        &mut self,
        name: &str,
        f: &Function,
        actuals: Arguments,
        line: usize,
    ) -> Result<Symbol> {
        let mut saved = std::mem::take(&mut self.locals.values);
        let saved_roots = std::mem::take(&mut self.locals.places);
        let saved_old = std::mem::take(&mut self.entry.values);
        let saved_entry_world = self.entry.world;
        let saved_old_memory = self.entry.memory.take();
        let saved_ideal = std::mem::take(&mut self.locals.ideal_bindings);
        let saved_module = std::mem::replace(&mut self.locals.module, f.module.clone());
        self.locals.ideal_bindings = f.ideal_params.iter().cloned().collect();
        self.locals.values.clear();
        self.locals.places.clear();
        self.bind_arguments(f, actuals.values, line)?;
        self.capture_old(f)?;
        let mut call_dependencies = Vec::new();
        if let Some(pre) = &f.pre {
            let subjects = self.call_subjects(pre, &actuals.subjects, line, false)?;
            let p = self.proposition(pre)?;
            let evidence = self.prove_subjects(
                &p,
                subjects.as_ref(),
                &format!("precondition of {name}"),
                line,
            )?;
            if !self.evidence_dependencies(evidence)?.admissions.is_empty() {
                call_dependencies.push(evidence);
            }
        }
        let inherited_contracts = self.proof.contract_parents.clone();
        self.proof
            .contract_parents
            .extend(call_dependencies.iter().copied());
        let inputs = if f
            .params
            .iter()
            .any(|(_, ty)| type_has_reference(ty, self.declarations.structs))
        {
            self.incoming_references(f, !f.modifies.is_empty())?
        } else {
            Vec::new()
        };
        let writes = self.write_places(f, &inputs)?;
        // Even read-only contracts may observe reference identity.
        // An independent-port summary cannot describe aliased inputs.
        let overlaps = self.reference_ports_overlap(&inputs)?;
        if overlaps && f.external.is_some() {
            return Err("external calls with overlapping reference ports require an alias-aware contract; unsupported".into());
        }
        if self.execution.current.as_deref() == Some(name) && !f.partial {
            let entry = self
                .execution
                .measure
                .clone()
                .ok_or("recursive calls require a decreases clause")?;
            let expression = f
                .decreases
                .as_ref()
                .ok_or("recursive calls require a decreases clause")?;
            let saved_specification = self.execution.phase;
            self.execution.phase = Phase::Specification;
            let next = self.nonnegative(expression, "nonnegative recursion measure")?;
            self.execution.phase = saved_specification;
            self.prove(
                &Formula::Ge(entry.sub(&next)?.add(&Linear::number(-1))?),
                "strictly decreasing recursion measure",
                line,
            )?;
        }
        let ret = self.resolve(&f.ret)?;
        let mut changed_roots = BTreeSet::new();
        for write in &writes {
            let id = self.storage.memory.plane(write.reference)?;
            changed_roots.insert(id);
            let owned = self.owns_plane_in(&saved, &saved_roots, id)? || self.owns_plane(id)?;
            if !self.write_permitted(write.reference, &write.path, owned)? {
                return Err(format!("line {}: call to {name} writes through a parameter without a matching modifies contract", line));
            }
        }
        let heap_call = heap::function_uses_planes(f, self.declarations.structs);
        let value = if overlaps
            || heap_call
            || !self.storage.opened_planes.is_empty() && !f.modifies.is_empty()
        {
            let reason = if overlaps {
                "overlaps incoming references"
            } else if heap_call {
                "uses owned planes"
            } else {
                "writes while invariants are open"
            };
            self.check_actual_body(f, &ret, writes, inputs)
                .map_err(|error| {
                    format!(
                        "line {}: call to {name} {reason}; body recheck failed: {error}",
                        line
                    )
                })?
        } else {
            let safety = self.import_summary(name, summaries::Aspect::Safety)?;
            self.proof.uses.extend(safety);
            let contract = self.import_summary(name, summaries::Aspect::Contract)?;
            self.proof.contract_parents.extend(contract);
            call_dependencies = self.proof.contract_parents.clone();
            let value = if !f.borrows.is_empty() {
                let aliases = self.return_aliases(f, None)?;
                self.return_shape(&ret, &mut Vec::new(), &aliases)?
            } else {
                self.arbitrary(&ret)?
            };
            for write in writes {
                let id = self.storage.memory.plane(write.reference)?;
                let mut new = self.arbitrary(&write.ty)?;
                self.charge_value_work(symbol_weight(self.storage.memory.read(write.reference)?)?)?;
                let mut root = self.storage.memory.read(write.reference)?.clone();
                self.preserve_views(project(&root, &write.path)?, &mut new)?;
                self.replace_projection(&mut root, &write.path, new)?;
                self.note_state_write(id, &write.path)?;
                self.storage.memory.write(id, root, false)?;
            }
            for input in inputs.iter().filter(|_| !f.modifies.is_empty()) {
                // Each input's declared type is an implicit return contract.
                // The body is checked to preserve these views even if the
                // local parameter is rebound. Caller-only enclosing types
                // are obligations below, not assumptions here.
                self.charge_value_work(symbol_weight(project(
                    self.storage.memory.read(input.reference)?,
                    &input.path,
                )?)?)?;
                let target =
                    project(self.storage.memory.read(input.reference)?, &input.path)?.clone();
                self.assume_element_type(&target)?;
            }
            if !f.borrows.is_empty() {
                self.assume_return_type(&value, &ret)?;
            }
            self.locals.values.insert("result".into(), value.clone());
            if let Some(post) = &f.post {
                if call_dependencies.is_empty() {
                    let p = self.proposition(post)?;
                    self.assume(&p)?;
                } else {
                    let paths = self.proof.paths.clone();
                    let subjects = self.call_subjects(post, &actuals.subjects, line, true)?;
                    let p = self.proposition(post)?;
                    self.proof.paths = paths;
                    let node = self.proof.evidence.contract(p, call_dependencies.clone())?;
                    if self.evidence_dependencies(node)?.admissions.is_empty() {
                        if let Some(snapshot) = subjects {
                            self.record_recursive_context(node, snapshot)?;
                        }
                        let p = self.proof.evidence.claim(node)?.clone();
                        self.assume_from(&p, paths::Origin::Evidence(node))?;
                    } else {
                        let clauses = self.contract_clauses(node, subjects.unwrap_or_default())?;
                        let origin = self.claim_subjects(&Expr {
                            kind: Kind::Name("result".into()),
                            line,
                        })?;
                        for proof in clauses {
                            self.proof.claims.insert(proof);
                            self.charge_value_work(symbol_weight(&value)?)?;
                            self.proof.results.push(value_evidence::CallResult {
                                value: value.clone(),
                                proof,
                                origin: origin.clone(),
                            });
                        }
                    }
                }
            }
            // Alias contracts describe entry storage. After applying the
            // checked postcondition, revalidate the saved reference and its
            // current target. Havoced contents need not satisfy nominal
            // invariants until that postcondition has constrained them.
            if !f.borrows.is_empty() && !f.modifies.is_empty() {
                self.validate_argument(&value, line)?;
            }
            value
        };
        if heap_call {
            // An actual body may write and then release storage it
            // received by ownership. Surviving plain aliases are never;
            // validating a fictional post-store root would revive it.
            changed_roots.retain(|root| self.storage.memory.get(*root).is_ok());
        }
        for root in &changed_roots {
            self.charge_value_work(symbol_weight(self.storage.memory.get(*root)?)?)?;
            let stored = self.storage.memory.get(*root)?.clone();
            for (binding, plane) in &saved_roots {
                if plane == root {
                    saved.insert(binding.clone(), stored.clone());
                }
            }
        }
        self.locals.values = saved;
        self.locals.places = saved_roots;
        self.entry.values = saved_old;
        self.entry.world = saved_entry_world;
        self.entry.memory = saved_old_memory;
        self.locals.ideal_bindings = saved_ideal;
        self.locals.module = saved_module;
        for root in changed_roots {
            self.charge_value_work(symbol_weight(self.storage.memory.get(root)?)?)?;
            let stored = self.storage.memory.get(root)?.clone();
            let lifted = self
                .storage
                .opened_planes
                .get(&root)
                .cloned()
                .unwrap_or_default();
            self.retained_valid_with(&stored, line, &lifted)?;
        }
        if !f.modifies.is_empty() {
            self.validate_live(line)?;
        }
        self.proof.contract_parents = inherited_contracts;
        Ok(value)
    }
}
