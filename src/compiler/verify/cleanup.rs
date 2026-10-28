//! Cleanup elaboration. Effectful destructors are checked against the actual
//! receiver so child cleanup sees fields changed by its parent's body.

use super::*;

struct Scope {
    env: BTreeMap<String, Symbol>,
    roots: BTreeMap<String, PlaneId>,
    facts: BTreeMap<String, Expr>,
    proofs: BTreeMap<String, evidence::NodeId>,
    claims: BTreeSet<evidence::NodeId>,
    value_claims: Vec<evidence::NodeId>,
    module: Option<String>,
    phase: Phase,
    current: Option<String>,
    measure: Option<Linear>,
    opened_planes: BTreeMap<PlaneId, BTreeSet<String>>,
    dropping: bool,
    writable: Vec<WritePlace>,
    inputs: Vec<InputReference>,
    old_values: BTreeMap<String, Symbol>,
    entry_world: state::WorldId,
    old_memory: Option<Box<EntryMemory>>,
    ideal: BTreeSet<String>,
    temporaries: Vec<(Symbol, usize)>,
}

impl Scope {
    fn enter(ctx: &mut Context<'_>, f: &Function, receiver: Symbol) -> Self {
        let saved = Self {
            env: std::mem::take(&mut ctx.locals.values),
            roots: std::mem::take(&mut ctx.locals.places),
            facts: std::mem::take(&mut ctx.proof.facts),
            proofs: std::mem::take(&mut ctx.proof.witnesses),
            claims: std::mem::take(&mut ctx.proof.claims),
            value_claims: std::mem::take(&mut ctx.proof.value_claims),
            module: std::mem::replace(&mut ctx.locals.module, f.module.clone()),
            phase: std::mem::replace(&mut ctx.execution.phase, Phase::Runtime),
            current: ctx.execution.current.replace(f.name.clone()),
            measure: ctx.execution.measure.take(),
            opened_planes: std::mem::take(&mut ctx.storage.opened_planes),
            dropping: std::mem::replace(&mut ctx.execution.dropping, true),
            writable: std::mem::take(&mut ctx.storage.writable),
            inputs: std::mem::take(&mut ctx.storage.inputs),
            old_values: std::mem::take(&mut ctx.entry.values),
            entry_world: ctx.entry.world,
            old_memory: ctx.entry.memory.take(),
            ideal: std::mem::take(&mut ctx.locals.ideal_bindings),
            temporaries: std::mem::take(&mut ctx.storage.temporaries),
        };
        ctx.locals.values.insert("self".into(), receiver);
        saved
    }

    fn restore(self, ctx: &mut Context<'_>) {
        ctx.locals.values = self.env;
        ctx.locals.places = self.roots;
        ctx.proof.facts = self.facts;
        ctx.proof.witnesses = self.proofs;
        ctx.proof.claims = self.claims;
        ctx.proof.value_claims = self.value_claims;
        ctx.locals.module = self.module;
        ctx.execution.phase = self.phase;
        ctx.execution.current = self.current;
        ctx.execution.measure = self.measure;
        ctx.storage.opened_planes = self.opened_planes;
        ctx.execution.dropping = self.dropping;
        ctx.storage.writable = self.writable;
        ctx.storage.inputs = self.inputs;
        ctx.entry.values = self.old_values;
        ctx.entry.world = self.entry_world;
        ctx.entry.memory = self.old_memory;
        ctx.locals.ideal_bindings = self.ideal;
        ctx.storage.temporaries = self.temporaries;
    }
}

impl Context<'_> {
    pub(super) fn note_cleanup_divergence(&mut self, method: &str) {
        self.execution.partial_execution |= self
            .declarations
            .functions
            .get(method)
            .is_some_and(|function| function.partial);
    }

    pub(super) fn drop_receiver_consumed(&self) -> bool {
        self.execution.dropping
            && self
                .locals
                .places
                .get("self")
                .is_some_and(|plane| self.storage.memory.get(*plane).is_err())
    }

    pub(super) fn finish_scope(&mut self, f: &Function) -> Result<()> {
        let mut names = f.params.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>();
        names.extend(
            f.body
                .iter()
                .flat_map(|s| s.bindings().into_iter().map(str::to_owned)),
        );
        self.finish_bindings(names, f.drop_target.is_some(), f.result.line)
    }

    pub(super) fn finish_bindings(
        &mut self,
        names: Vec<String>,
        drop_receiver: bool,
        line: usize,
    ) -> Result<()> {
        for name in names.into_iter().rev() {
            let value = if let Some(id) = self.locals.places.get(&name).copied() {
                if self.storage.memory.get(id).is_err() {
                    continue;
                }
                let before = self.storage.memory.get(id)?.clone();
                if self.symbol_is_move_only(&before) {
                    self.validate_argument(&before, line)?;
                }
                self.take_symbol(id)?
            } else {
                let value = self
                    .locals
                    .values
                    .remove(&name)
                    .ok_or("unknown cleanup binding")?;
                if self.symbol_is_move_only(&value) {
                    self.validate_argument(&value, line)?;
                }
                value
            };
            if self.execution.phase == Phase::Runtime && !self.locals.ideal_bindings.contains(&name)
            {
                if name == "self" && drop_receiver {
                    self.cleanup_fields(value, line)?;
                } else {
                    self.cleanup_value(value, line)?;
                }
            }
        }
        Ok(())
    }

    // The destructor is already running. Consuming its complete receiver moves
    // all fields into locals; scope cleanup must not run the parent Drop again.
    pub(super) fn take_drop_receiver(&mut self, record: &str, expression: &Expr) -> Result<Symbol> {
        let value = self.storage(expression)?;
        self.compatible(&value.ty(), &Ty::Record(record.to_owned()), expression.line)?;
        self.validate_argument(&value, expression.line)?;
        let (reference, path) = self.location(expression)?;
        if !path.is_empty() {
            return Err("destructor receiver decomposition requires all of self".into());
        }
        let plane = self.storage.memory.plane(reference)?;
        self.take_symbol(plane)
    }

    fn cleanup_effects_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Union(_) => true,
            Type::Unique(_) | Type::Shared(_) => true,
            Type::Named(name) => {
                self.declarations
                    .destructors
                    .get(name)
                    .is_some_and(|f| !f.modifies.is_empty())
                    || self.declarations.structs.get(name).is_some_and(|s| {
                        s.runtime_fields()
                            .any(|(_, t)| self.cleanup_effects_type(t))
                    })
            }
            Type::Array(element, _) => self.cleanup_effects_type(element),
            _ => false, // References do not own their pointees.
        }
    }

    fn cleanup_effects(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Union(_) => true,
            Ty::Unique(_) | Ty::Shared(_) => true,
            Ty::Record(name) => self.cleanup_effects_type(&Type::Named(name.clone())),
            Ty::Array(element, _) => self.cleanup_effects(element),
            _ => false,
        }
    }

    pub(super) fn has_runtime_cleanup(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Union(_) => true,
            Ty::Array(inner, _) => self.has_runtime_cleanup(inner),
            Ty::Unique(_) | Ty::Shared(_) => true,
            Ty::Record(name) => crate::shared::ownership::needs_drop(
                &Type::Named(name.clone()),
                self.declarations.structs,
                self.declarations.drops,
            ),
            _ => false,
        }
    }

    pub(super) fn cleanup_value(&mut self, value: Symbol, line: usize) -> Result<()> {
        if matches!(value, Symbol::Union { .. }) {
            return Err(format!("line {line}: raw unions cannot be dropped implicitly; prove the active member and consume it"));
        }
        if self.execution.phase != Phase::Runtime {
            return Ok(());
        }
        let requires_drop = self.has_runtime_cleanup(&value.ty());
        // Callers validate before consuming storage. A value with no runtime
        // destructor must not be observed again after its own slot is invalid.
        if !requires_drop {
            return Ok(());
        }
        if self.symbol_is_move_only(&value) {
            self.validate_argument(&value, line)?;
        }
        // Reference-free cleanup can use its universal safety summary. A
        // receiver with references must be rechecked against actual aliases;
        // independent declaration ports may describe an impossible entry.
        if !self.cleanup_effects(&value.ty()) && !self.ty_has_reference(&value.ty()) {
            self.import_cleanup_safety(&value)?;
            return Ok(());
        }
        if let Symbol::Record(name, _) = &value {
            if let Some(method) = self.declarations.destructors.get(name).cloned() {
                return self.cleanup_method(value, method, line);
            }
        }
        self.cleanup_fields(value, line)
    }

    pub(super) fn cleanup_fields(&mut self, value: Symbol, line: usize) -> Result<()> {
        if self.execution.phase != Phase::Runtime {
            return Ok(());
        }
        self.charge_value_work(1)?;
        match value {
            Symbol::Shared(_, owner) => self.leak_shared(owner, line)?,
            Symbol::Unique(_, reference) => {
                let plane = self.storage.memory.plane(reference)?;
                let payload = self.take_symbol(plane)?;
                self.cleanup_value(payload, line)?;
            }
            Symbol::Record(name, mut fields) => {
                let order = self
                    .declarations
                    .structs
                    .get(&name)
                    .ok_or("unknown cleanup type")?
                    .runtime_fields()
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>();
                for name in order {
                    self.cleanup_value(fields.remove(&name).ok_or("missing cleanup field")?, line)?;
                }
            }
            Symbol::Array {
                items: Some(items), ..
            } => {
                for value in items {
                    self.cleanup_value(value, line)?;
                }
            }
            Symbol::Array {
                element,
                len,
                identity,
                cells,
                ..
            } if len != Linear::number(0)
                && (self.cleanup_effects(&element)
                    || (self.ty_has_reference(&element) && self.has_runtime_cleanup(&element))) =>
            {
                let Some(length) = constant_index(&len) else {
                    return Err("cleanup of opaque arrays with effects or reference-dependent destructors requires element summaries; unsupported".into());
                };
                // Cleanup observes every element when it has no universal
                // summary. Charge that demand before expanding any cells;
                // merely declaring or reading the array never does this.
                self.charge_value_work(length)?;
                for index in 0..length {
                    let value = self.read_array(
                        &element,
                        &identity,
                        &Linear::number(index as i128),
                        None,
                        &cells,
                    )?;
                    self.cleanup_value(value, line)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn cleanup_method(&mut self, receiver: Symbol, method: Function, line: usize) -> Result<()> {
        if self.execution.cleanup_depth >= 64 {
            return Err("cleanup nesting limit reached (64)".into());
        }
        self.charge_value_work(1)?;
        self.execution.cleanup_depth += 1;
        let name = method
            .drop_target
            .clone()
            .ok_or("cleanup method has no receiver type")?;
        self.note_cleanup_divergence(&method.name);
        let owner_scope = self.storage.memory.owner_scope();
        let saved = Scope::enter(self, &method, receiver);
        let checked = (|| -> Result<BTreeSet<PlaneId>> {
            self.capture_old(&method)?;
            let inputs = self.incoming_references(&method)?;
            let writes = self.write_places(&method, &inputs)?;
            // This method is elaborated against the actual receiver below.
            // Its postcondition is proved again, so overlapping ports do not
            // require the independent-input summary used by modular calls.
            let mut changed = BTreeSet::new();
            for write in &writes {
                let id = self.storage.memory.plane(write.reference)?;
                let owned =
                    self.owns_plane_in(&saved.env, &saved.roots, id)? || self.owns_plane(id)?;
                if !self.write_contract_permitted_by(&saved.writable, write, owned)? {
                    return Err(
                        "cleanup writes through a reference without a matching modifies contract"
                            .into(),
                    );
                }
                changed.insert(id);
            }
            self.storage.writable = writes;
            self.storage.inputs = inputs;
            let entry = self.clone_env()?;
            for statement in &method.body {
                self.statement(statement)?;
            }
            let value = self.scoped_eval(&method.result, Some(&Ty::Unit))?;
            self.validate_live(method.result.line)?;
            self.finish_scope(&method)?;
            self.storage.memory.require_owner_scope(&owner_scope)?;
            if let Some(post) = &method.post {
                self.execution.phase = Phase::Specification;
                self.locals.values = entry;
                self.locals.places.clear();
                self.locals.values.insert("result".into(), value);
                let facts = std::mem::take(&mut self.proof.facts);
                let goal = self.proposition(post)?;
                self.proof.facts = facts;
                self.prove_with(
                    &goal,
                    &format!("cleanup postcondition of {name}"),
                    post.line,
                    method.proof.as_deref(),
                )?;
            }
            Ok(changed)
        })();
        saved.restore(self);
        self.execution.cleanup_depth -= 1;
        let changed = checked.map_err(|error| {
            self.session.note_source(&error, method.source, method.line);
            format!("line {line}: cleanup of {name}: {error}")
        })?;
        if self.execution.replacing_cleanup != 0 {
            self.execution.deferred_cleanup_roots.extend(changed);
            return Ok(());
        }
        self.validate_cleanup_roots(changed, line)?;
        self.validate_live(line)
    }

    pub(super) fn finish_replacement_cleanup(&mut self, line: usize) -> Result<()> {
        if self.execution.replacing_cleanup != 0 {
            return Ok(());
        }
        let changed = std::mem::take(&mut self.execution.deferred_cleanup_roots);
        self.validate_cleanup_roots(changed, line)?;
        self.validate_live(line)
    }

    fn validate_cleanup_roots(&mut self, changed: BTreeSet<PlaneId>, line: usize) -> Result<()> {
        for id in changed {
            // A receiver may mutate its owned payload before child cleanup
            // releases it. Only surviving roots have post-state invariants.
            let Ok(current) = self.storage.memory.get(id) else {
                continue;
            };
            self.charge_value_work(symbol_weight(current)?)?;
            let current = self.storage.memory.get(id)?.clone();
            self.record_valid(&current, line)?;
            for (binding, root) in &self.locals.places {
                if *root == id {
                    self.locals.values.insert(binding.clone(), current.clone());
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
