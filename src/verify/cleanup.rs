//! Cleanup elaboration. Effectful destructors are checked against the actual
//! receiver so child cleanup sees fields changed by its parent's body.
use super::*;

struct Scope {
    env: BTreeMap<String, Symbol>,
    roots: BTreeMap<String, PlaneId>,
    facts: BTreeMap<String, Expr>,
    proofs: BTreeMap<String, Formula>,
    module: Option<String>,
    phase: Phase,
    current: Option<String>,
    measure: Option<Linear>,
    opened: BTreeMap<String, BTreeSet<String>>,
    opened_planes: BTreeMap<PlaneId, BTreeSet<String>>,
    dropping: bool,
    writable: Vec<WritePlace>,
    inputs: Vec<InputReference>,
    old_values: BTreeMap<String, Symbol>,
    old_memory: Option<Box<EntryMemory>>,
    ideal: BTreeSet<String>,
    temporaries: Vec<(Symbol, usize)>,
}
impl Scope {
    fn enter(ctx: &mut Context<'_>, f: &Function, receiver: Symbol) -> Self {
        let saved = Self {
            env: std::mem::take(&mut ctx.env),
            roots: std::mem::take(&mut ctx.roots),
            facts: std::mem::take(&mut ctx.facts),
            proofs: std::mem::take(&mut ctx.proofs),
            module: std::mem::replace(&mut ctx.module, f.module.clone()),
            phase: std::mem::replace(&mut ctx.phase, Phase::Runtime),
            current: ctx.current.replace(f.name.clone()),
            measure: ctx.measure.take(),
            opened: std::mem::take(&mut ctx.opened),
            opened_planes: std::mem::take(&mut ctx.opened_planes),
            dropping: std::mem::replace(&mut ctx.dropping, true),
            writable: std::mem::take(&mut ctx.writable),
            inputs: std::mem::take(&mut ctx.input_references),
            old_values: std::mem::take(&mut ctx.old_values),
            old_memory: ctx.old_memory.take(),
            ideal: std::mem::take(&mut ctx.ideal_bindings),
            temporaries: std::mem::take(&mut ctx.temporaries),
        };
        ctx.env.insert("self".into(), receiver);
        saved
    }
    fn restore(self, ctx: &mut Context<'_>) {
        ctx.env = self.env;
        ctx.roots = self.roots;
        ctx.facts = self.facts;
        ctx.proofs = self.proofs;
        ctx.module = self.module;
        ctx.phase = self.phase;
        ctx.current = self.current;
        ctx.measure = self.measure;
        ctx.opened = self.opened;
        ctx.opened_planes = self.opened_planes;
        ctx.dropping = self.dropping;
        ctx.writable = self.writable;
        ctx.input_references = self.inputs;
        ctx.old_values = self.old_values;
        ctx.old_memory = self.old_memory;
        ctx.ideal_bindings = self.ideal;
        ctx.temporaries = self.temporaries;
    }
}

impl Context<'_> {
    fn cleanup_effects_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Named(name) => {
                self.destructors
                    .get(name)
                    .is_some_and(|f| !f.modifies.is_empty())
                    || self
                        .structs
                        .get(name)
                        .is_some_and(|s| s.fields.iter().any(|(_, t)| self.cleanup_effects_type(t)))
            }
            Type::Array(element, _) => self.cleanup_effects_type(element),
            _ => false, // References do not own their pointees.
        }
    }
    fn cleanup_effects(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Record(name) => self.cleanup_effects_type(&Type::Named(name.clone())),
            Ty::Array(element, _) => self.cleanup_effects(element),
            _ => false,
        }
    }

    pub(super) fn cleanup_value(&mut self, value: Symbol, line: usize) -> Result<()> {
        if self.phase != Phase::Runtime {
            return Ok(());
        }
        if self.symbol_is_affine(&value) {
            self.validate_argument(&value, line)?;
        }
        // Effect-free methods are checked universally at their declarations.
        // Revalidate each receiver here, including later siblings whose type
        // may have been affected by an earlier sibling's cleanup.
        if !self.cleanup_effects(&value.ty()) {
            return Ok(());
        }
        if let Symbol::Record(name, _) = &value {
            if let Some(method) = self.destructors.get(name).cloned() {
                return self.cleanup_method(value, method, line);
            }
        }
        self.cleanup_fields(value, line)
    }

    pub(super) fn cleanup_fields(&mut self, value: Symbol, line: usize) -> Result<()> {
        if self.phase != Phase::Runtime {
            return Ok(());
        }
        self.charge_value_work(1)?;
        match value {
            Symbol::Record(name, mut fields) => {
                let order = self
                    .structs
                    .get(&name)
                    .ok_or("unknown cleanup type")?
                    .fields
                    .iter()
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
            Symbol::Array { element, len, .. }
                if len != Linear::number(0) && self.cleanup_effects(&element) =>
            {
                return Err("cleanup of opaque arrays with external effects requires element summaries; unsupported".into());
            }
            _ => {}
        }
        Ok(())
    }

    fn cleanup_method(&mut self, receiver: Symbol, method: Function, line: usize) -> Result<()> {
        if self.cleanup_depth >= 64 {
            return Err("cleanup nesting limit reached (64)".into());
        }
        self.charge_value_work(1)?;
        self.cleanup_depth += 1;
        let name = method
            .drop_target
            .clone()
            .ok_or("cleanup method has no receiver type")?;
        let saved = Scope::enter(self, &method, receiver);
        let checked = (|| -> Result<BTreeSet<PlaneId>> {
            self.capture_old(&method)?;
            let inputs = self.incoming_references(&method, true)?;
            let writes = self.write_places(&method, &inputs)?;
            // This method is elaborated against the actual receiver below.
            // Its postcondition is proved again, so overlapping ports do not
            // require the independent-input summary used by modular calls.
            let mut changed = BTreeSet::new();
            for write in &writes {
                let id = self.memory.plane(write.reference)?;
                let owned = saved.roots.values().any(|root| *root == id);
                if !self.write_permitted_by(&saved.writable, write.reference, &write.path, owned)? {
                    return Err(
                        "cleanup writes through a reference without a matching modifies contract"
                            .into(),
                    );
                }
                changed.insert(id);
            }
            self.writable = writes;
            self.input_references = inputs;
            let entry = self.clone_env()?;
            for statement in &method.body {
                self.statement(statement)?;
            }
            let value = self.scoped_eval(&method.result, Some(&Ty::Unit))?;
            self.validate_live(method.result.line)?;
            self.finish_scope(&method)?;
            if let Some(post) = &method.post {
                self.phase = Phase::Specification;
                self.env = entry;
                self.roots.clear();
                self.env.insert("result".into(), value);
                let facts = std::mem::take(&mut self.facts);
                let goal = self.proposition(post)?;
                self.facts = facts;
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
        self.cleanup_depth -= 1;
        let changed =
            checked.map_err(|error| format!("line {line}: cleanup of {name}: {error}"))?;
        for id in changed {
            self.charge_value_work(symbol_weight(self.memory.get(id)?)?)?;
            let current = self.memory.get(id)?.clone();
            self.record_valid(&current, line)?;
            for (binding, root) in &self.roots {
                if *root == id {
                    self.env.insert(binding.clone(), current.clone());
                }
            }
        }
        self.validate_live(line)
    }
}
