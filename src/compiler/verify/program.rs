//! Program verification in dependency order. Only checked callees are
//! published to later functions; the current recursive summary is the sole
//! exception, governed by the existing termination and phase checks.

use super::*;

pub(super) fn verify(
    mut parsed: syntax::Program,
    session: &mut Session,
) -> Result<VerifiedProgram> {
    prepare(&mut parsed)?;
    // These headers validate Drop ownership/module declarations only. Contexts
    // see a record after its fields and refinement have actually been checked.
    let mut headers = BTreeMap::new();
    for s in &parsed.structs {
        if headers.insert(s.name.clone(), s.clone()).is_some() {
            return Err(format!("line {}: duplicate struct {}", s.line, s.name));
        }
    }
    let (drops, destructors) = check_destructors(&parsed.destructors, &headers)?;
    let mut functions = parsed.functions;
    functions.extend(parsed.destructors.into_iter().map(|(_, f)| f));
    let mut verification = Verification {
        structs: BTreeMap::new(),
        drops,
        destructors,
        functions: BTreeMap::new(),
        summaries: BTreeMap::new(),
        helpers: BTreeSet::new(),
        cleanup_helpers: BTreeSet::new(),
        obligations: 0,
    };
    for declaration in
        crate::compiler::declarations::verification_order(&parsed.structs, &functions)?
    {
        match declaration {
            crate::compiler::declarations::Declaration::Record(index) => {
                let record = &parsed.structs[index];
                crate::compiler::copy::validate(
                    record,
                    &verification.structs,
                    &verification.drops,
                )?;
                check_record(record, verification.declarations(), session)?;
                verification
                    .structs
                    .insert(record.name.clone(), record.clone());
            }
            crate::compiler::declarations::Declaration::Function(index) => {
                let function = &mut functions[index];
                verification
                    .check_function(function, session)
                    .map_err(|error| {
                        if error.starts_with("line ") {
                            error
                        } else {
                            format!(
                                "line {}: while checking {}: {error}",
                                function.line, function.name
                            )
                        }
                    })?;
            }
        }
    }
    Ok(verification.finish(functions, session))
}

fn prepare(parsed: &mut syntax::Program) -> Result<()> {
    crate::shared::target::native()?;
    crate::compiler::methods::validate(parsed)?;
    crate::compiler::copy::configure(parsed)?;
    crate::compiler::scalar_types::lower(parsed)?;
    crate::compiler::declarations::schedule_types(parsed)?;
    check_type_expansion(&parsed.structs)?;
    crate::compiler::field_sugar::expand(parsed);
    Ok(())
}

fn check_record(s: &Struct, declarations: Declarations<'_>, session: &mut Session) -> Result<()> {
    let structs = declarations.structs;
    let mut ctx = Context::new(declarations, session);
    ctx.locals.module = s.module.clone();
    ctx.locals.declaring = Some(s.name.clone());
    ctx.execution.phase = if s.ideal {
        Phase::Ideal
    } else {
        Phase::Runtime
    };
    for (n, t) in &s.fields {
        if s.ideal_fields.contains(n) && !erased_type(t, structs) {
            return Err(format!(
                "line {}: ideal field {n} may own only proof data; runtime owners must be borrowed",
                s.line
            ));
        }
        if !s.ideal && !s.ideal_fields.contains(n) && !runtime_type(t, structs) {
            return Err(format!(
                "line {}: field {n} needs a runtime layout; use ideal type for proof data",
                s.line
            ));
        }
        if n == "self" || ctx.locals.values.contains_key(n) {
            return Err(format!("line {}: duplicate or reserved field {n}", s.line));
        }
        let phase = ctx.execution.phase;
        if s.ideal_fields.contains(n) && ctx.execution.phase == Phase::Runtime {
            ctx.execution.phase = Phase::Ideal;
        }
        let t = ctx.resolve(t)?;
        let value = ctx.arbitrary(&t)?;
        ctx.execution.phase = phase;
        ctx.locals.values.insert(n.clone(), value);
    }
    let fields = ctx.clone_env()?;
    ctx.locals
        .values
        .insert("self".into(), Symbol::Record(s.name.clone(), fields));
    for (name, proposition) in &s.facts {
        ctx.fresh_binding(name, proposition.line)?;
        ctx.proposition(proposition)?;
        ctx.proof.facts.insert(name.clone(), proposition.clone());
    }
    if let Some(p) = &s.invariant {
        ctx.proposition(p)?;
    }
    Ok(())
}

fn check_destructors(
    declarations: &[(String, Function)],
    structs: &BTreeMap<String, Struct>,
) -> Result<(BTreeSet<String>, BTreeMap<String, Function>)> {
    let mut drops = BTreeSet::new();
    for (target, f) in declarations {
        if structs.get(target).is_some_and(|s| s.module != f.module) {
            return Err(format!(
                "line {}: Drop must be defined in the type's defining module",
                f.line
            ));
        }
        if structs.get(target).is_some_and(|s| s.ideal) {
            return Err(format!(
                "line {}: ideal data has no runtime Drop implementation",
                f.line
            ));
        }
        if !structs.contains_key(target) || !drops.insert(target.clone()) {
            return Err(format!(
                "line {}: unknown or duplicate Drop implementation for {target}",
                f.line
            ));
        }
        if !destructor_body(&f.body) || !destructor_expression(&f.result) {
            return Err(format!("line {}: destructor effects require proofs; Drop bodies allow scalar work, checked scalar helpers, borrows, facts, and a complete pattern of self; other ownership construction/destructuring is unsupported", f.line));
        }
    }
    let destructors = declarations
        .iter()
        .map(|(name, method)| {
            let mut method = method.clone();
            method.entry_memory = needs_old_memory(&method);
            (name.clone(), method)
        })
        .collect::<BTreeMap<_, _>>();
    Ok((drops, destructors))
}

struct Verification {
    structs: BTreeMap<String, Struct>,
    drops: BTreeSet<String>,
    destructors: BTreeMap<String, Function>,
    functions: BTreeMap<String, Function>,
    summaries: BTreeMap<String, summaries::Summary>,
    helpers: BTreeSet<String>,
    cleanup_helpers: BTreeSet<String>,
    obligations: usize,
}

impl Verification {
    fn declarations(&self) -> Declarations<'_> {
        Declarations {
            functions: &self.functions,
            summaries: &self.summaries,
            structs: &self.structs,
            drops: &self.drops,
            destructors: &self.destructors,
            helpers: &self.helpers,
            cleanup_helpers: &self.cleanup_helpers,
        }
    }

    fn check_signature(&self, f: &Function) -> Result<()> {
        for (name, ty) in &f.params {
            if f.ideal_params.contains(name) && !erased_type(ty, &self.structs) {
                return Err(format!("line {}: ideal parameters may own only proof data; runtime owners must be borrowed", f.line));
            }
            if f.ideal
                && is_move_only(ty, &self.structs, &self.drops)
                && !erased_type(ty, &self.structs)
            {
                return Err(format!(
                    "line {}: ideal functions may borrow runtime ownership but cannot consume it",
                    f.line
                ));
            }
        }
        if f.ideal
            && is_move_only(&f.ret, &self.structs, &self.drops)
            && !erased_type(&f.ret, &self.structs)
        {
            return Err(format!(
                "line {}: ideal functions cannot produce runtime ownership",
                f.line
            ));
        }
        if !f.modifies.is_empty() {
            let references = f
                .params
                .iter()
                .filter(|(_, t)| type_has_reference(t, &self.structs))
                .collect::<Vec<_>>();
            if f.modifies.iter().any(|expression| {
                !borrow_expression(expression)
                    || !references
                        .iter()
                        .any(|(name, _)| Some(name.as_str()) == effect_origin(expression))
            }) {
                return Err(format!("line {}: modifies requires projections of incoming reference-bearing parameters", f.line));
            }
        }
        if !f.ideal
            && (!runtime_type(&f.ret, &self.structs)
                || f.params
                    .iter()
                    .any(|(n, t)| !f.ideal_params.contains(n) && !runtime_type(t, &self.structs)))
        {
            return Err(format!("line {}: runtime signatures require fixed-layout types; integer/nat and ideal records are proof-only", f.line));
        }
        if MachineInt::parse(f.name.rsplit("::").next().unwrap_or(&f.name)).is_some()
            || matches!(
                f.name.rsplit("::").next().unwrap_or(&f.name),
                "move"
                    | "drop"
                    | "alloc"
                    | "integer"
                    | "nat"
                    | "old"
                    | "typeof"
                    | "shape"
                    | "owners"
                    | "share_owner"
                    | "duplicate_owner"
                    | "release_owner"
                    | "recover_owner"
            )
        {
            return Err(format!("line {}: {} is a reserved builtin", f.line, f.name));
        }
        returns::check_return_borrows(f, &self.structs)?;
        if self.functions.contains_key(&f.name) {
            return Err(format!("line {}: duplicate function {}", f.line, f.name));
        }
        Ok(())
    }

    fn check_function(&mut self, f: &mut Function, session: &mut Session) -> Result<()> {
        f.entry_memory = needs_old_memory(f);
        f.partial = f.external.is_some()
            || !f.ideal && crate::compiler::effects::unmeasured_loops(f)
            || !f.ideal && f.decreases.is_none() && crate::compiler::effects::recursive(f);
        self.check_signature(f)?;
        if f.decreases.is_some() || f.partial {
            self.functions.insert(f.name.clone(), f.clone());
        }
        let (obligations, partial, summary) = cases::check(f, self.declarations(), session)?;
        self.summaries.insert(f.name.clone(), summary);
        self.obligations += obligations;
        f.partial = partial;
        if crate::compiler::effects::invariant_independent(
            f,
            &self.functions,
            &self.helpers,
            &self.structs,
        ) {
            self.helpers.insert(f.name.clone());
        }
        if crate::compiler::effects::ownership_free(
            f,
            &self.functions,
            &self.cleanup_helpers,
            &self.structs,
        ) {
            self.cleanup_helpers.insert(f.name.clone());
        }
        self.functions.insert(f.name.clone(), f.clone());
        Ok(())
    }

    fn finish(self, functions: Vec<Function>, session: &Session) -> VerifiedProgram {
        VerifiedProgram {
            functions,
            summaries: self.summaries,
            structs: self.structs,
            obligations: self.obligations,
            drops: self.drops,
            trusted: session.trusted_assumptions().to_vec(),
            proof_searches: session.search_count(),
        }
    }
}

impl Context<'_> {
    pub(super) fn enter_function(&mut self, f: &Function) -> Result<()> {
        self.locals.module = f.module.clone();
        self.execution.ideal_execution = f.ideal;
        self.execution.partial_execution = f.partial;
        self.execution.dropping = f.drop_target.is_some();
        let execution = if f.ideal {
            Phase::Ideal
        } else {
            Phase::Runtime
        };
        self.execution.phase = execution;
        self.locals.ideal_bindings = f.ideal_params.iter().cloned().collect();
        self.execution.current = Some(f.name.clone());
        self.declare_parameters(f)?;
        self.capture_old(f)?;
        if let Some(pre) = &f.pre {
            self.execution.phase = Phase::Specification;
            let p = self.eval(pre, Some(&Ty::Bool))?.proposition()?;
            self.assume(&p)?;
            self.execution.phase = execution;
        }
        Ok(())
    }

    pub(super) fn check_declaration_body(&mut self, f: &Function) -> Result<()> {
        let inputs = if f.modifies.is_empty() && f.borrows.is_empty() {
            Vec::new()
        } else {
            self.incoming_references(f)?
        };
        self.storage.writable = self.write_places(f, &inputs)?;
        self.storage.inputs = inputs.clone();
        let ret = self.resolve(&f.ret)?;
        if let Some(measure) = &f.decreases {
            self.execution.phase = Phase::Specification;
            self.execution.measure =
                Some(self.nonnegative(measure, "nonnegative recursion measure")?);
            self.execution.phase = if f.ideal {
                Phase::Ideal
            } else {
                Phase::Runtime
            };
        }
        if f.external.is_some() {
            self.check_external(f, &ret)?;
        } else {
            self.check_function_body(f, &ret, &inputs, true)?;
        }
        Ok(())
    }
}
