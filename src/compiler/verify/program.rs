//! Program verification in dependency order. Only checked callees are
//! published to later functions; the current recursive summary is the sole
//! exception, governed by the existing termination and phase checks.

use super::*;

pub(super) fn verify(
    mut parsed: syntax::Program,
    session: &mut Session,
) -> Result<VerifiedProgram> {
    prepare(&mut parsed)?;
    let structs = check_records(&parsed, session)?;
    let (drops, destructors) = check_destructors(&parsed.destructors, &structs)?;
    let mut functions = parsed.functions;
    functions.extend(parsed.destructors.into_iter().map(|(_, f)| f));
    let mut verification = Verification {
        structs,
        drops,
        destructors,
        functions: BTreeMap::new(),
        helpers: BTreeSet::new(),
        cleanup_helpers: BTreeSet::new(),
        obligations: 0,
    };
    for function in &mut functions {
        verification.check_function(function, session)?;
    }
    Ok(verification.finish(functions, session))
}

fn prepare(parsed: &mut syntax::Program) -> Result<()> {
    crate::compiler::methods::validate(parsed)?;
    crate::compiler::copy::configure(parsed)?;
    crate::compiler::scalar_types::lower(parsed)?;
    crate::compiler::declarations::schedule_types(parsed)?;
    check_type_expansion(&parsed.structs)?;
    crate::compiler::field_sugar::expand(parsed);
    crate::compiler::declarations::schedule_functions(parsed)?;
    Ok(())
}

fn check_records(
    parsed: &syntax::Program,
    session: &mut Session,
) -> Result<BTreeMap<String, Struct>> {
    let mut structs = BTreeMap::new();
    let copy_forbidden = parsed
        .destructors
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<BTreeSet<_>>();
    for s in &parsed.structs {
        crate::compiler::copy::validate(s, &structs, &copy_forbidden)?;
        if structs.contains_key(&s.name) {
            return Err(format!("line {}: duplicate struct {}", s.line, s.name));
        }
        check_record(s, &structs, session)?;
        structs.insert(s.name.clone(), s.clone());
    }
    Ok(structs)
}

fn check_record(
    s: &Struct,
    structs: &BTreeMap<String, Struct>,
    session: &mut Session,
) -> Result<()> {
    let empty_functions = BTreeMap::new();
    let empty_drops = BTreeSet::new();
    let empty_destructors = BTreeMap::new();
    let mut ctx = Context::new(
        &empty_functions,
        structs,
        &empty_drops,
        &empty_destructors,
        &empty_drops,
        &empty_drops,
        session,
    );
    ctx.module = s.module.clone();
    ctx.declaring = Some(s.name.clone());
    ctx.phase = if s.ideal {
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
        if n == "self" || ctx.env.contains_key(n) {
            return Err(format!("line {}: duplicate or reserved field {n}", s.line));
        }
        let phase = ctx.phase;
        if s.ideal_fields.contains(n) && ctx.phase == Phase::Runtime {
            ctx.phase = Phase::Ideal;
        }
        let t = ctx.resolve(t)?;
        let value = ctx.arbitrary(&t)?;
        ctx.phase = phase;
        ctx.env.insert(n.clone(), value);
    }
    let fields = ctx.clone_env()?;
    ctx.env
        .insert("self".into(), Symbol::Record(s.name.clone(), fields));
    for (name, proposition) in &s.facts {
        ctx.fresh_binding(name, proposition.line)?;
        ctx.proposition(proposition)?;
        ctx.facts.insert(name.clone(), proposition.clone());
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
    helpers: BTreeSet<String>,
    cleanup_helpers: BTreeSet<String>,
    obligations: usize,
}

impl Verification {
    fn check_signature(&self, f: &Function) -> Result<()> {
        for (name, ty) in &f.params {
            if f.ideal_params.contains(name) && !erased_type(ty, &self.structs) {
                return Err(format!("line {}: ideal parameters may own only proof data; runtime owners must be borrowed", f.line));
            }
            if f.ideal
                && is_affine(ty, &self.structs, &self.drops)
                && !erased_type(ty, &self.structs)
            {
                return Err(format!(
                    "line {}: ideal functions may borrow runtime ownership but cannot consume it",
                    f.line
                ));
            }
        }
        if f.ideal
            && is_affine(&f.ret, &self.structs, &self.drops)
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
                "move" | "drop" | "alloc" | "integer" | "nat" | "old"
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
            || !f.ideal && f.decreases.is_none() && crate::compiler::effects::recursive(f);
        self.check_signature(f)?;
        if f.decreases.is_some() || f.partial {
            self.functions.insert(f.name.clone(), f.clone());
        }
        let (obligations, partial) = {
            let mut ctx = Context::new(
                &self.functions,
                &self.structs,
                &self.drops,
                &self.destructors,
                &self.helpers,
                &self.cleanup_helpers,
                session,
            );
            ctx.enter_function(f)?;
            ctx.check_declaration_body(f)?;
            (ctx.obligations, ctx.partial_execution)
        };
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
            structs: self.structs,
            obligations: self.obligations,
            drops: self.drops,
            cleanup_helpers: self.cleanup_helpers,
            trusted: session.trusted_assumptions().to_vec(),
            proof_searches: session.search_count(),
        }
    }
}

impl Context<'_> {
    fn enter_function(&mut self, f: &Function) -> Result<()> {
        self.module = f.module.clone();
        self.ideal_execution = f.ideal;
        self.partial_execution = f.partial;
        self.dropping = f.drop_target.is_some();
        let execution = if f.ideal {
            Phase::Ideal
        } else {
            Phase::Runtime
        };
        self.phase = execution;
        self.ideal_bindings = f.ideal_params.iter().cloned().collect();
        self.current = Some(f.name.clone());
        self.declare_parameters(f)?;
        self.capture_old(f)?;
        if let Some(pre) = &f.pre {
            self.phase = Phase::Specification;
            let p = self.eval(pre, Some(&Ty::Bool))?.proposition()?;
            self.assume(&p)?;
            self.phase = execution;
        }
        Ok(())
    }

    fn check_declaration_body(&mut self, f: &Function) -> Result<()> {
        let inputs = if f.modifies.is_empty() && f.borrows.is_empty() {
            Vec::new()
        } else {
            self.incoming_references(f, !f.modifies.is_empty())?
        };
        self.writable = self.write_places(f, &inputs)?;
        self.input_references = inputs.clone();
        let ret = self.resolve(&f.ret)?;
        if let Some(measure) = &f.decreases {
            self.phase = Phase::Specification;
            self.measure = Some(self.nonnegative(measure, "nonnegative recursion measure")?);
            self.phase = if f.ideal {
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
