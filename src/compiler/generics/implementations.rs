//! Generic impls attach ordinary methods and destruction to concrete records.
//! Method headers aid frontend name resolution; only demanded bodies survive
//! into verification. Headers never supply a trusted function summary.

use super::*;
use crate::syntax::{GenericImplementation, GenericImplementationKind};
use std::sync::Arc;

#[derive(Default)]
pub(super) struct Registry {
    implementations: BTreeMap<String, Vec<Arc<Implementation>>>,
    pub bodies: BTreeMap<String, MethodBody>,
    pub headers: Vec<Function>,
}

struct Implementation {
    parameters: Vec<GenericParameter>,
    pattern: Vec<GenericArgument>,
    kind: GenericImplementationKind,
    methods: Vec<Arc<Method>>,
}

pub(super) struct MethodBody {
    method: Arc<Method>,
    bindings: Arc<BTreeMap<String, GenericArgument>>,
    target: String,
}

struct Method {
    template: Template,
    header: Function,
    header_work: usize,
}

impl Registry {
    pub fn register(
        &mut self,
        source: GenericImplementation,
        templates: &BTreeMap<String, Template>,
        work: &mut usize,
    ) -> Result<()> {
        let Type::Apply(target, pattern) = &source.target else {
            return Err("generic impls require an explicit generic record target".into());
        };
        let Some(Template {
            declaration:
                GenericDeclaration::Record {
                    parameters,
                    definition,
                },
            ..
        }) = templates.get(target)
        else {
            return Err(format!(
                "generic impl requires a declared generic record {target}"
            ));
        };
        if source.module != definition.module {
            return Err(format!(
                "line {}: impl must be defined in the type's module",
                source.line
            ));
        }
        check_pattern(&source.parameters, pattern, parameters.len())?;
        let prior = self.implementations.entry(target.clone()).or_default();
        if source.kind != GenericImplementationKind::Inherent
            && prior
                .iter()
                .any(|implementation| implementation.kind == source.kind)
        {
            return Err("duplicate generic trait implementation".into());
        }
        let mut names = prior
            .iter()
            .flat_map(|implementation| implementation.methods.iter())
            .map(|method| method.header.name.clone())
            .collect::<BTreeSet<_>>();
        let mut methods = Vec::new();
        for function in source.functions {
            if !names.insert(function.name.clone()) {
                return Err(format!("duplicate generic method {}", function.name));
            }
            let mut header = header(&function);
            let header_work = templates::function_work(&mut header)?;
            let template = Template::new(GenericDeclaration::Function {
                parameters: Vec::new(),
                definition: Box::new(function),
            })?;
            charge_copy(work, template.body_work + header_work)?;
            methods.push(Arc::new(Method {
                template,
                header,
                header_work,
            }));
        }
        prior.push(Arc::new(Implementation {
            parameters: source.parameters,
            pattern: pattern.clone(),
            kind: source.kind,
            methods,
        }));
        Ok(())
    }

    pub fn install(
        &mut self,
        base: &str,
        actual: &[GenericArgument],
        target: &str,
        record: &mut Struct,
        pending: &mut VecDeque<Concrete>,
        work: &mut usize,
    ) -> Result<()> {
        let Some(implementations) = self.implementations.get(base) else {
            return Ok(());
        };
        for implementation in implementations {
            let mut bindings = bind(implementation, actual, work)?;
            bindings.insert(
                "Self".into(),
                GenericArgument::Type(Type::Named(target.to_owned())),
            );
            let bindings = Arc::new(bindings);
            if implementation.kind == GenericImplementationKind::Copy {
                record.copy = true;
            }
            for method in &implementation.methods {
                let body = MethodBody {
                    method: method.clone(),
                    bindings: bindings.clone(),
                    target: target.to_owned(),
                };
                if implementation.kind == GenericImplementationKind::Drop {
                    let mut function = body.instantiate(work)?;
                    function.name = format!("evg_drop_{target}");
                    function.drop_target = Some(target.to_owned());
                    function.impl_target = None;
                    pending.push_back(Concrete::Destructor(target.to_owned(), function));
                } else {
                    charge_copy(work, method.header_work)?;
                    let mut header = method.header.clone();
                    Substitution {
                        bindings: &bindings,
                        work,
                    }
                    .function(&mut header)?;
                    header.name = format!("{target}::{}", header.name);
                    header.impl_target = Some(target.to_owned());
                    self.bodies.insert(header.name.clone(), body);
                    self.headers.push(header);
                }
            }
        }
        Ok(())
    }
}

impl MethodBody {
    pub fn instantiate(&self, work: &mut usize) -> Result<Box<Function>> {
        charge_copy(work, self.method.template.body_work)?;
        let GenericDeclaration::Function { mut definition, .. } =
            self.method.template.declaration.clone()
        else {
            return Err("invalid method template".into());
        };
        if definition
            .params
            .iter()
            .any(|(name, _)| self.bindings.contains_key(name))
        {
            return Err("runtime parameters cannot shadow generic parameters".into());
        }
        Substitution {
            bindings: &self.bindings,
            work,
        }
        .function(&mut definition)?;
        definition.name = format!("{}::{}", self.target, definition.name);
        definition.impl_target = Some(self.target.clone());
        definition.drop_target = None;
        Ok(definition)
    }
}

fn check_pattern(
    parameters: &[GenericParameter],
    pattern: &[GenericArgument],
    arity: usize,
) -> Result<()> {
    if pattern.len() != arity || parameters.len() != arity {
        return Err("generic impl target must bind every record parameter exactly once".into());
    }
    let mut seen = BTreeSet::new();
    for argument in pattern {
        let name = match argument {
            GenericArgument::Type(Type::Named(name)) => name,
            GenericArgument::Const(Expr {
                kind: Kind::Name(name),
                ..
            }) => name,
            _ => return Err("generic impl specialization patterns are not implemented yet".into()),
        };
        let Some(parameter) = parameters.iter().find(|parameter| parameter.name() == name) else {
            return Err("generic impl target arguments must name its parameters".into());
        };
        let same_kind = matches!(
            (parameter, argument),
            (
                GenericParameter::Type { default: None, .. },
                GenericArgument::Type(_)
            ) | (
                GenericParameter::Const { default: None, .. },
                GenericArgument::Const(_)
            )
        );
        if !same_kind || !seen.insert(name.clone()) {
            return Err(
                "generic impl parameters must have matching kinds, no defaults, and no repetitions"
                    .into(),
            );
        }
    }
    Ok(())
}

fn bind(
    implementation: &Implementation,
    actual: &[GenericArgument],
    work: &mut usize,
) -> Result<BTreeMap<String, GenericArgument>> {
    let mut bindings = BTreeMap::new();
    for (pattern, value) in implementation.pattern.iter().zip(actual) {
        let name = match pattern {
            GenericArgument::Type(Type::Named(name)) => name,
            GenericArgument::Const(Expr {
                kind: Kind::Name(name),
                ..
            }) => name,
            _ => return Err("invalid generic implementation pattern".into()),
        };
        if let GenericArgument::Type(ty) = value {
            charge_type(work, ty)?;
        }
        bindings.insert(name.clone(), value.clone());
    }
    for parameter in &implementation.parameters {
        match (parameter, &bindings[parameter.name()]) {
            (GenericParameter::Type { .. }, GenericArgument::Type(_)) => {}
            (GenericParameter::Const { ty, .. }, GenericArgument::Const(value)) => {
                let mut ty = ty.clone();
                Substitution {
                    bindings: &bindings,
                    work,
                }
                .ty(&mut ty)?;
                constants::canonical(value, &ty)?;
            }
            _ => return Err("generic impl argument kind does not match its parameter".into()),
        }
    }
    Ok(bindings)
}

fn header(source: &Function) -> Function {
    Function {
        impl_target: source.impl_target.clone(),
        receiver: source.receiver,
        name: source.name.clone(),
        external: None,
        params: source.params.clone(),
        ret: source.ret.clone(),
        pre: None,
        post: None,
        decreases: None,
        borrows: Vec::new(),
        body: Vec::new(),
        result: Expr {
            kind: Kind::Unit,
            line: source.line,
        },
        proof: None,
        line: source.line,
        drop_target: None,
        ideal: source.ideal,
        modifies: Vec::new(),
        ideal_params: source.ideal_params.clone(),
        module: source.module.clone(),
        partial: false,
        entry_memory: false,
    }
}
