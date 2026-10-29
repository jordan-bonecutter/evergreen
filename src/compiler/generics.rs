//! Concrete specialization before ordinary declaration and proof checking.
//! An uninstantiated template is syntax, not a verified universal theorem.

use crate::syntax::{
    self,
    visit::{self, Visitor},
    Expr, Function, GenericArgument, GenericDeclaration, GenericParameter, Kind, Program,
    Statement, Struct, Type,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

mod constants;
mod discovery;
mod implementations;
mod inference;
mod substitute;
mod templates;
#[cfg(test)]
mod tests;
use substitute::Substitution;
use templates::Template;

type Result<T> = std::result::Result<T, String>;

fn charge(work: &mut usize) -> Result<()> {
    charge_copy(work, 1)
}

fn charge_copy(work: &mut usize, amount: usize) -> Result<()> {
    *work = work
        .checked_add(amount)
        .ok_or("generic expansion work exhausted")?;
    if *work > 100_000 {
        return Err("generic expansion work limit reached".into());
    }
    Ok(())
}

fn charge_type(work: &mut usize, ty: &Type) -> Result<()> {
    let mut pending = vec![(ty, 0)];
    while let Some((ty, depth)) = pending.pop() {
        charge(work)?;
        if depth >= 128 {
            return Err("generic type expansion depth limit reached".into());
        }
        match ty {
            Type::Named(name) => charge_copy(work, name.len() / 32)?,
            Type::Ref(inner)
            | Type::Unique(inner)
            | Type::Shared(inner)
            | Type::Shape(inner)
            | Type::Array(inner, _) => pending.push((inner, depth + 1)),
            Type::Union(members) => pending.extend(members.iter().map(|ty| (ty, depth + 1))),
            Type::Apply(..) => {
                return Err("generic substitution requires closed type arguments".into())
            }
            _ => {}
        }
    }
    Ok(())
}

enum Concrete {
    Record(Box<Struct>),
    Function(Box<Function>),
    Destructor(String, Box<Function>),
}

struct Engine {
    target: crate::compiler::TargetKind,
    implementations: implementations::Registry,
    inference: inference::Inference,
    known_types: BTreeSet<String>,
    templates: BTreeMap<String, Template>,
    instances: HashMap<(String, Vec<GenericArgument>), String>,
    pending: VecDeque<Concrete>,
    work: usize,
    depth: usize,
}

pub(super) fn lower_for(program: &mut Program, target: crate::compiler::TargetKind) -> Result<()> {
    if program.generics.is_empty() {
        return Ok(());
    }
    let mut engine = Engine {
        target,
        implementations: implementations::Registry::default(),
        inference: inference::Inference::default(),
        known_types: program
            .structs
            .iter()
            .map(|record| record.name.clone())
            .collect(),
        templates: BTreeMap::new(),
        instances: HashMap::new(),
        pending: VecDeque::new(),
        work: 0,
        depth: 0,
    };
    let mut implementations = Vec::new();
    for declaration in std::mem::take(&mut program.generics) {
        let name = match &declaration {
            GenericDeclaration::Implementation(_) => {
                let GenericDeclaration::Implementation(implementation) = declaration else {
                    return Err("invalid implementation declaration".into());
                };
                implementations.push(*implementation);
                continue;
            }
            GenericDeclaration::Record { definition, .. } => &definition.name,
            GenericDeclaration::Function { definition, .. } => &definition.name,
        };
        if program.structs.iter().any(|s| &s.name == name)
            || program.functions.iter().any(|f| &f.name == name)
            || engine.templates.contains_key(name)
        {
            return Err(format!("duplicate generic declaration {name}"));
        }
        let name = name.clone();
        if let GenericDeclaration::Function { definition, .. } = &declaration {
            if syntax::is_builtin_name(&definition.name) {
                return Err(format!(
                    "line {}: {} is a reserved builtin",
                    definition.line, definition.name
                ));
            }
        }
        let template = Template::new(declaration)?;
        charge_copy(
            &mut engine.work,
            template.parameter_work + template.body_work,
        )?;
        engine.templates.insert(name, template);
    }
    for implementation in implementations {
        engine
            .implementations
            .register(implementation, &engine.templates, &mut engine.work)?;
    }
    engine
        .inference
        .register_program(program, &mut engine.work)?;
    for record in &mut program.structs {
        engine.record(record)?;
    }
    for function in program
        .functions
        .iter_mut()
        .chain(program.destructors.iter_mut().map(|(_, f)| f))
    {
        engine.function(function)?;
    }
    engine.finish(program)
}

impl Engine {
    fn specialize(
        &mut self,
        name: &str,
        arguments: Vec<GenericArgument>,
        record: bool,
    ) -> Result<String> {
        charge_copy(&mut self.work, 1 + name.len() / 32)?;
        let template = self
            .templates
            .get(name)
            .ok_or_else(|| format!("unknown generic declaration {name}"))?;
        charge_copy(&mut self.work, template.parameter_work)?;
        let parameters = match &template.declaration {
            GenericDeclaration::Record { parameters, .. } if record => parameters,
            GenericDeclaration::Function { parameters, .. } if !record => parameters,
            _ => {
                return Err(format!(
                    "generic {name} used in the wrong declaration context"
                ))
            }
        }
        .clone();
        if arguments.len() > parameters.len() {
            return Err(format!("too many generic arguments for {name}"));
        }
        let mut supplied = arguments.into_iter();
        let mut bindings = BTreeMap::new();
        let mut key = Vec::new();
        for parameter in &parameters {
            let mut argument = match (supplied.next(), parameter) {
                (Some(argument), _) => argument,
                (
                    None,
                    GenericParameter::Type {
                        default: Some(ty), ..
                    },
                ) => GenericArgument::Type(ty.clone()),
                (
                    None,
                    GenericParameter::Const {
                        default: Some(value),
                        ..
                    },
                ) => GenericArgument::Const(value.clone()),
                _ => {
                    return Err(format!(
                        "missing generic argument {} for {name}",
                        parameter.name()
                    ))
                }
            };
            Substitution {
                bindings: &bindings,
                work: &mut self.work,
            }
            .argument(&mut argument)?;
            let argument = match (parameter, argument) {
                (GenericParameter::Type { .. }, GenericArgument::Type(mut ty)) => {
                    self.closed_type(&mut ty)?;
                    GenericArgument::Type(ty)
                }
                (GenericParameter::Const { ty, .. }, GenericArgument::Const(value)) => {
                    let mut ty = ty.clone();
                    Substitution {
                        bindings: &bindings,
                        work: &mut self.work,
                    }
                    .ty(&mut ty)?;
                    GenericArgument::Const(constants::canonical(&value, &ty)?)
                }
                _ => {
                    return Err(format!(
                        "generic argument kind disagrees with parameter {}",
                        parameter.name()
                    ))
                }
            };
            bindings.insert(parameter.name().to_owned(), argument.clone());
            key.push(argument);
        }
        let key = (name.to_owned(), key);
        if let Some(instance) = self.instances.get(&key) {
            return Ok(instance.clone());
        }
        let template = &self.templates[name];
        charge_copy(&mut self.work, template.body_work + template.parameter_work)?;
        let template = template.declaration.clone();
        let generated = format!(
            "evg_generic_{}_{}",
            self.instances.len(),
            name.rsplit("::").next().unwrap_or(name)
        );
        for argument in &key.1 {
            if let GenericArgument::Type(ty) = argument {
                charge_type(&mut self.work, ty)?;
            }
        }
        let actual = key.1.clone();
        self.inference
            .instances
            .insert(generated.clone(), key.clone());
        self.instances.insert(key, generated.clone());
        if record {
            self.known_types.insert(generated.clone());
        }
        let mut substitution = Substitution {
            bindings: &bindings,
            work: &mut self.work,
        };
        let concrete = match template {
            GenericDeclaration::Implementation(_) => {
                return Err(
                    "implementation cannot be specialized as a record or free function".into(),
                )
            }
            GenericDeclaration::Record { mut definition, .. } => {
                if definition
                    .fields
                    .iter()
                    .map(|(name, _)| name)
                    .chain(definition.facts.iter().map(|(name, _)| name))
                    .any(|name| bindings.contains_key(name))
                {
                    return Err("record fields and facts cannot shadow generic parameters".into());
                }
                definition.name = generated.clone();
                substitution.record(&mut definition)?;
                let first_header = self.implementations.headers.len();
                self.implementations.install(
                    name,
                    &actual,
                    &generated,
                    &mut definition,
                    &mut self.pending,
                    &mut self.work,
                )?;
                self.inference
                    .register_record(&definition, &mut self.work)?;
                for header in &self.implementations.headers[first_header..] {
                    self.inference.register_function(header, &mut self.work)?;
                }
                Concrete::Record(definition)
            }
            GenericDeclaration::Function { mut definition, .. } => {
                if definition
                    .params
                    .iter()
                    .any(|(name, _)| bindings.contains_key(name))
                {
                    return Err("runtime parameters cannot shadow generic parameters".into());
                }
                definition.name = generated.clone();
                substitution.function(&mut definition)?;
                self.inference
                    .register_function(&definition, &mut self.work)?;
                Concrete::Function(definition)
            }
        };
        self.pending.push_back(concrete);
        Ok(generated)
    }

    fn closed_type(&mut self, ty: &mut Type) -> Result<()> {
        self.ty(ty)?;
        match ty {
            Type::Array(element, count) => {
                self.closed_type(element)?;
                let usize_type = Type::Machine(self.target.integer("usize").unwrap());
                **count = constants::canonical(count, &usize_type)?;
            }
            Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) | Type::Shape(inner) => {
                self.closed_type(inner)?
            }
            Type::Union(members) => {
                for member in members.iter_mut() {
                    self.closed_type(member)?;
                }
                members.sort_by_cached_key(|ty| format!("{ty:?}"));
            }
            Type::Named(name) if !self.known_types.contains(name) => {
                return Err(format!("unknown generic type argument {name}"))
            }
            _ => {}
        }
        Ok(())
    }
}

impl Visitor for Engine {
    fn ty(&mut self, ty: &mut Type) -> Result<()> {
        charge(&mut self.work)?;
        if self.depth >= 128 {
            return Err("generic expansion depth limit reached".into());
        }
        self.depth += 1;
        let result = (|| {
            visit::walk_type(self, ty)?;
            match ty {
                Type::Apply(name, arguments) => {
                    *ty = Type::Named(self.specialize(name, std::mem::take(arguments), true)?);
                }
                Type::Named(name) if self.templates.contains_key(name) => {
                    *ty = Type::Named(self.specialize(name, Vec::new(), true)?);
                }
                _ => {}
            }
            Ok(())
        })();
        self.depth -= 1;
        result
    }

    fn expr(&mut self, expression: &mut Expr) -> Result<()> {
        self.expression(expression).map(|_| ())
    }

    fn function(&mut self, function: &mut Function) -> Result<()> {
        self.infer_function(function)
    }

    fn record(&mut self, record: &mut Struct) -> Result<()> {
        self.infer_record(record)
    }

    fn statement(&mut self, statement: &mut Statement) -> Result<()> {
        self.infer_statement(statement)
    }
}
