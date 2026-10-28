//! Match known argument shapes against template parameters. This is deliberately
//! independent of facts: a proof cannot rewrite the type chosen for a call.

use super::*;

type Bindings = BTreeMap<String, GenericArgument>;

impl Engine {
    pub(super) fn inferred_arguments(
        &mut self,
        name: &str,
        actual: &[(Option<&str>, Option<Type>)],
        line: usize,
    ) -> Result<Vec<GenericArgument>> {
        let template = &self.templates[name];
        charge_copy(
            &mut self.work,
            template.parameter_work + template.signature_work,
        )?;
        let (parameters, formal) = match &template.declaration {
            GenericDeclaration::Function {
                parameters,
                definition,
            } => (parameters.clone(), definition.params.clone()),
            GenericDeclaration::Record {
                parameters,
                definition,
            } => (parameters.clone(), definition.fields.clone()),
            _ => return Err("implementation is not a generic call".into()),
        };
        let mut bindings = BTreeMap::new();
        // Missing runtime-length arguments are elaborated later. Do not pair a
        // shifted argument list with the wrong parameters.
        if actual.len() == formal.len() {
            for (index, (field, ty)) in actual.iter().enumerate() {
                let Some(ty) = ty else { continue };
                let parameter = match field {
                    Some(field) => formal.iter().find(|(name, _)| name == field),
                    None => formal.get(index),
                };
                if let Some((_, pattern)) = parameter {
                    self.unify(pattern, ty, &parameters, &mut bindings, 0)
                        .map_err(|error| format!("line {line}: {error} in generic call {name}"))?;
                }
            }
        }
        parameters.iter().map(|parameter| {
            if let Some(inferred) = bindings.remove(parameter.name()) {
                return Ok(inferred);
            }
            match parameter {
                GenericParameter::Type { default: Some(ty), .. } => Ok(GenericArgument::Type(ty.clone())),
                GenericParameter::Const { default: Some(value), .. } => Ok(GenericArgument::Const(value.clone())),
                _ => Err(format!("line {line}: cannot infer generic argument {} for {name}; supply explicit generic arguments or annotate the input value", parameter.name())),
            }
        }).collect()
    }

    fn unify(
        &mut self,
        pattern: &Type,
        actual: &Type,
        parameters: &[GenericParameter],
        bindings: &mut Bindings,
        depth: usize,
    ) -> Result<()> {
        charge(&mut self.work)?;
        if depth >= 128 {
            return Err("generic inference depth limit reached".into());
        }
        if let Type::Named(name) = pattern {
            if parameters
                .iter()
                .any(|p| matches!(p, GenericParameter::Type { .. }) && p.name() == name)
            {
                charge_type(&mut self.work, actual)?;
                let mut actual = actual.clone();
                self.closed_type(&mut actual)?;
                return bind(name, GenericArgument::Type(actual), bindings);
            }
        }
        match (pattern, actual) {
            (Type::Ref(a), Type::Ref(b))
            | (Type::Unique(a), Type::Unique(b))
            | (Type::Shared(a), Type::Shared(b))
            | (Type::Shape(a), Type::Shape(b)) => {
                self.unify(a, b, parameters, bindings, depth + 1)?;
            }
            (Type::Array(a, count), Type::Array(b, extent)) => {
                self.unify(a, b, parameters, bindings, depth + 1)?;
                self.unify_const(count, extent, parameters, bindings)?;
            }
            (Type::Apply(base, arguments), Type::Named(instance)) => {
                let Some((actual_base, actual_arguments)) = self.inference.instances.get(instance)
                else {
                    return Ok(());
                };
                if base != actual_base {
                    return Ok(());
                }
                for argument in actual_arguments {
                    if let GenericArgument::Type(ty) = argument {
                        charge_type(&mut self.work, ty)?;
                    }
                }
                let actual_arguments = actual_arguments.clone();
                for (pattern, actual) in arguments.iter().zip(&actual_arguments) {
                    match (pattern, actual) {
                        (GenericArgument::Type(a), GenericArgument::Type(b)) => {
                            self.unify(a, b, parameters, bindings, depth + 1)?
                        }
                        (GenericArgument::Const(a), GenericArgument::Const(b)) => {
                            self.unify_const(a, b, parameters, bindings)?
                        }
                        _ => {}
                    }
                }
            }
            // Fixed type mismatches, union selection, and coercions belong to
            // the verifier; they cannot contribute guessed generic arguments.
            _ => {}
        }
        Ok(())
    }

    fn unify_const(
        &mut self,
        pattern: &Expr,
        actual: &Expr,
        parameters: &[GenericParameter],
        bindings: &mut Bindings,
    ) -> Result<()> {
        let Kind::Name(name) = &pattern.kind else {
            return Ok(());
        };
        let Some(GenericParameter::Const { ty, .. }) = parameters.iter().find(|p| p.name() == name)
        else {
            return Ok(());
        };
        charge(&mut self.work)?;
        let value = constants::canonical(actual, ty)?;
        bind(name, GenericArgument::Const(value), bindings)
    }
}

fn bind(name: &str, argument: GenericArgument, bindings: &mut Bindings) -> Result<()> {
    if let Some(previous) = bindings.get(name) {
        if previous != &argument {
            return Err(format!("conflicting inferred arguments for {name}"));
        }
    } else {
        bindings.insert(name.to_owned(), argument);
    }
    Ok(())
}
