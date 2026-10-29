//! Explicit refinement constructors elaborate to ordinary checked records.
//! No new storage, ownership, or proof rule is introduced here.

use crate::syntax::visit::{self, Visitor};
use crate::syntax::{Expr, GenericDeclaration, GenericParameter, Kind, Program, Struct, Type};
use std::collections::BTreeSet;

pub(super) fn lower(program: &mut Program) -> Result<(), String> {
    let records = program
        .structs
        .iter()
        .chain(program.generics.iter().filter_map(|d| match d {
            GenericDeclaration::Record { definition, .. } => Some(definition.as_ref()),
            _ => None,
        }));
    let names = records
        .filter(|s| s.refined_base().is_some())
        .map(|s| s.name.clone())
        .collect::<BTreeSet<_>>();
    let functions = program
        .functions
        .iter()
        .chain(program.generics.iter().filter_map(|d| match d {
            GenericDeclaration::Function { definition, .. } => Some(definition.as_ref()),
            _ => None,
        }));
    for function in functions {
        if names.contains(&function.name) {
            return Err(format!(
                "line {}: function {} conflicts with its refinement constructor",
                function.line, function.name
            ));
        }
    }
    let mut constructors = Constructors {
        names: &names,
        refined_self: false,
    };
    for record in &mut program.structs {
        constructors.record(record)?;
    }
    for function in program
        .functions
        .iter_mut()
        .chain(program.destructors.iter_mut().map(|(_, f)| f))
    {
        constructors.refined_self = function
            .impl_target
            .as_ref()
            .is_some_and(|name| names.contains(name));
        constructors.function(function)?;
    }
    for declaration in &mut program.generics {
        constructors.refined_self = false;
        for parameter in declaration.parameters_mut() {
            match parameter {
                GenericParameter::Type {
                    default: Some(ty), ..
                } => constructors.ty(ty)?,
                GenericParameter::Const { ty, default, .. } => {
                    constructors.ty(ty)?;
                    if let Some(value) = default {
                        constructors.expr(value)?;
                    }
                }
                _ => {}
            }
        }
        match declaration {
            GenericDeclaration::Record { definition, .. } => constructors.record(definition)?,
            GenericDeclaration::Function { definition, .. } => constructors.function(definition)?,
            GenericDeclaration::Implementation(implementation) => {
                constructors.refined_self = match &implementation.target {
                    Type::Named(name) | Type::Apply(name, _) => names.contains(name),
                    _ => false,
                };
                constructors.ty(&mut implementation.target)?;
                for function in &mut implementation.functions {
                    constructors.function(function)?;
                }
            }
        }
    }
    Ok(())
}

struct Constructors<'a> {
    names: &'a BTreeSet<String>,
    refined_self: bool,
}

impl Visitor for Constructors<'_> {
    fn expr(&mut self, expr: &mut Expr) -> Result<(), String> {
        if let Kind::Call(name, args) = &mut expr.kind {
            if self.names.contains(name) || (name == "Self" && self.refined_self) {
                if args.len() != 1 {
                    return Err(format!("line {}: refinement constructor {name} requires exactly one underlying value", expr.line));
                }
                let value = args.pop().expect("checked constructor arity");
                expr.kind = Kind::Record(name.clone(), vec![(Struct::REFINED_VALUE.into(), value)]);
            }
        }
        visit::walk_expr(self, expr)
    }
}
