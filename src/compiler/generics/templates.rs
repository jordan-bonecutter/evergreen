//! Charge syntax copies by measured tree size. Cached calls copy parameter
//! defaults only; they never repeatedly clone the template body.

use super::*;

pub(super) struct Template {
    pub declaration: GenericDeclaration,
    pub parameter_work: usize,
    pub signature_work: usize,
    pub body_work: usize,
}

struct Counter {
    work: usize,
}

pub(super) fn type_work(ty: &mut Type) -> Result<usize> {
    let mut counter = Counter { work: 0 };
    counter.ty(ty)?;
    Ok(counter.work)
}

pub(super) fn function_work(function: &mut Function) -> Result<usize> {
    let mut counter = Counter { work: 0 };
    counter.function(function)?;
    Ok(counter.work)
}

pub(super) fn charge_program(program: &mut Program, work: &mut usize) -> Result<()> {
    let mut counter = Counter { work: *work };
    for record in &mut program.structs {
        counter.record(record)?;
    }
    for function in program
        .functions
        .iter_mut()
        .chain(program.destructors.iter_mut().map(|(_, f)| f))
    {
        counter.function(function)?;
    }
    *work = counter.work;
    Ok(())
}
impl Visitor for Counter {
    fn ty(&mut self, ty: &mut Type) -> Result<()> {
        charge(&mut self.work)?;
        if let Type::Named(name) | Type::Apply(name, _) = ty {
            charge_copy(&mut self.work, name.len() / 32)?;
        }
        visit::walk_type(self, ty)
    }
    fn expr(&mut self, expression: &mut Expr) -> Result<()> {
        charge(&mut self.work)?;
        let bytes = match &expression.kind {
            Kind::Bytes(bytes) => bytes.len(),
            Kind::Name(name) | Kind::Call(name, _) | Kind::Record(name, _) => name.len(),
            _ => 0,
        };
        charge_copy(&mut self.work, bytes / 32)?;
        visit::walk_expr(self, expression)
    }
}

impl Template {
    pub fn new(declaration: GenericDeclaration) -> Result<Self> {
        // Parsed source is size/depth bounded. This one probe clone is bounded
        // by source size, before any substitution can enlarge a type tree.
        let mut probe = declaration.clone();
        let parameters = probe.parameters_mut();
        let mut count = Counter { work: 0 };
        for parameter in parameters {
            charge(&mut count.work)?;
            match parameter {
                GenericParameter::Type { default, .. } => {
                    if let Some(ty) = default {
                        count.ty(ty)?;
                    }
                }
                GenericParameter::Const { ty, default, .. } => {
                    count.ty(ty)?;
                    if let Some(value) = default {
                        count.expr(value)?;
                    }
                }
            }
        }
        let parameter_work = count.work;
        count.work = 0;
        let module = match &probe {
            GenericDeclaration::Implementation(_) => {
                return Err("implementation metadata is not a function or record template".into())
            }
            GenericDeclaration::Record { definition, .. } => &definition.module,
            GenericDeclaration::Function { definition, .. } => &definition.module,
        };
        charge_copy(
            &mut count.work,
            module.as_ref().map_or(0, |name| name.len() / 32),
        )?;
        match &mut probe {
            GenericDeclaration::Implementation(_) => {
                return Err("implementation metadata is not a function or record template".into())
            }
            GenericDeclaration::Record { definition, .. } => count.record(definition)?,
            GenericDeclaration::Function { definition, .. } => count.function(definition)?,
        }
        let mut signature_work = 0;
        let fields = match &mut probe {
            GenericDeclaration::Record { definition, .. } => &mut definition.fields,
            GenericDeclaration::Function { definition, .. } => &mut definition.params,
            _ => unreachable!("implementation rejected above"),
        };
        for (_, ty) in fields {
            charge_copy(&mut signature_work, type_work(ty)?)?;
        }
        Ok(Self {
            declaration,
            signature_work,
            parameter_work,
            body_work: count.work,
        })
    }
}
