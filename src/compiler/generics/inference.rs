//! Structural hints select concrete syntax, never proof or ownership authority.
//! Unknown hints stay unknown; the ordinary verifier checks every selected call.

use super::*;
use std::sync::Arc;

mod applications;
mod expressions;
mod scopes;
#[cfg(test)]
mod tests;
mod unify;

#[derive(Default)]
pub(super) struct Inference {
    scopes: Vec<BTreeMap<String, Option<Arc<Hint>>>>,
    records: BTreeMap<String, BTreeMap<String, Arc<Hint>>>,
    returns: BTreeMap<String, Arc<Hint>>,
    pub instances: BTreeMap<String, (String, Vec<GenericArgument>)>,
}

struct Hint {
    ty: Type,
    work: usize,
}

impl Hint {
    fn new(ty: &Type, work: &mut usize) -> Result<Arc<Self>> {
        // This first copy comes from already metered source/substituted syntax.
        // Subsequent reads pay for the measured tree before copying it.
        let mut ty = ty.clone();
        let size = templates::type_work(&mut ty)?;
        charge_copy(work, size)?;
        Ok(Arc::new(Self { ty, work: size }))
    }
}

impl Inference {
    pub fn register_program(&mut self, program: &Program, work: &mut usize) -> Result<()> {
        for record in &program.structs {
            self.register_record(record, work)?;
        }
        for function in &program.functions {
            self.register_function(function, work)?;
        }
        Ok(())
    }

    pub fn register_function(&mut self, function: &Function, work: &mut usize) -> Result<()> {
        self.returns
            .insert(function.name.clone(), Hint::new(&function.ret, work)?);
        Ok(())
    }

    pub fn register_record(&mut self, record: &Struct, work: &mut usize) -> Result<()> {
        let mut fields = BTreeMap::new();
        for (name, ty) in &record.fields {
            fields.insert(name.clone(), Hint::new(ty, work)?);
        }
        self.records.insert(record.name.clone(), fields);
        Ok(())
    }

    fn bind(&mut self, name: &str, ty: Option<Type>, work: &mut usize) -> Result<()> {
        let hint = ty.as_ref().map(|ty| Hint::new(ty, work)).transpose()?;
        if let Some(scope) = self.scopes.last_mut() {
            // None shadows a known outer binding too.
            scope.insert(name.to_owned(), hint);
        }
        Ok(())
    }
}

impl Engine {
    fn read_hint(&mut self, hint: Option<Arc<Hint>>) -> Result<Option<Type>> {
        let Some(hint) = hint else { return Ok(None) };
        charge_copy(&mut self.work, hint.work)?;
        let mut ty = hint.ty.clone();
        // Close generic return/field types only when actually observed. An unused
        // method header may contain an indefinitely growing generic return type.
        self.ty(&mut ty)?;
        Ok(Some(ty))
    }

    fn field_hint(&mut self, mut ty: Type, name: &str) -> Result<Option<Type>> {
        while let Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) = ty {
            ty = *inner;
        }
        let Type::Named(record) = ty else {
            return Ok(None);
        };
        let hint = self
            .inference
            .records
            .get(&record)
            .and_then(|r| r.get(name))
            .cloned();
        self.read_hint(hint)
    }
}
