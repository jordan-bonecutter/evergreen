//! A scalar leaf is identified by the array version and a structural field path.
//! Projection does not create an array, memory plane, or ownership authority.

use super::*;
use crate::compiler::kernel::terms::Id;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::compiler::verify) struct Contents {
    pub(super) identity: String,
    pub(super) whole: bool,
    pub(super) fields: Vec<String>,
}

impl Contents {
    pub(super) fn with_identity(&self, identity: String) -> Self {
        Self {
            identity,
            whole: self.whole,
            fields: self.fields.clone(),
        }
    }

    pub(super) fn project<'v>(&self, mut value: &'v Symbol) -> Result<&'v Symbol> {
        for field in &self.fields {
            let Symbol::Record(_, fields) = value else {
                return Err("array payload field requires record storage".into());
            };
            value = fields
                .get(field)
                .ok_or("array payload field does not exist")?;
        }
        Ok(value)
    }

    pub(super) fn term(&self, terms: &mut Terms, index: Id, work: &mut Work) -> Result<Id> {
        let mut value = terms.application(
            &format!(
                "{}:{}",
                if self.whole {
                    "array_values"
                } else {
                    "array_contents"
                },
                self.identity
            ),
            &[index],
            work,
        )?;
        for field in &self.fields {
            value = terms.application(&format!("record_field:{field}"), &[value], work)?;
        }
        Ok(value)
    }
}

pub(super) fn indexed_parts(expression: &Expr) -> Option<(&Expr, &Expr, Vec<String>)> {
    let mut expression = expression;
    let mut fields = Vec::new();
    while let Kind::Field(base, field) = &expression.kind {
        fields.push(field.clone());
        expression = base;
    }
    let Kind::Index(base, index) = &expression.kind else {
        return None;
    };
    fields.reverse();
    Some((base, index, fields))
}

impl Context<'_> {
    pub(super) fn scalar_projection_type(
        &mut self,
        mut ty: Ty,
        fields: &[String],
        line: usize,
    ) -> Result<Ty> {
        if fields.len() >= 64 {
            return Err("array scalar projection depth limit reached".into());
        }
        for field in fields {
            self.charge_value_work(1 + field.len())?;
            let Ty::Record(name) = ty else {
                return Err("array payload field requires a record type".into());
            };
            self.field_access(&name, field, line)?;
            let field_type = self.declarations.structs[&name]
                .fields
                .iter()
                .find(|(name, _)| name == field)
                .ok_or_else(|| format!("line {line}: unknown field {field}"))?
                .1
                .clone();
            ty = self.resolve(&field_type)?;
        }
        Ok(ty)
    }

    pub(super) fn scalar_leaves<'v>(
        &mut self,
        value: &'v Symbol,
    ) -> Result<Vec<(Vec<String>, &'v Symbol)>> {
        let mut pending = vec![(Vec::new(), value)];
        let mut leaves = Vec::new();
        while let Some((path, value)) = pending.pop() {
            self.charge_value_work(1 + path.len())?;
            if path.len() >= 64 {
                return Err("array scalar projection depth limit reached".into());
            }
            if scalar(&value.ty()) {
                leaves.push((path, value));
            } else if let Symbol::Record(_, fields) = value {
                for (name, value) in fields {
                    self.charge_value_work(1 + name.len() + path.len())?;
                    let mut next = path.clone();
                    next.push(name.clone());
                    pending.push((next, value));
                }
            }
        }
        Ok(leaves)
    }
}
