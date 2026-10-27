//! Independent runtime validation of the empty-buffer transition. The reference
//! evaluator remains fuel-bounded and stores actual cells, unlike proof state.

use super::*;

impl Evaluator<'_> {
    pub(super) fn empty_array_target(source: &Type, target: &Type) -> Result<bool> {
        let (Type::Array(source, _), Type::Array(target, _)) = (source, target) else {
            return Ok(false);
        };
        let Type::Union(members) = source.as_ref() else {
            return Ok(false);
        };
        if !matches!(target.as_ref(), Type::Shape(_)) {
            return Ok(false);
        }
        members.iter().try_fold(false, |found, member| {
            Ok(found || type_match::same_runtime_type(member, target)?)
        })
    }

    pub(super) fn narrow_empty_array(
        &mut self,
        reference: Reference,
        target: &Type,
    ) -> Result<Value> {
        let Type::Array(element, count) = target else {
            return Err("empty array conversion requires an array".into());
        };
        let Value::Array(_, items) = copy_value(self.memory.read(reference)?, &mut self.fuel)?
        else {
            return Err("empty array conversion requires array storage".into());
        };
        if crate::syntax::constant_extent(count)
            && crate::compiler::layout::array_length(count)? != items.len()
        {
            return Err("empty array extent changed: compiler/runtime disagreement".into());
        }
        let mut converted = Vec::new();
        for value in items {
            let value = match value {
                Value::Union(_, payload) => *payload,
                value => value,
            };
            charge_value(&value, &mut self.fuel)?;
            if !value.matches_type(element)? {
                return Err("empty array conversion discarded an initialized member: compiler/runtime disagreement".into());
            }
            converted.push(value);
        }
        let plane = self.memory.plane(reference)?;
        self.memory.write(
            plane,
            Value::Array(Arc::new((**element).clone()), converted),
            false,
        )?;
        Ok(Value::Unique(
            Box::new(target.clone()),
            self.memory.borrow(plane)?,
        ))
    }
}
