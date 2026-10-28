//! The reference execution model checks generic lifetime tokens independently
//! of source Rc counters. Native code erases this semantic bookkeeping.

use super::*;

impl Evaluator<'_> {
    pub(super) fn contains_shared(value: &Value) -> bool {
        match value {
            Value::Shared(..) => true,
            Value::Record(_, fields) => fields.values().any(Self::contains_shared),
            Value::Array(_, items) => items.iter().any(Self::contains_shared),
            Value::Union(_, payload) => Self::contains_shared(payload),
            _ => false,
        }
    }

    pub(super) fn copy_pointer_read(&mut self, value: Value) -> Result<Value> {
        if self.value_is_move_only(&value) || !Self::contains_shared(&value) {
            return Ok(value);
        }
        self.copy_shared_fields(value)
    }

    fn copy_shared_fields(&mut self, value: Value) -> Result<Value> {
        self.fuel = self
            .fuel
            .checked_sub(1)
            .ok_or("execution value-work limit reached during pointer copy")?;
        Ok(match value {
            Value::Shared(ty, owner) => Value::Shared(ty, self.memory.copy_owner(owner)?.owner()),
            Value::Record(name, fields) => Value::Record(
                name,
                fields
                    .into_iter()
                    .map(|(name, value)| Ok((name, self.copy_shared_fields(value)?)))
                    .collect::<Result<_>>()?,
            ),
            Value::Array(ty, items) => Value::Array(
                ty,
                items
                    .into_iter()
                    .map(|value| self.copy_shared_fields(value))
                    .collect::<Result<_>>()?,
            ),
            other => other,
        })
    }

    pub(super) fn coerce_pointer(
        &mut self,
        value: Value,
        expected: Option<&Type>,
    ) -> Result<Value> {
        match (value, expected) {
            (Value::Ref(source, reference, mut path), Some(Type::Ref(target)))
                if matches!(source.as_ref(), Type::Union(_))
                    && source.as_ref() != target.as_ref() =>
            {
                let Value::Union(members, payload) = project(self.memory.read(reference)?, &path)?
                else {
                    return Err("member borrows require current union storage".into());
                };
                let index = members
                    .iter()
                    .position(|member| {
                        type_match::same_runtime_type(member, target).unwrap_or(false)
                    })
                    .ok_or("reference target is not a raw union member")?;
                if !payload.matches_member_type(target)? {
                    return Err("borrowing an inactive raw union member".into());
                }
                path.push(Projection::Member {
                    index,
                    expected: members[index].clone(),
                });
                Ok(Value::Ref(target.clone(), reference, path))
            }
            (Value::Unique(source, reference), Some(Type::Unique(target)))
                if Self::empty_array_target(&source, target)? =>
            {
                self.narrow_empty_array(reference, target)
            }
            (Value::Unique(ty, reference), Some(Type::Shared(target)))
                if type_match::same_runtime_type(&ty, target)? =>
            {
                let plane = self.memory.plane(reference)?;
                Ok(Value::Shared(ty, self.memory.share_owner(plane)?))
            }
            (Value::Shared(ty, owner), Some(Type::Unique(target)))
                if type_match::same_runtime_type(&ty, target)? =>
            {
                let reference = self.memory.borrow_owned(owner)?;
                let census = self.memory.owner_census(reference)?;
                self.memory.recover_unique_owner_at(owner, census)?;
                Ok(Value::Unique(ty, reference))
            }
            (value, _) => Ok(value),
        }
    }

    pub(super) fn leak_value(&mut self, value: Value) -> Result<()> {
        self.fuel = self
            .fuel
            .checked_sub(1)
            .ok_or("execution value-work limit reached during leak")?;
        match value {
            Value::Shared(_, owner) => {
                self.memory.release_owner(owner)?;
            }
            Value::Unique(_, reference) => {
                let plane = self.memory.plane(reference)?;
                let owner = self.memory.share_owner(plane)?;
                self.memory.release_owner(owner)?;
            }
            Value::Record(_, fields) => {
                for value in fields.into_values() {
                    self.leak_value(value)?;
                }
            }
            Value::Array(_, items) => {
                for value in items {
                    self.leak_value(value)?;
                }
            }
            Value::Union(_, payload) => self.leak_value(*payload)?,
            _ => {}
        }
        Ok(())
    }
}
