//! Runtime checks for member extraction. Shape transitions change metadata;
//! native execution erases them and leaves the payload bytes uninterpretable.

use super::*;

impl Evaluator<'_> {
    pub(super) fn select_projected_member(
        &self,
        value: Value,
        expected: Option<&Type>,
    ) -> Result<Value> {
        match (value, expected) {
            (Value::Union(_, payload), Some(target)) if !matches!(target, Type::Union(_)) => {
                if !payload.matches_type(target)? {
                    return Err("inactive raw union member: compiler/runtime disagreement".into());
                }
                Ok(*payload)
            }
            (value, _) => Ok(value),
        }
    }

    pub(super) fn union_move_place(
        &self,
        expression: &Expr,
        env: &BTreeMap<String, Value>,
        target: &Type,
    ) -> Result<bool> {
        let projected = matches!(expression.kind, Kind::Field(..) | Kind::Index(..))
            || matches!(&expression.kind, Kind::Unary(op, _) if op == "*");
        if !projected {
            return Ok(false);
        }
        let Some(Type::Union(members)) = self.hint(expression, env) else {
            return Ok(false);
        };
        let mut member = false;
        let mut shape = false;
        for ty in members {
            member |= type_match::same_runtime_type(&ty, target)?;
            if let Type::Shape(inner) = ty {
                shape |= type_match::same_runtime_type(&inner, target)?;
            }
        }
        Ok(member && shape)
    }

    pub(super) fn move_union_member(
        &mut self,
        expression: &Expr,
        env: &BTreeMap<String, Value>,
        target: &Type,
    ) -> Result<Value> {
        let (reference, path) = self.location(expression, env)?;
        let mut root = copy_value(self.memory.read(reference)?, &mut self.fuel)?;
        let Value::Union(members, payload) = copy_value(project(&root, &path)?, &mut self.fuel)?
        else {
            return Err("member extraction requires union storage".into());
        };
        if !payload.matches_type(target)? {
            return Err("inactive raw union member: compiler/runtime disagreement".into());
        }
        let replacement = Value::Union(members, Box::new(Value::Shape(Box::new(target.clone()))));
        replace_projection(&mut root, &path, replacement)?;
        let plane = self.memory.plane(reference)?;
        self.memory.write(plane, root, false)?;
        Ok(*payload)
    }
}
