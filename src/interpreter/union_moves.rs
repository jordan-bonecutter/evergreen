//! Runtime checks for member extraction. Shape transitions change metadata;
//! native execution erases them and leaves the payload bytes uninterpretable.

use super::*;

impl Evaluator<'_> {
    pub(super) fn transfer_type(
        &mut self,
        args: &[Expr],
        env: &BTreeMap<String, Value>,
    ) -> Result<Value> {
        let [source, target] = args else {
            return Err("transfer_type requires two references".into());
        };
        let Value::Ref(_, source_ref, source_path) = self.expr(source, env, None)? else {
            return Err("type transfer source is not a reference".into());
        };
        let Value::Ref(_, target_ref, target_path) = self.expr(target, env, None)? else {
            return Err("type transfer target is not a reference".into());
        };
        let Value::Union(source_members, payload) = copy_value(
            project(self.memory.read(source_ref)?, &source_path)?,
            &mut self.fuel,
        )?
        else {
            return Err("type transfer source is not union storage".into());
        };
        let Value::Union(target_members, target_payload) = copy_value(
            project(self.memory.read(target_ref)?, &target_path)?,
            &mut self.fuel,
        )?
        else {
            return Err("type transfer target is not union storage".into());
        };
        let Value::Representation(ty, bytes) = *target_payload else {
            return Err("type transfer target has no captured representation".into());
        };
        if payload != bytes {
            return Err("type transfer representation mismatch: compiler/runtime disagreement or admitted equality".into());
        }
        let mut source_root = copy_value(self.memory.read(source_ref)?, &mut self.fuel)?;
        replace_projection(
            &mut source_root,
            &source_path,
            Value::Union(source_members, Box::new(Value::Representation(ty, bytes))),
        )?;
        let source_plane = self.memory.plane(source_ref)?;
        self.memory.write(source_plane, source_root, false)?;
        let mut target_root = copy_value(self.memory.read(target_ref)?, &mut self.fuel)?;
        replace_projection(
            &mut target_root,
            &target_path,
            Value::Union(target_members, payload),
        )?;
        let target_plane = self.memory.plane(target_ref)?;
        self.memory.write(target_plane, target_root, false)?;
        Ok(Value::Unit)
    }

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
