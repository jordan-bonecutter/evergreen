//! Lexical hint scopes are independent of the verifier's plane revisions.
//! A missing type shadows outer hints; no local hint escapes its lexical block.

use super::*;

impl Engine {
    pub(super) fn with_scope<T>(
        &mut self,
        action: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        self.inference.scopes.push(BTreeMap::new());
        let result = action(self);
        self.inference.scopes.pop();
        result
    }

    pub(in crate::compiler::generics) fn infer_function(
        &mut self,
        function: &mut Function,
    ) -> Result<()> {
        self.with_scope(|engine| {
            for (name, ty) in &mut function.params {
                engine.ty(ty)?;
                engine
                    .inference
                    .bind(name, Some(ty.clone()), &mut engine.work)?;
            }
            engine.ty(&mut function.ret)?;
            engine
                .inference
                .register_function(function, &mut engine.work)?;
            for expression in function
                .pre
                .iter_mut()
                .chain(function.decreases.iter_mut())
                .chain(function.modifies.iter_mut())
            {
                engine.expr(expression)?;
            }
            engine.with_scope(|engine| {
                engine
                    .inference
                    .bind("result", Some(function.ret.clone()), &mut engine.work)?;
                if let Some(expression) = &mut function.post {
                    engine.expr(expression)?;
                }
                for alias in &mut function.borrows {
                    engine.expr(&mut alias.reference)?;
                }
                Ok(())
            })?;
            for statement in &mut function.body {
                engine.statement(statement)?;
            }
            engine.expr(&mut function.result)
        })
    }

    pub(in crate::compiler::generics) fn infer_record(
        &mut self,
        record: &mut Struct,
    ) -> Result<()> {
        self.with_scope(|engine| {
            engine.inference.bind(
                "self",
                Some(Type::Named(record.name.clone())),
                &mut engine.work,
            )?;
            for (name, ty) in &mut record.fields {
                engine.ty(ty)?;
                engine
                    .inference
                    .bind(name, Some(ty.clone()), &mut engine.work)?;
            }
            engine.inference.register_record(record, &mut engine.work)?;
            for (_, fact) in &mut record.facts {
                engine.expr(fact)?;
            }
            if let Some(invariant) = &mut record.invariant {
                engine.expr(invariant)?;
            }
            Ok(())
        })
    }

    pub(in crate::compiler::generics) fn infer_statement(
        &mut self,
        statement: &mut Statement,
    ) -> Result<()> {
        match statement {
            Statement::Let { name, ty, value } => {
                if let Some(ty) = ty {
                    self.ty(ty)?;
                }
                let inferred = self.expression(value)?;
                self.inference
                    .bind(name, ty.clone().or(inferred), &mut self.work)
            }
            Statement::Destructure {
                record,
                arguments,
                fields,
                value,
            } => {
                for argument in arguments.iter_mut() {
                    self.argument(argument)?;
                }
                let actual = self.expression(value)?;
                if arguments.is_empty() && self.templates.contains_key(record) {
                    if let Some(Type::Named(instance)) = &actual {
                        if self
                            .inference
                            .instances
                            .get(instance)
                            .is_some_and(|(base, _)| base == record)
                        {
                            *record = instance.clone();
                        }
                    }
                }
                if !arguments.is_empty() || self.templates.contains_key(record) {
                    *record = self.specialize(record, std::mem::take(arguments), true)?;
                }
                for (field, name) in fields {
                    let ty = self.field_hint(Type::Named(record.clone()), field)?;
                    self.inference.bind(name, ty, &mut self.work)?;
                }
                Ok(())
            }
            Statement::While {
                condition,
                invariant,
                modifies,
                decreases,
                body,
                ..
            } => {
                self.expr(condition)?;
                self.expr(invariant)?;
                for expression in modifies.iter_mut().chain(decreases.iter_mut()) {
                    self.expr(expression)?;
                }
                self.with_scope(|engine| {
                    for statement in body {
                        engine.statement(statement)?;
                    }
                    Ok(())
                })
            }
            Statement::Update { places, body, .. } => {
                for place in places {
                    self.expr(place)?;
                }
                self.with_scope(|engine| {
                    for statement in body {
                        engine.statement(statement)?;
                    }
                    Ok(())
                })
            }
            Statement::Fact { name, value } => {
                self.expr(value)?;
                self.inference.bind(name, Some(Type::Bool), &mut self.work)
            }
            _ => visit::walk_statement(self, statement),
        }
    }
}
