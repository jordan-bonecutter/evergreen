//! Inline record and array construction in source evaluation order.

use super::*;

impl Emitter<'_> {
    pub(super) fn record_literal(
        &mut self,
        name: &str,
        entries: &[(String, Expr)],
    ) -> Result<Type> {
        let ty = Type::Named(name.to_owned());
        let object = self.allocate(&ty)?;
        if self.structs[name].runtime_fields().next().is_none() {
            self.immediate(0);
            self.copy_frame(object, &Type::Unit)?;
        }
        for (field, expression) in entries {
            if self.structs[name].ideal_fields.contains(field) {
                continue;
            }
            let field = self.field(&ty, field)?;
            self.expr(expression, Some(&field.ty))?;
            self.copy_frame(object + field.offset as i32, &field.ty)?;
        }
        self.frame_address(object);
        Ok(ty)
    }

    pub(super) fn array_literal(
        &mut self,
        items: &[Expr],
        expected: Option<&Type>,
        line: usize,
    ) -> Result<Type> {
        let expected = expected.and_then(|ty| layout::literal_array_member(ty, items.len()));
        let ty = if let Some(Type::Array(..)) = expected {
            expected.unwrap().clone()
        } else {
            let first = items.first().ok_or("native empty array needs a type")?;
            Type::Array(
                Box::new(self.hint(first).unwrap_or_else(machine)),
                Box::new(Expr {
                    kind: Kind::Number(items.len() as i128),
                    line,
                }),
            )
        };
        let Type::Array(element, count) = &ty else {
            unreachable!()
        };
        if layout::array_length(count)? != items.len() {
            return Err("native array literal length mismatch".into());
        }
        let bytes = layout::of(element, self.structs)?.size;
        let object = self.allocate(&ty)?;
        if items.is_empty() {
            self.immediate(0);
            self.copy_frame(object, &Type::Unit)?;
        }
        for (index, item) in items.iter().enumerate() {
            self.expr(item, Some(element))?;
            self.copy_frame(object + (index * bytes) as i32, element)?;
        }
        self.frame_address(object);
        Ok(ty)
    }
}
