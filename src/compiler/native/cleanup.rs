//! Lowering of verified destruction and expression temporary lifetimes.

use super::*;

impl Emitter<'_> {
    pub(super) fn has_drop(&self, ty: &Type) -> bool {
        match ty {
            Type::Union(_) => true,
            Type::Unique(_) => true,
            Type::Named(name) => {
                self.drops.contains(name)
                    || self
                        .structs
                        .get(name)
                        .is_some_and(|s| s.runtime_fields().any(|(_, t)| self.has_drop(t)))
            }
            Type::Array(element, _) => self.has_drop(element),
            _ => false,
        }
    }

    pub(super) fn trace_drop(&mut self, name: &str) -> Result<()> {
        match self.trace {
            TraceMode::Value => {}
            TraceMode::Count => self.code.extend([0x49, 0xff, 0xc7]),
            TraceMode::Order => {
                self.code.extend([0x4d, 0x69, 0xff]);
                self.code.extend(167u32.to_le_bytes());
                self.code.extend([0x49, 0x81, 0xc7]);
                self.code.extend(
                    self.drop_ids
                        .get(name)
                        .ok_or("missing native trace type")?
                        .to_le_bytes(),
                );
            }
        }
        Ok(())
    }

    pub(super) fn drop_fields(&mut self, ty: &Type, offset: i32) -> Result<()> {
        match ty {
            Type::Union(_) => return Err("uneliminated raw union reached native cleanup".into()),
            Type::Named(name) => {
                let fields = self
                    .structs
                    .get(name)
                    .ok_or("unknown native cleanup type")?
                    .runtime_fields()
                    .cloned()
                    .collect::<Vec<_>>();
                let object = layout::of(ty, self.structs)?;
                for (name, ty) in fields {
                    self.drop_frame(&ty, offset + object.fields[&name].offset as i32)?;
                }
            }
            Type::Array(element, count) if self.has_drop(element) => {
                let bytes = layout::of(element, self.structs)?.size;
                for index in 0..layout::array_length(count)? {
                    self.drop_frame(element, offset + (index * bytes) as i32)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn drop_frame(&mut self, ty: &Type, offset: i32) -> Result<()> {
        if !self.has_drop(ty) {
            return Ok(());
        }
        if let Type::Unique(payload) = ty {
            if self.has_drop(payload) {
                self.frame_address(offset);
                self.code.extend([0x48, 0x8b, 0x00]);
                self.snapshot(payload)?;
                self.drop_value(payload)?;
            }
            self.unmap_payload(offset);
            return Ok(());
        }
        if let Type::Named(name) = ty {
            if self.drops.contains(name) {
                self.trace_drop(name)?;
                self.frame_address(offset);
                self.push_value(ty)?;
                return self.invoke(
                    &format!("evg_drop_{name}"),
                    storage::argument_size(ty, self.structs)?,
                );
            }
        }
        self.drop_fields(ty, offset)
    }

    pub(super) fn drop_value(&mut self, ty: &Type) -> Result<()> {
        if self.has_drop(ty) {
            let home = self.allocate(ty)?;
            self.copy_frame(home, ty)?;
            self.drop_frame(ty, home)?;
        }
        Ok(())
    }

    pub(super) fn finish_temporaries(&mut self, start: usize) -> Result<()> {
        for (offset, ty) in self.temporaries.split_off(start).into_iter().rev() {
            self.drop_frame(&ty, offset)?;
        }
        Ok(())
    }

    pub(super) fn scoped_expr(&mut self, e: &Expr, expected: Option<&Type>) -> Result<Type> {
        let start = self.temporaries.len();
        let ty = self.expr(e, expected)?;
        if self.temporaries.len() != start {
            let home = self.allocate(&ty)?;
            self.copy_frame(home, &ty)?;
            self.finish_temporaries(start)?;
            self.frame_address(home);
            if !layout::aggregate(&ty) {
                self.load_scalar(&ty)?;
            }
        }
        Ok(ty)
    }
}
