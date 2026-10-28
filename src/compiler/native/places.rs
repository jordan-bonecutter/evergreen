//! Addresses and values of stored fields, arrays, and borrowed temporaries.

use super::*;

impl Emitter<'_> {
    pub(super) fn storage_value(&mut self, e: &Expr) -> Result<Type> {
        match &e.kind {
            Kind::Name(name) => self.load(name),
            Kind::Field(base, name) => {
                let direct = base.stored_place();
                let ty = if direct {
                    self.address(base)?
                } else {
                    self.storage_value(base)?
                };
                let field = self.field(&ty, name)?;
                self.add_offset(field.offset);
                if !layout::aggregate(&field.ty) {
                    self.load_scalar(&field.ty)?;
                } else if direct {
                    self.snapshot(&field.ty)?;
                }
                Ok(field.ty)
            }
            Kind::Index(base, index) => {
                let mode = if base.stored_place() {
                    ReadMode::Place
                } else {
                    ReadMode::Storage
                };
                let ty = self.index_address(base, index, mode)?;
                if !layout::aggregate(&ty) {
                    self.load_scalar(&ty)?;
                }
                Ok(ty)
            }
            Kind::Unary(op, _) if op == "*" => {
                let ty = self.address(e)?;
                self.snapshot(&ty)?;
                Ok(ty)
            }
            _ => {
                let ty = self.expr(e, None)?;
                if self.has_drop(&ty) {
                    let home = self.allocate(&ty)?;
                    self.copy_frame(home, &ty)?;
                    self.temporaries.push((home, ty.clone()));
                    self.frame_address(home);
                    if !layout::aggregate(&ty) {
                        self.load_scalar(&ty)?;
                    }
                }
                Ok(ty)
            }
        }
    }

    pub(super) fn field(&self, ty: &Type, name: &str) -> Result<layout::Field> {
        layout::of(ty, self.structs)?
            .fields
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown native field {name}"))
    }

    pub(super) fn add_offset(&mut self, offset: usize) {
        if offset != 0 {
            self.code.extend([0x48, 0x05]);
            self.code.extend((offset as u32).to_le_bytes());
        }
    }

    pub(super) fn index_address(
        &mut self,
        base: &Expr,
        index: &Expr,
        mode: ReadMode,
    ) -> Result<Type> {
        let ty = match mode {
            ReadMode::Place => self.address(base)?,
            ReadMode::Value => self.expr(base, None)?,
            ReadMode::Storage => self.storage_value(base)?,
        };
        let Type::Array(element, _) = ty else {
            return Err("native index requires an array".into());
        };
        let bytes = layout::of(&element, self.structs)?.size;
        self.push();
        let index_ty = self.expr(index, None)?;
        if !matches!(index_ty, Type::Machine(_)) {
            return Err("native index requires a machine integer".into());
        }
        self.code.extend([0x48, 0x69, 0xc0]);
        self.code.extend((bytes as u32).to_le_bytes());
        self.pop();
        self.code.extend([0x48, 0x01, 0xc8]);
        Ok(*element)
    }

    pub(super) fn address(&mut self, e: &Expr) -> Result<Type> {
        match &e.kind {
            Kind::Field(base, name) => {
                let base = self.address(base)?;
                let field = self.field(&base, name)?;
                self.add_offset(field.offset);
                Ok(field.ty)
            }
            Kind::Index(base, index) => self.index_address(base, index, ReadMode::Place),
            Kind::Name(name) => {
                let Local { offset, ty, .. } =
                    self.slots.get(name).ok_or("unknown native place")?;
                self.code.extend([0x48, 0x8d, 0x85]);
                self.code.extend(offset.to_le_bytes());
                Ok(ty.clone())
            }
            Kind::Unary(op, x) if op == "*" => match self.pointer_operand(x)? {
                Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) => Ok(*inner),
                _ => Err("native place dereference requires a reference".into()),
            },
            Kind::Bytes(_) | Kind::Record(..) | Kind::Call(..) | Kind::If(..) | Kind::Block(..) => {
                let ty = self.expr(e, None)?;
                if !matches!(ty, Type::Named(_)) && !matches!(e.kind, Kind::Bytes(_)) {
                    return Err("temporary borrows require a record value".into());
                }
                let home = self.allocate(&ty)?;
                self.copy_frame(home, &ty)?;
                self.temporaries.push((home, ty.clone()));
                self.frame_address(home);
                Ok(ty)
            }
            _ => Err("native references require stored places".into()),
        }
    }
}
