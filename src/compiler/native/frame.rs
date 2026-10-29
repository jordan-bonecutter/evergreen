//! Frame slots, value snapshots, and the private operand stack.

use super::*;

impl Emitter<'_> {
    pub(super) fn allocate(&mut self, ty: &Type) -> Result<i32> {
        let object = layout::of(ty, self.structs)?;
        self.frame = self
            .frame
            .checked_add(object.size.max(1))
            .ok_or("native frame overflow")?
            .next_multiple_of(object.align);
        if self.frame + 16 > STACK {
            return Err("native frame exceeds private stack budget".into());
        }
        Ok(-i32::try_from(self.frame).map_err(|_| "native frame offset overflow")?)
    }

    /// Put rbp + offset in rax.
    pub(super) fn frame_address(&mut self, offset: i32) {
        self.code.extend([0x48, 0x8d, 0x85]);
        self.code.extend(offset.to_le_bytes());
    }

    pub(super) fn snapshot(&mut self, ty: &Type) -> Result<()> {
        if layout::aggregate(ty) {
            let offset = self.allocate(ty)?;
            self.copy_frame(offset, ty)?;
            self.frame_address(offset);
        } else {
            self.load_scalar(ty)?;
        }
        Ok(())
    }

    pub(super) fn slot(&mut self, name: &str, ty: Type) -> Result<()> {
        let offset = self.allocate(&ty)?;
        self.copy_frame(offset, &ty)?;
        let drop_flag = if self.has_drop(&ty) {
            Some(self.allocate(&Type::Bool)?)
        } else {
            None
        };
        if self
            .slots
            .insert(
                name.into(),
                Local {
                    offset,
                    ty,
                    drop_flag,
                },
            )
            .is_some()
        {
            return Err("duplicate native binding".into());
        }
        self.mark_live(name);
        Ok(())
    }

    pub(super) fn load(&mut self, name: &str) -> Result<Type> {
        let Local { offset, ty, .. } = self
            .slots
            .get(name)
            .cloned()
            .ok_or_else(|| format!("missing native binding {name}"))?;
        self.frame_address(offset);
        self.snapshot(&ty)?;
        Ok(ty)
    }

    /// Load a word into rax.
    pub(super) fn immediate(&mut self, value: u64) {
        self.code.extend([0x48, 0xb8]);
        self.code.extend(value.to_le_bytes());
    }

    /// Save rax on the private operand/argument stack.
    pub(super) fn push(&mut self) {
        self.code.push(0x50);
        self.temporary += 8;
        self.peak = self.peak.max(self.temporary);
    }

    /// Restore the saved word into rcx, preserving the current value in rax.
    pub(super) fn pop(&mut self) {
        self.code.push(0x59);
        self.temporary -= 8;
    }

    /// Reserve a rel32 jump, conditional on the zero flag when requested.
    pub(super) fn jump(&mut self, conditional: bool) -> usize {
        if conditional {
            self.code.extend([0x0f, 0x84]);
        } else {
            self.code.push(0xe9);
        }
        let position = self.code.len();
        self.code.extend([0; 4]);
        position
    }
}
