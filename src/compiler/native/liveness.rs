//! Local drop flags preserve path-dependent moves. They are private frame
//! bytes, never part of an Evergreen type's layout or call ABI.

use super::*;

impl Emitter<'_> {
    fn write_drop_flag(&mut self, name: &str, live: bool) {
        if let Some(offset) = self.slots.get(name).and_then(|local| local.drop_flag) {
            // mov byte ptr [rbp + offset], live; preserve value registers.
            self.code.extend([0xc6, 0x85]);
            self.code.extend(offset.to_le_bytes());
            self.code.push(u8::from(live));
        }
    }

    pub(super) fn mark_live(&mut self, name: &str) {
        self.alive.insert(name.into());
        self.write_drop_flag(name, true);
    }

    pub(super) fn mark_moved(&mut self, name: &str) {
        if self.alive.remove(name) {
            self.write_drop_flag(name, false);
        }
    }

    fn skip_dead_binding(&mut self, name: &str) -> Option<usize> {
        let offset = self.slots.get(name)?.drop_flag?;
        // cmp byte ptr [rbp + offset], 0; je skip cleanup.
        self.code.extend([0x80, 0xbd]);
        self.code.extend(offset.to_le_bytes());
        self.code.push(0);
        Some(self.jump(true))
    }

    fn finish_drop_guard(&mut self, skip: Option<usize>) -> Result<()> {
        if let Some(skip) = skip {
            let end = self.code.len();
            patch(self.code, skip, end)?;
        }
        Ok(())
    }

    pub(super) fn cleanup_binding(&mut self, name: &str, fields_only: bool) -> Result<()> {
        if !self.alive.remove(name) {
            return Ok(());
        }
        let Local { offset, ty, .. } = self
            .slots
            .get(name)
            .cloned()
            .ok_or("missing cleanup binding")?;
        let skip = self.skip_dead_binding(name);
        self.write_drop_flag(name, false);
        if fields_only {
            self.drop_fields(&ty, offset)?;
        } else {
            self.drop_frame(&ty, offset)?;
        }
        self.finish_drop_guard(skip)
    }

    pub(super) fn cleanup_replaced_value(
        &mut self,
        root: &str,
        offset: i32,
        ty: &Type,
    ) -> Result<()> {
        if !self.alive.contains(root) {
            return Ok(());
        }
        let skip = self.skip_dead_binding(root);
        // Replacing a field does not consume its enclosing record. A whole
        // binding assignment sets its flag after installing the new value.
        self.drop_frame(ty, offset)?;
        self.finish_drop_guard(skip)
    }
}
