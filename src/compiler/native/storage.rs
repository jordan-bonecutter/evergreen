//! Width-correct accesses and exact-size copies of native storage.

use super::*;

pub(super) fn argument_size(ty: &Type, structs: &BTreeMap<String, Struct>) -> Result<usize> {
    // The private call stack uses words; addressable values retain their own layout.
    Ok(if layout::aggregate(ty) {
        layout::of(ty, structs)?.size.next_multiple_of(8)
    } else {
        8
    })
}

impl Emitter<'_> {
    /// Choose the low result bits, then restore the signed/unsigned register
    /// representation. Overflow is unspecified in source; this is a target choice.
    pub(super) fn normalize_machine(&mut self, ty: &Type) -> Result<()> {
        let Type::Machine(integer) = ty else {
            return Err("native arithmetic requires a machine integer".into());
        };
        self.code.extend(match (integer.bits, integer.signed) {
            (8, false) => &[0x0f, 0xb6, 0xc0][..],
            (8, true) => &[0x48, 0x0f, 0xbe, 0xc0],
            (16, false) => &[0x0f, 0xb7, 0xc0],
            (16, true) => &[0x48, 0x0f, 0xbf, 0xc0],
            (32, false) => &[0x89, 0xc0],
            (32, true) => &[0x48, 0x63, 0xc0],
            (64, _) => &[],
            _ => return Err("invalid native arithmetic width".into()),
        });
        Ok(())
    }

    /// Load a scalar at rax, extending it to the register representation.
    pub(super) fn load_scalar(&mut self, ty: &Type) -> Result<()> {
        let size = layout::of(ty, self.structs)?.size;
        let signed = matches!(ty, Type::Machine(integer) if integer.signed);
        self.code.extend(match (size, signed) {
            (1, false) => &[0x0f, 0xb6, 0x00][..],
            (1, true) => &[0x48, 0x0f, 0xbe, 0x00],
            (2, false) => &[0x0f, 0xb7, 0x00],
            (2, true) => &[0x48, 0x0f, 0xbf, 0x00],
            (4, false) => &[0x8b, 0x00],
            (4, true) => &[0x48, 0x63, 0x00],
            (8, _) => &[0x48, 0x8b, 0x00],
            _ => return Err("invalid native scalar width".into()),
        });
        Ok(())
    }

    fn store_scalar(&mut self, size: usize, destination: u8, offset: i32) -> Result<()> {
        self.code.extend(match size {
            1 => &[0x88][..],
            2 => &[0x66, 0x89],
            4 => &[0x89],
            8 => &[0x48, 0x89],
            _ => return Err("invalid native store width".into()),
        });
        self.code.push(destination);
        self.code.extend(offset.to_le_bytes());
        Ok(())
    }

    fn copy_storage(&mut self, size: usize, destination: u8, base: i32) -> Result<()> {
        self.code.extend([0x48, 0x89, 0xc2]); // rdx = source
        let mut offset = 0;
        while offset < size {
            let remaining = size - offset;
            let width = [8, 4, 2, 1].into_iter().find(|n| *n <= remaining).unwrap();
            self.code.extend(match width {
                8 => &[0x48, 0x8b, 0x82][..],
                4 => &[0x8b, 0x82],
                2 => &[0x0f, 0xb7, 0x82],
                _ => &[0x0f, 0xb6, 0x82],
            });
            self.code.extend((offset as i32).to_le_bytes());
            self.store_scalar(width, destination, base + offset as i32)?;
            offset += width;
        }
        Ok(())
    }

    pub(super) fn copy_frame(&mut self, offset: i32, ty: &Type) -> Result<()> {
        let size = layout::of(ty, self.structs)?.size;
        if layout::aggregate(ty) {
            self.copy_storage(size, 0x85, offset)
        } else {
            self.store_scalar(size, 0x85, offset)
        }
    }

    /// Destination is rcx. Aggregate register values are snapshot addresses.
    pub(super) fn copy_address(&mut self, ty: &Type) -> Result<()> {
        let size = layout::of(ty, self.structs)?.size;
        if layout::aggregate(ty) {
            self.copy_storage(size, 0x81, 0)
        } else {
            self.store_scalar(size, 0x81, 0)
        }
    }
}
