//! Private mapping headers let owners free runtime-sized payloads without
//! carrying an extra size word in every source-level owner value.

use super::*;

const HEADER: u8 = 8;

impl Emitter<'_> {
    /// Input: positive payload byte count in rax. Output: payload address in rax.
    pub(super) fn map_payload(&mut self) {
        self.code.extend([0x48, 0x83, 0xc0, HEADER]);
        self.code.extend([0x48, 0x89, 0xc6]); // rsi = mapping bytes, including header
        self.code.extend([0x31, 0xff]); // null address hint
        self.code.extend([0xba, 3, 0, 0, 0]); // read/write
        self.code.extend([0x41, 0xba, 0x22, 0, 0, 0]); // private anonymous
        self.code.extend([0x49, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff]);
        self.code.extend([0x45, 0x31, 0xc9]);
        self.code.extend([0xb8, 9, 0, 0, 0, 0x0f, 0x05]);
        self.code.extend([0x48, 0x85, 0xc0]);
        self.heap_guard(0x79);
        self.code.extend([0x48, 0x89, 0x30]); // header = mapping byte count
        self.code.extend([0x48, 0x83, 0xc0, HEADER]);
    }

    pub(super) fn unmap_payload(&mut self, owner: i32) {
        self.code.extend([0x48, 0x8b, 0xbd]);
        self.code.extend(owner.to_le_bytes());
        self.code.extend([0x48, 0x83, 0xef, HEADER]); // allocation base
        self.code.extend([0x48, 0x8b, 0x37]); // mapping bytes from header
        self.code.extend([0xb8, 11, 0, 0, 0, 0x0f, 0x05]);
        self.code.extend([0x48, 0x85, 0xc0]);
        self.heap_guard(0x79);
    }
}

impl Emitter<'_> {
    pub(super) fn allocate_filled(
        &mut self,
        args: &[Expr],
        expected: Option<&Type>,
    ) -> Result<Type> {
        let count_type = Type::Machine(MachineInt::parse("usize").unwrap());
        self.expr(&args[0], Some(&count_type))?;
        let count = self.allocate(&count_type)?;
        self.copy_frame(count, &count_type)?;
        let hint = match expected {
            Some(Type::Plane(inner)) => match inner.as_ref() {
                Type::Array(element, _) => Some(element.as_ref()),
                _ => None,
            },
            _ => None,
        };
        let element = self.expr(&args[1], hint)?;
        if self.has_drop(&element) {
            return Err("filled allocation cannot duplicate owning values".into());
        }
        let layout = layout::of(&element, self.structs)?;
        let initial = self.allocate(&element)?;
        self.copy_frame(initial, &element)?;
        self.frame_address(count);
        self.load_scalar(&count_type)?;
        self.code.extend([0x48, 0x69, 0xc0]);
        self.code.extend((layout.size as u32).to_le_bytes());
        self.code.extend([0x48, 0x85, 0xc0, 0x75, 10]); // preserve empty-object identity
        self.immediate(layout.align as u64);
        self.map_payload();
        let result = Type::Plane(Box::new(Type::Array(
            Box::new(element.clone()),
            Box::new(args[0].clone()),
        )));
        let home = self.allocate(&result)?;
        self.copy_frame(home, &result)?;
        self.code.extend([0x49, 0x89, 0xc1]); // r9 = cursor
        self.code.extend([0x4c, 0x8b, 0x85]); // r8 = count
        self.code.extend(count.to_le_bytes());
        self.code.extend([0x4d, 0x85, 0xc0]);
        let empty = self.jump(true);
        let loop_start = self.code.len();
        self.frame_address(initial);
        if !layout::aggregate(&element) {
            self.load_scalar(&element)?;
        }
        self.code.extend([0x4c, 0x89, 0xc9]); // rcx = cursor
        self.copy_address(&element)?;
        self.code.extend([0x49, 0x81, 0xc1]);
        self.code.extend((layout.size as u32).to_le_bytes());
        self.code.extend([0x49, 0xff, 0xc8]);
        self.code.extend([0x0f, 0x85]);
        let back = self.code.len();
        self.code.extend([0; 4]);
        patch(self.code, back, loop_start)?;
        let done = self.code.len();
        patch(self.code, empty, done)?;
        self.frame_address(home);
        self.load_scalar(&result)?;
        Ok(result)
    }
}
