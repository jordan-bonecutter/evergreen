//! Target atomic instruction emission. Protocols remain Evergreen library code.

use super::*;

impl Emitter<'_> {
    pub(super) fn compare_exchange64(&mut self, function: &Function) -> Result<()> {
        let parameters = function
            .params
            .iter()
            .filter(|(name, _)| !function.ideal_params.contains(name))
            .collect::<Vec<_>>();
        let [(pointer, ty), (expected, _), (desired, _)] = parameters.as_slice() else {
            return Err(
                "compare_exchange64 requires pointer, expected, and desired operands".into(),
            );
        };
        let Type::Ref(inner) = ty else {
            return Err("compare_exchange64 requires a referenced integer".into());
        };
        let storage = layout::of(inner, self.structs)?;
        if storage.size != 8 || storage.align != 8 {
            return Err("compare_exchange64 requires eight-byte storage and alignment".into());
        }
        self.load(pointer)?;
        self.code.extend([0x48, 0x89, 0xc2]); // rdx = address
        self.load(desired)?;
        self.code.extend([0x48, 0x89, 0xc1]); // rcx = desired bits
        self.load(expected)?; // rax = expected bits
        self.code.extend([0xf0, 0x48, 0x0f, 0xb1, 0x0a]); // lock cmpxchg [rdx], rcx
                                                          // rax is the observed old value, on both success and failure.
        Ok(())
    }
}
