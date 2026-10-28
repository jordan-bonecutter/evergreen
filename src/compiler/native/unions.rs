//! Union coercions move bytes at offset zero. Active-member evidence was checked
//! by the verifier; this backend emits no selector or runtime discriminator.

use super::*;

impl Emitter<'_> {
    pub(super) fn pointer_operand(&mut self, expression: &Expr) -> Result<Type> {
        let ty = self.storage_value(expression)?;
        let pointer = ty
            .pointer_member()
            .cloned()
            .ok_or("native dereference requires an unambiguous pointer member")?;
        self.union_value(ty, Some(&pointer))
    }

    pub(super) fn zero_storage(&mut self, home: i32, size: usize) {
        self.frame_address(home);
        self.code.extend([0x48, 0x89, 0xc7]); // rdi = destination
        self.immediate(size as u64);
        self.code
            .extend([0x48, 0x89, 0xc1, 0x31, 0xc0, 0xfc, 0xf3, 0xaa]); // rcx = size; xor eax; cld; rep stosb
    }

    pub(super) fn union_value(&mut self, got: Type, expected: Option<&Type>) -> Result<Type> {
        let Some(expected) = expected else {
            return Ok(got);
        };
        if Self::compatible(&got, expected)? {
            return Ok(expected.clone());
        }
        if let (Type::Unique(inner), Type::Shared(target))
        | (Type::Shared(inner), Type::Unique(target)) = (&got, expected)
        {
            if Self::compatible(inner, target)? {
                return Ok(expected.clone());
            }
        }
        if let Type::Union(members) = expected {
            if members.iter().try_fold(false, |found, member| {
                Ok::<_, String>(found || Self::compatible(&got, member)?)
            })? {
                let source = self.allocate(&got)?;
                self.copy_frame(source, &got)?;
                let home = self.allocate(expected)?;
                self.zero_storage(home, layout::of(expected, self.structs)?.size);
                self.frame_address(source);
                if !layout::aggregate(&got) {
                    self.load_scalar(&got)?;
                }
                self.copy_frame(home, &got)?;
                self.frame_address(home);
                return Ok(expected.clone());
            }
        }
        if let Type::Union(members) = &got {
            if members.iter().try_fold(false, |found, member| {
                Ok::<_, String>(found || Self::compatible(member, expected)?)
            })? {
                if !layout::aggregate(expected) {
                    self.load_scalar(expected)?;
                }
                return Ok(expected.clone());
            }
        }
        Ok(got)
    }
    pub(super) fn shape_value(&mut self, value: &Expr) -> Result<Type> {
        let ty = Type::Shape(Box::new(
            value.literal_type().ok_or("shape requires a type")?,
        ));
        let home = self.allocate(&ty)?;
        self.zero_storage(home, layout::of(&ty, self.structs)?.size);
        self.frame_address(home);
        Ok(ty)
    }
}
