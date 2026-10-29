//! Literal target data written in Evergreen. Decoding does not execute code.
//! The instruction backend still validates the widths it can implement.

use crate::syntax::{self, Endianness, MachineInt, Representation, Type};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::OnceLock,
};

type Result<T> = std::result::Result<T, String>;

const X86_64: &str = include_str!("../../targets/x86_64.evg");
const WASM: &str = include_str!("../../targets/wasm.evg");

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TargetKind {
    #[default]
    X86_64,
    Wasm32,
}

impl TargetKind {
    pub(crate) fn module(self) -> &'static str {
        match self {
            Self::X86_64 => "x86_64",
            Self::Wasm32 => "wasm",
        }
    }

    pub(crate) fn source(self) -> &'static str {
        match self {
            Self::X86_64 => X86_64,
            Self::Wasm32 => WASM,
        }
    }

    pub(crate) fn word_bits(self) -> u8 {
        match self {
            Self::X86_64 => 64,
            Self::Wasm32 => 32,
        }
    }

    pub(crate) fn max_allocation_bytes(self) -> u64 {
        (1u64 << (self.word_bits() - 1)) - 1
    }

    pub(crate) fn max_array_length(self, stride: usize) -> i128 {
        if stride == 0 {
            self.integer("usize").expect("word type").bounds().1
        } else {
            (self.max_allocation_bytes() / stride as u64) as i128
        }
    }

    pub(crate) fn integer(self, name: &str) -> Option<MachineInt> {
        MachineInt::for_word_bits(name, self.word_bits())
    }

    pub(crate) fn profile(self) -> Result<&'static Target> {
        static NATIVE: OnceLock<Result<Target>> = OnceLock::new();
        static BROWSER: OnceLock<Result<Target>> = OnceLock::new();
        let slot = match self {
            Self::X86_64 => &NATIVE,
            Self::Wasm32 => &BROWSER,
        };
        slot.get_or_init(|| Target::decode_for(self, self.source()))
            .as_ref()
            .map_err(Clone::clone)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScalarLayout {
    pub size: usize,
    pub align: usize,
}

pub(crate) struct Target {
    layouts: BTreeMap<String, ScalarLayout>,
    copy_types: BTreeSet<String>,
}

impl Target {
    #[cfg(test)]
    fn decode(source: &str) -> Result<Self> {
        Self::decode_for(TargetKind::X86_64, source)
    }

    fn decode_for(kind: TargetKind, source: &str) -> Result<Self> {
        let program = syntax::parse_with_word_bits(source, kind.word_bits())?;
        let mut layouts = BTreeMap::new();
        if !program.functions.is_empty()
            || !program.structs.is_empty()
            || !program.destructors.is_empty()
        {
            return Err(
                "target profiles contain only make_type declarations and Copy implementations"
                    .into(),
            );
        }
        for definition in program.scalar_types {
            if definition.module.as_deref() != Some(kind.module()) {
                return Err(format!(
                    "target declarations require module {}",
                    kind.module()
                ));
            }
            let name = definition.name.as_str();
            let ty = representation_type(&definition.represents)?;
            let expected = match name {
                "bool" => Some(Type::Bool),
                "unit" => Some(Type::Unit),
                "pointer" => None,
                _ => Some(Type::Machine(
                    kind.integer(name).ok_or("unknown target scalar")?,
                )),
            };
            if name == "pointer" {
                if !matches!(
                    definition.represents,
                    Representation::Pointer {
                        bits,
                        endian: Endianness::Little
                    } if bits == kind.word_bits()
                ) {
                    return Err(format!(
                        "{} pointers require a {}-bit little-endian representation",
                        kind.module(),
                        kind.word_bits()
                    ));
                }
            } else if ty
                != expected.as_ref().map(|ty| match ty {
                    Type::Machine(integer) => Type::Machine(integer.representation()),
                    other => other.clone(),
                })
            {
                return Err(format!(
                    "representation of {name} does not match its declared integer meaning"
                ));
            }
            if layouts
                .insert(
                    name.to_owned(),
                    ScalarLayout {
                        size: definition.size,
                        align: definition.align,
                    },
                )
                .is_some()
            {
                return Err("duplicate target scalar definition".into());
            }
        }
        for name in [
            "u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64", "usize", "isize", "bool", "unit",
            "pointer", "Null",
        ] {
            if !layouts.contains_key(name) {
                return Err(format!("missing target layout for {name}"));
            }
        }
        let unsigned = if kind.word_bits() == 32 { "u32" } else { "u64" };
        let signed = if kind.word_bits() == 32 { "i32" } else { "i64" };
        for (alias, base) in [("usize", unsigned), ("isize", signed), ("Null", "usize")] {
            if layouts[alias] != layouts[base] {
                return Err(format!(
                    "{alias} must share the {base} layout on {}",
                    kind.module()
                ));
            }
        }
        let mut copy_types = BTreeSet::new();
        for implementation in program.copy_impls {
            if implementation.module.as_deref() != Some(kind.module()) {
                return Err(format!(
                    "target Copy implementations require module {}",
                    kind.module()
                ));
            }
            let name = implementation
                .target
                .strip_prefix(&format!("{}::", kind.module()))
                .ok_or("Copy requires a declared target primitive")?;
            if !layouts.contains_key(name) {
                return Err(format!(
                    "unknown target primitive in Copy implementation: {name}"
                ));
            }
            if !copy_types.insert(name.to_owned()) {
                return Err(format!("duplicate target Copy implementation for {name}"));
            }
        }
        for (alias, base) in [("usize", unsigned), ("isize", signed)] {
            if copy_types.contains(alias) != copy_types.contains(base) {
                return Err(format!("{alias} must share the {base} Copy implementation"));
            }
        }
        Ok(Self {
            layouts,
            copy_types,
        })
    }

    /// Layout aliases share a primitive identity; owned planes remain move-only
    /// even when the raw pointer representation implements Copy.
    pub(crate) fn is_copy(&self, ty: &Type) -> bool {
        let name = match ty {
            Type::Machine(integer) => integer.primitive_name(),
            Type::Bool => "bool".into(),
            Type::Unit => "unit".into(),
            Type::Ref(_) | Type::Shared(_) => "pointer".into(),
            _ => return false,
        };
        self.copy_types.contains(&name)
    }

    pub(crate) fn scalar(&self, ty: &Type) -> Result<ScalarLayout> {
        let name = match ty {
            Type::Machine(integer) => integer.primitive_name(),
            Type::Bool => "bool".into(),
            Type::Unit => "unit".into(),
            Type::Ref(_) | Type::Unique(_) | Type::Shared(_) => "pointer".into(),
            _ => return Err("aggregate or ideal type requested as a target scalar".into()),
        };
        self.layouts
            .get(&name)
            .copied()
            .ok_or_else(|| format!("target does not support scalar {name}"))
    }
}

pub(crate) fn representation_type(representation: &Representation) -> Result<Option<Type>> {
    match *representation {
        Representation::Integral {
            signed,
            bits,
            endian: Endianness::Little,
            ..
        } => Ok(Some(Type::Machine(MachineInt {
            signed,
            bits,
            domain: syntax::IntegerDomain::Full,
        }))),
        Representation::Boolean => Ok(Some(Type::Bool)),
        Representation::Unit => Ok(Some(Type::Unit)),
        Representation::Pointer {
            bits: 32 | 64,
            endian: Endianness::Little,
        } => Ok(None),
        _ => Err("representation is unsupported by the bootstrap backends".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::verify::{prove, verify_with_certificate};
    use crate::syntax::format::test_edit::SourceEdit;

    #[test]
    fn wasm_profile_controls_layout_literals_inference_and_runtime() {
        use crate::compiler::verify::{
            prove_for_target, verify_for_target, verify_with_certificate_for_target,
        };
        let target = TargetKind::Wasm32;
        let (profile, certificate) = prove_for_target(WASM, target).unwrap();
        assert!(profile.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate_for_target(WASM, &certificate, target)
                .unwrap()
                .proof_search_count(),
            0
        );
        let source = r#"
            type Pair struct {byte: u8, word: usize, wide: u64}
            fn first<T>(length: usize, data: &[T; length]) -> T where length > 0 {(*data)[0]}
            fn main() -> usize {
                proof _: usize::MAX == 4294967295 && isize::MIN == -2147483648;
                proof _: size_of(usize) == 4 && size_of(isize) == 4 && size_of(Null) == 4;
                proof _: size_of(&usize) == 4 && size_of(u64) == 8 && size_of(i64) == 8;
                proof _: size_of([usize; 3]) == 12 && size_of(Pair) == 16;
                let words: [usize; 2] = [42, 7];
                let answer = first(&words);
                proof _: typeof(answer) == usize;
                answer
            }
        "#;
        let (program, bundle) = prove_for_target(source, target).unwrap();
        assert_eq!(program.target(), target);
        assert_eq!(program.run().unwrap().to_string(), "42");
        assert_eq!(
            verify_with_certificate_for_target(source, &bundle, target)
                .unwrap()
                .proof_search_count(),
            0
        );
        for source in [
            "fn main() -> usize {4294967296}",
            "fn main() -> usize {usize(u64::MAX)}",
            "fn main() {proof _: usize::MAX == 18446744073709551615;}",
            "fn main() -> usize {size_of([u8; 2147483648])}",
        ] {
            assert!(
                verify_for_target(source, target).is_err(),
                "accepted {source}"
            );
        }
        for source in [
            include_str!("../../examples/generics.evg"),
            "fn main() -> usize {let data: unique(usize | shape(usize), 1) = alloc(1, shape(usize)); (*data)[0] = 42; let value: usize = move((*data)[0]); arrays::release_empty::<usize>(data); value}",
        ] {
            assert_eq!(verify_for_target(source, target).unwrap().run().unwrap().to_string(), "42");
        }
    }

    #[test]
    fn target_certificates_and_emitters_cannot_be_mixed() {
        use crate::compiler::verify::{prove_for_target, verify_with_certificate_for_target};
        let source = "fn main() -> usize {42}";
        for (target, other) in [
            (TargetKind::X86_64, TargetKind::Wasm32),
            (TargetKind::Wasm32, TargetKind::X86_64),
        ] {
            let (program, bundle) = prove_for_target(source, target).unwrap();
            assert!(verify_with_certificate_for_target(source, &bundle, other).is_err());
            assert_eq!(
                crate::compiler::native::emit(&program).is_ok(),
                target == TargetKind::X86_64
            );
            assert_eq!(
                crate::compiler::wasm::emit(&program).is_ok(),
                target == TargetKind::Wasm32
            );
        }
    }

    #[test]
    fn target_data_is_checked_evergreen_and_replays_without_trust() {
        let (program, bundle) = prove(X86_64).unwrap();
        assert!(program.trusted_assumptions().is_empty());
        assert_eq!(
            verify_with_certificate(X86_64, &bundle)
                .unwrap()
                .proof_search_count(),
            0
        );
        let target = Target::decode(X86_64).unwrap();
        assert_eq!(
            target
                .scalar(&Type::Machine(MachineInt::parse("u16").unwrap()))
                .unwrap(),
            ScalarLayout { size: 2, align: 2 }
        );
        // Alignment is data, not reconstructed from the integer width.
        let source = X86_64.replace_evg("size: 8, align: 8", "size: 8, align: 4");
        assert!(prove(&source).unwrap().0.trusted_assumptions().is_empty());
        let target = Target::decode(&source).unwrap();
        assert_eq!(
            target
                .scalar(&Type::Machine(MachineInt::parse("u64").unwrap()))
                .unwrap(),
            ScalarLayout { size: 8, align: 4 }
        );
    }

    #[test]
    fn malformed_or_incompatible_target_data_fails_closed() {
        for source in [
            X86_64.replace_evg("size: 1, align: 1", "size: 2, align: 1"),
            X86_64.replace_evg("size: 0, align: 1", "size: 1, align: 1"),
            X86_64.replace_evg("size: 0, align: 1", "size: 0, align: 2"),
            X86_64.replace_evg("size: 8, align: 8", "size: 8, align: 3"),
            X86_64.replace_evg("size: 8, align: 8", "size: 8, align: 0"),
            X86_64.replace_evg("size: 8, align: 8", "size: 8, align: 16"),
            X86_64.replace_evg("size: 1, align: 1", "size: 1 + 0, align: 1"),
            X86_64.replace_evg("type u8 =", "type unknown ="),
            X86_64.replace_evg("type i8 =", "type u8 ="),
            X86_64.replace_evg("align: 1", "size: 1"),
            X86_64.replace_evg("repr::Little", "repr::Big"),
            X86_64.replace_evg("signed: true", "signed: false"),
            X86_64.replace_evg("bits: 64", "bits: 32"),
            X86_64.replace_evg("repr::TwosComplement", "repr::Binary"),
        ] {
            assert!(
                Target::decode(&source).is_err(),
                "accepted malformed profile"
            );
        }
        let target = Target::decode(X86_64).unwrap();
        assert!(target
            .scalar(&Type::Machine(MachineInt {
                signed: false,
                bits: 7,
                domain: syntax::IntegerDomain::Full
            }))
            .is_err());
    }
}

#[cfg(test)]
mod copy_tests {
    use super::*;
    use crate::syntax::format::test_edit::SourceEdit;

    fn machine(name: &str) -> Type {
        Type::Machine(MachineInt::parse(name).unwrap())
    }

    #[test]
    fn copying_requires_an_explicit_primitive_trait_implementation() {
        let source = X86_64.replace_evg("impl Copy for u8 {}", "");
        let target = Target::decode(&source).unwrap();
        assert!(!target.is_copy(&machine("u8")));
        let source = X86_64.replace_evg("impl Copy for Null {}", "");
        let without_null_copy = Target::decode(&source).unwrap();
        assert!(!without_null_copy.is_copy(&machine("Null")));
        assert!(without_null_copy.is_copy(&machine("usize")));
        assert!(target.is_copy(&machine("u16")));
        let source = X86_64.replace_evg("impl Copy for pointer {}", "");
        let target = Target::decode(&source).unwrap();
        assert!(!target.is_copy(&Type::Ref(Box::new(Type::Unit))));
        let target = Target::decode(X86_64).unwrap();
        assert!(target.is_copy(&Type::Ref(Box::new(Type::Unit))));
        assert!(!target.is_copy(&Type::Unique(Box::new(Type::Unit))));
        let source = X86_64.replace_evg("impl Copy for bool {}", "");
        assert!(!Target::decode(&source).unwrap().is_copy(&Type::Bool));
    }

    #[test]
    fn invalid_primitive_copy_declarations_are_rejected() {
        for source in [
            format!("{X86_64} impl Copy for u8 {{}}"),
            format!("{X86_64} impl Copy for Unknown {{}}"),
            X86_64.replace_evg("impl Copy for usize {}", ""),
            X86_64.replace_evg("impl Copy for isize {}", ""),
        ] {
            assert!(Target::decode(&source).is_err());
        }
    }
}
