//! Literal target data written in Evergreen. Decoding does not execute code.
//! The instruction backend still validates the widths it can implement.

use crate::syntax::{self, Endianness, MachineInt, Representation, Type};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::OnceLock,
};

type Result<T> = std::result::Result<T, String>;

const X86_64: &str = include_str!("../../targets/x86_64.evg");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScalarLayout {
    pub size: usize,
    pub align: usize,
}

pub(crate) struct Target {
    layouts: BTreeMap<String, ScalarLayout>,
    copy_types: BTreeSet<String>,
}

pub(crate) fn native() -> Result<&'static Target> {
    static TARGET: OnceLock<Result<Target>> = OnceLock::new();
    TARGET
        .get_or_init(|| Target::decode(X86_64))
        .as_ref()
        .map_err(Clone::clone)
}

impl Target {
    fn decode(source: &str) -> Result<Self> {
        let program = syntax::parse(source)?;
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
            if definition.module.as_deref() != Some("x86_64") {
                return Err("x86-64 target declarations require module x86_64".into());
            }
            let name = definition.name.as_str();
            let ty = representation_type(&definition.represents)?;
            let expected = match name {
                "bool" => Some(Type::Bool),
                "unit" => Some(Type::Unit),
                "pointer" => None,
                _ => Some(Type::Machine(
                    MachineInt::parse(name).ok_or("unknown target scalar")?,
                )),
            };
            if name == "pointer" {
                if !matches!(
                    definition.represents,
                    Representation::Pointer {
                        bits: 64,
                        endian: Endianness::Little
                    }
                ) {
                    return Err(
                        "x86-64 pointers require a 64-bit little-endian representation".into(),
                    );
                }
            } else if ty != expected {
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
            "pointer",
        ] {
            if !layouts.contains_key(name) {
                return Err(format!("missing target layout for {name}"));
            }
        }
        for (alias, base) in [("usize", "u64"), ("isize", "i64")] {
            if layouts[alias] != layouts[base] {
                return Err(format!("{alias} must share the {base} layout on x86-64"));
            }
        }
        let mut copy_types = BTreeSet::new();
        for implementation in program.copy_impls {
            if implementation.module.as_deref() != Some("x86_64") {
                return Err("target Copy implementations require module x86_64".into());
            }
            let name = implementation
                .target
                .strip_prefix("x86_64::")
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
        for (alias, base) in [("usize", "u64"), ("isize", "i64")] {
            if copy_types.contains(alias) != copy_types.contains(base) {
                return Err(format!(
                    "{alias} must share the {base} Copy implementation on x86-64"
                ));
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
            Type::Machine(integer) => {
                format!("{}{}", if integer.signed { 'i' } else { 'u' }, integer.bits)
            }
            Type::Bool => "bool".into(),
            Type::Unit => "unit".into(),
            Type::Ref(_) | Type::Shared(_) => "pointer".into(),
            _ => return false,
        };
        self.copy_types.contains(&name)
    }

    pub(crate) fn scalar(&self, ty: &Type) -> Result<ScalarLayout> {
        let name = match ty {
            Type::Machine(integer) => {
                format!("{}{}", if integer.signed { 'i' } else { 'u' }, integer.bits)
            }
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
        } => Ok(Some(Type::Machine(MachineInt { signed, bits }))),
        Representation::Boolean => Ok(Some(Type::Bool)),
        Representation::Unit => Ok(Some(Type::Unit)),
        Representation::Pointer {
            bits: 64,
            endian: Endianness::Little,
        } => Ok(None),
        _ => Err("representation is unsupported by the Linux x86-64 backend".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::verify::{prove, verify_with_certificate};

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
        let source = X86_64.replace("size: 8, align: 8", "size: 8, align: 4");
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
            X86_64.replace("size: 1, align: 1", "size: 2, align: 1"),
            X86_64.replace("size: 8, align: 8", "size: 8, align: 3"),
            X86_64.replace("size: 8, align: 8", "size: 8, align: 0"),
            X86_64.replace("size: 8, align: 8", "size: 8, align: 16"),
            X86_64.replace("size: 1, align: 1", "size: 1 + 0, align: 1"),
            X86_64.replace("type u8 =", "type unknown ="),
            X86_64.replace("type i8 =", "type u8 ="),
            X86_64.replace("align: 1", "size: 1"),
            X86_64.replace("repr::Little", "repr::Big"),
            X86_64.replace("signed: true", "signed: false"),
            X86_64.replace("bits: 64", "bits: 32"),
            X86_64.replace("repr::TwosComplement", "repr::Binary"),
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
                bits: 7
            }))
            .is_err());
    }
}

#[cfg(test)]
mod copy_tests {
    use super::*;

    fn machine(name: &str) -> Type {
        Type::Machine(MachineInt::parse(name).unwrap())
    }

    #[test]
    fn copying_requires_an_explicit_primitive_trait_implementation() {
        let source = X86_64.replace("impl Copy for u8 {}", "");
        let target = Target::decode(&source).unwrap();
        assert!(!target.is_copy(&machine("u8")));
        assert!(target.is_copy(&machine("u16")));
        let source = X86_64.replace("impl Copy for pointer {}", "");
        let target = Target::decode(&source).unwrap();
        assert!(!target.is_copy(&Type::Ref(Box::new(Type::Unit))));
        let target = Target::decode(X86_64).unwrap();
        assert!(target.is_copy(&Type::Ref(Box::new(Type::Unit))));
        assert!(!target.is_copy(&Type::Unique(Box::new(Type::Unit))));
        let source = X86_64.replace("impl Copy for bool {}", "");
        assert!(!Target::decode(&source).unwrap().is_copy(&Type::Bool));
    }

    #[test]
    fn invalid_primitive_copy_declarations_are_rejected() {
        for source in [
            format!("{X86_64} impl Copy for u8 {{}}"),
            format!("{X86_64} impl Copy for Unknown {{}}"),
            X86_64.replace("impl Copy for usize {}", ""),
            X86_64.replace("impl Copy for isize {}", ""),
        ] {
            assert!(Target::decode(&source).is_err());
        }
    }
}
