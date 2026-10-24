//! Literal target data written in Evergreen. Decoding does not execute code.
//! The instruction backend still validates the widths it can implement.

use crate::syntax::{self, Kind, MachineInt, Type};
use std::{collections::BTreeMap, sync::OnceLock};

type Result<T> = std::result::Result<T, String>;

const X86_64: &str = include_str!("../../targets/x86_64.evg");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScalarLayout {
    pub size: usize,
    pub align: usize,
}

pub(crate) struct Target {
    layouts: BTreeMap<String, ScalarLayout>,
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
        for function in program.functions {
            let name = function
                .name
                .strip_prefix("x86_64::layout_")
                .ok_or("unexpected function in x86-64 target data")?;
            if !function.ideal
                || !function.params.is_empty()
                || !function.body.is_empty()
                || function.external.is_some()
                || function.proof.is_some()
                || function.pre.is_some()
                || function.decreases.is_some()
                || !function.modifies.is_empty()
                || !function.borrows.is_empty()
                || function.ret != Type::Named("x86_64::ScalarLayout".into())
            {
                return Err(
                    "target layouts require ideal, parameterless literal data producers".into(),
                );
            }
            let Kind::Record(record, fields) = function.result.kind else {
                return Err("target layout must be a literal ScalarLayout record".into());
            };
            if record != "x86_64::ScalarLayout" || fields.len() != 2 {
                return Err("target layout requires size and alignment".into());
            }
            let mut values = BTreeMap::new();
            for (field, value) in fields {
                let Kind::Number(value) = value.kind else {
                    return Err("target layout fields must be nonnegative integer literals".into());
                };
                let value = usize::try_from(value)
                    .map_err(|_| "target layout value exceeds host limits")?;
                if values.insert(field, value).is_some() {
                    return Err("duplicate target layout field".into());
                }
            }
            let size = *values.get("size").ok_or("missing target size")?;
            let align = *values.get("alignment").ok_or("missing target alignment")?;
            let expected_size = match name {
                "bool" | "unit" => 1,
                "pointer" => 8,
                _ => usize::from(MachineInt::parse(name).ok_or("unknown target scalar")?.bits / 8),
            };
            if size != expected_size
                || !align.is_power_of_two()
                || align > 8
                || !size.is_multiple_of(align)
            {
                return Err(format!(
                    "target layout of {name} is incompatible with the x86-64 backend"
                ));
            }
            if layouts
                .insert(name.to_owned(), ScalarLayout { size, align })
                .is_some()
            {
                return Err("duplicate target scalar layout".into());
            }
        }
        for name in [
            "u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64", "bool", "unit", "pointer",
        ] {
            if !layouts.contains_key(name) {
                return Err(format!("missing target layout for {name}"));
            }
        }
        Ok(Self { layouts })
    }

    pub(crate) fn scalar(&self, ty: &Type) -> Result<ScalarLayout> {
        let name = match ty {
            Type::Machine(integer) => {
                format!("{}{}", if integer.signed { 'i' } else { 'u' }, integer.bits)
            }
            Type::Bool => "bool".into(),
            Type::Unit => "unit".into(),
            Type::Ref(_) | Type::Plane(_) => "pointer".into(),
            _ => return Err("aggregate or ideal type requested as a target scalar".into()),
        };
        self.layouts
            .get(&name)
            .copied()
            .ok_or_else(|| format!("target does not support scalar {name}"))
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
        let source = X86_64
            .replace("size: 8, alignment: 8", "size: 8, alignment: 4")
            .replace(
                "result.size == 8 && result.alignment == 8",
                "result.size == 8 && result.alignment == 4",
            );
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
            X86_64.replace("size: 1, alignment: 1", "size: 2, alignment: 1"),
            X86_64.replace("size: 8, alignment: 8", "size: 8, alignment: 3"),
            X86_64.replace("size: 8, alignment: 8", "size: 8, alignment: 0"),
            X86_64.replace("size: 8, alignment: 8", "size: 8, alignment: 16"),
            X86_64.replace("size: 1, alignment: 1", "size: 1 + 0, alignment: 1"),
            X86_64.replace("layout_u8", "layout_unknown"),
            X86_64.replace("layout_i8", "layout_u8"),
            X86_64.replace("alignment: 1", "size: 1"),
            X86_64.replace("ideal fn layout_u8", "fn layout_u8"),
            X86_64.replace("layout_u8()", "layout_u8(n: nat)"),
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
