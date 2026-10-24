//! Native sizes and alignment for the Linux x86-64 bootstrap target.
//! Fields retain declaration order. Empty values reserve one byte for identity.
//! This is not a C/FFI layout contract.

use crate::syntax::{Expr, Kind, Struct, Type};
use std::collections::{BTreeMap, BTreeSet};

type Result<T> = std::result::Result<T, String>;

pub const MAX_LAYOUT_BYTES: usize = 65536;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub offset: usize,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: usize,
    pub align: usize,
    pub fields: BTreeMap<String, Field>,
}

pub fn aggregate(ty: &Type) -> bool {
    matches!(ty, Type::Array(..) | Type::Named(_))
}

pub fn array_length(expression: &Expr) -> Result<usize> {
    fn machine_hint(expression: &Expr) -> bool {
        match &expression.kind {
            Kind::Constant(..) => true,
            Kind::Unary(_, x) => machine_hint(x),
            Kind::Binary(_, a, b) => machine_hint(a) || machine_hint(b),
            _ => false,
        }
    }

    fn integer(expression: &Expr, natural: bool) -> Result<i128> {
        let overflow = || "constant native layout arithmetic overflow".to_string();
        match &expression.kind {
            Kind::Number(n) | Kind::Constant(_, n) => Ok(*n),
            Kind::Unary(op, x) if op == "-" && !natural => {
                integer(x, natural)?.checked_neg().ok_or_else(overflow)
            }
            Kind::Binary(op, a, b) if matches!(op.as_str(), "+" | "-" | "*") => {
                let a = integer(a, natural)?;
                let b = integer(b, natural)?;
                match op.as_str() {
                    "+" => a.checked_add(b),
                    "-" if natural && a < b => Some(0),
                    "-" => a.checked_sub(b),
                    _ => a.checked_mul(b),
                }
                .ok_or_else(overflow)
            }
            _ => Err("native array layouts currently require constant integer lengths".into()),
        }
    }
    usize::try_from(integer(expression, !machine_hint(expression))?)
        .map_err(|_| "native array length is negative or exceeds the host limit".into())
}

pub fn of(ty: &Type, structs: &BTreeMap<String, Struct>) -> Result<Layout> {
    fn compute(
        ty: &Type,
        structs: &BTreeMap<String, Struct>,
        active: &mut BTreeSet<String>,
    ) -> Result<Layout> {
        let mut fields = BTreeMap::new();
        let mut align = 1;
        let size = match ty {
            Type::Machine(integer) => {
                align = usize::from(integer.bits / 8);
                align
            }
            Type::Bool => 1,
            Type::Unit => 1,
            Type::Ref(_) | Type::Plane(_) => {
                align = 8;
                8
            }
            Type::Int | Type::Nat => {
                return Err("ideal mathematical types have no native runtime layout".into())
            }
            Type::Array(element, count) => {
                let element = compute(element, structs, active)?;
                align = element.align;
                element
                    .size
                    .checked_mul(array_length(count)?)
                    .ok_or("native array layout overflow")?
                    .max(align)
            }
            Type::Named(name) => {
                let definition = structs
                    .get(name)
                    .ok_or_else(|| format!("unknown native layout type {name}"))?;
                if definition.ideal {
                    return Err(format!("ideal type {name} has no native runtime layout"));
                }
                if !active.insert(name.clone()) {
                    return Err("recursive inline native layout".into());
                }
                let mut offset = 0usize;
                for (name, ty) in definition.runtime_fields() {
                    let layout = compute(ty, structs, active)?;
                    align = align.max(layout.align);
                    offset = offset.next_multiple_of(layout.align);
                    if fields
                        .insert(
                            name.clone(),
                            Field {
                                offset,
                                ty: ty.clone(),
                            },
                        )
                        .is_some()
                    {
                        return Err("duplicate native layout field".into());
                    }
                    offset = offset
                        .checked_add(layout.size)
                        .ok_or("native record layout overflow")?;
                    if offset > MAX_LAYOUT_BYTES {
                        return Err("native object exceeds 64 KiB layout budget".into());
                    }
                }
                active.remove(name);
                offset.next_multiple_of(align).max(1)
            }
        };
        if size > MAX_LAYOUT_BYTES {
            return Err("native object exceeds 64 KiB layout budget".into());
        }
        Ok(Layout {
            size,
            align,
            fields,
        })
    }
    compute(ty, structs, &mut BTreeSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn definitions(source: &str) -> BTreeMap<String, Struct> {
        crate::syntax::parse(&format!("{source} fn main() {{}}"))
            .unwrap()
            .structs
            .into_iter()
            .map(|s| (s.name.clone(), s))
            .collect()
    }

    #[test]
    fn aggregate_layouts_preserve_declaration_order_and_field_alignment() {
        let defs = definitions("type Inner struct {small: u8, flag: bool} type Outer struct {first: usize, payload: [Inner; 2], last: &usize}");
        let layout = of(&Type::Named("Outer".into()), &defs).unwrap();
        assert_eq!(layout.size, 24);
        assert_eq!(layout.align, 8);
        assert_eq!(layout.fields["first"].offset, 0);
        assert_eq!(layout.fields["payload"].offset, 8);
        assert_eq!(layout.fields["last"].offset, 16);
        assert!(layout.fields.values().all(|f| f.offset % 8 == 0));
        let empty = definitions("type Empty struct {}");
        assert_eq!(of(&Type::Named("Empty".into()), &empty).unwrap().size, 1);
    }

    #[test]
    fn scalar_widths_array_strides_and_record_padding() {
        let defs = definitions("type Mixed struct {a: u8, b: u32, c: u16, d: bool} type Bytes struct {data: [u8; 7]} type Nested struct {head: u8, body: Mixed, tail: u8}");
        for (name, size) in [
            ("u8", 1),
            ("i8", 1),
            ("u16", 2),
            ("i16", 2),
            ("u32", 4),
            ("i32", 4),
            ("usize", 8),
            ("isize", 8),
        ] {
            let layout = of(
                &Type::Machine(crate::syntax::MachineInt::parse(name).unwrap()),
                &defs,
            )
            .unwrap();
            assert_eq!((layout.size, layout.align), (size, size), "{name}");
        }
        let mixed = of(&Type::Named("Mixed".into()), &defs).unwrap();
        assert_eq!((mixed.size, mixed.align), (12, 4));
        for (field, offset) in [("a", 0), ("b", 4), ("c", 8), ("d", 10)] {
            assert_eq!(mixed.fields[field].offset, offset);
        }
        let bytes = of(&Type::Named("Bytes".into()), &defs).unwrap();
        assert_eq!((bytes.size, bytes.align), (7, 1));
        let nested = of(&Type::Named("Nested".into()), &defs).unwrap();
        assert_eq!((nested.size, nested.align), (20, 4));
        assert_eq!(nested.fields["body"].offset, 4);
        assert_eq!(nested.fields["tail"].offset, 16);
        assert_eq!(of(&Type::Bool, &defs).unwrap().size, 1);
        assert_eq!(of(&Type::Unit, &defs).unwrap().size, 1);
        let empty_arrays = definitions("type Storage struct {data: [[u64; 0]; 2], tail: u8}");
        let storage = of(&Type::Named("Storage".into()), &empty_arrays).unwrap();
        assert_eq!((storage.size, storage.align), (24, 8));
        assert_eq!(storage.fields["tail"].offset, 16);
    }

    #[test]
    fn natural_length_folding_matches_the_frontend() {
        let defs = definitions("type Storage struct {data: [usize; (1 - 2) + 2]}");
        assert_eq!(of(&Type::Named("Storage".into()), &defs).unwrap().size, 16);
        let source = "type Storage struct {data: [usize; (1 - 2) + 2]} fn main() -> usize {let s = Storage {data: [7, 42]}; s.data[1]}";
        assert_eq!(
            crate::compiler::verify::verify(source)
                .unwrap()
                .run()
                .unwrap()
                .to_string(),
            "42"
        );
    }

    #[test]
    fn dependent_recursive_and_ideal_layouts_fail_closed() {
        for source in [
            "type Dynamic struct {len: usize, data: [usize; len]}",
            "type Loop struct {next: Loop}",
            "ideal type Model struct {n: nat}",
            "type Huge struct {data: [usize; 8193]}",
            "type Negative struct {data: [usize; -1]}",
            "type Overflow struct {data: [usize; 170141183460469231731687303715884105727 * 2]}",
        ] {
            let defs = definitions(source);
            assert!(
                of(&Type::Named(defs.keys().next().unwrap().clone()), &defs).is_err(),
                "{source}"
            );
        }
    }
}
