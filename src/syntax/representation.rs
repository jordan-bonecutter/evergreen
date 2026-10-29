//! Literal primitive type construction. Target representations are data, not
//! arbitrary compile-time code or unchecked conversions between runtime types.

use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Endianness {
    Little,
    Big,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegralEncoding {
    Binary,
    TwosComplement,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Representation {
    Integral {
        signed: bool,
        bits: u8,
        encoding: IntegralEncoding,
        endian: Endianness,
    },
    Boolean,
    Unit,
    Pointer {
        bits: u8,
        endian: Endianness,
    },
}

#[derive(Clone, Debug)]
pub struct ScalarDefinition {
    pub name: String,
    pub size: usize,
    pub align: usize,
    pub represents: Representation,
    pub module: Option<String>,
    pub line: usize,
}

fn integer(value: Expr) -> Result<usize, String> {
    match value.kind {
        Kind::Number(n) => usize::try_from(n)
            .map_err(|_| "representation sizes require nonnegative integer literals".into()),
        _ => Err("representation sizes require integer literals".into()),
    }
}

fn take(fields: &mut BTreeMap<String, Expr>, name: &str) -> Result<Expr, String> {
    fields
        .remove(name)
        .ok_or_else(|| format!("missing representation field {name}"))
}

fn fields(entries: Vec<(String, Expr)>) -> Result<BTreeMap<String, Expr>, String> {
    let mut result = BTreeMap::new();
    for (name, value) in entries {
        if result.insert(name.clone(), value).is_some() {
            return Err(format!("duplicate representation field {name}"));
        }
    }
    Ok(result)
}

fn variant(value: Expr) -> Result<String, String> {
    match value.kind {
        Kind::FactAt(base, name) if matches!(&base.kind, Kind::Name(module) if module == "repr") => {
            Ok(name)
        }
        _ => Err("expected a repr:: representation variant".into()),
    }
}

fn endian(fields: &mut BTreeMap<String, Expr>) -> Result<Endianness, String> {
    match variant(take(fields, "endian")?)?.as_str() {
        "Little" => Ok(Endianness::Little),
        "Big" => Ok(Endianness::Big),
        _ => Err("expected repr::Little or repr::Big".into()),
    }
}

fn representation(value: Expr) -> Result<Representation, String> {
    let Kind::Record(name, entries) = value.kind else {
        return Err("represents requires a repr:: representation record".into());
    };
    let mut fields = fields(entries)?;
    let result = match name.as_str() {
        "repr::Integral" => {
            let signed = match take(&mut fields, "signed")?.kind {
                Kind::Bool(b) => b,
                _ => return Err("signed requires a boolean literal".into()),
            };
            let bits = u8::try_from(integer(take(&mut fields, "bits")?)?)
                .map_err(|_| "representation bit width exceeds 255")?;
            let encoding = match variant(take(&mut fields, "encoding")?)?.as_str() {
                "Binary" => IntegralEncoding::Binary,
                "TwosComplement" => IntegralEncoding::TwosComplement,
                _ => return Err("expected repr::Binary or repr::TwosComplement".into()),
            };
            Representation::Integral {
                signed,
                bits,
                encoding,
                endian: endian(&mut fields)?,
            }
        }
        "repr::Boolean" => Representation::Boolean,
        "repr::Unit" => Representation::Unit,
        "repr::Pointer" => {
            let bits = u8::try_from(integer(take(&mut fields, "bits")?)?)
                .map_err(|_| "representation bit width exceeds 255")?;
            Representation::Pointer {
                bits,
                endian: endian(&mut fields)?,
            }
        }
        _ => return Err(format!("unknown representation {name}")),
    };
    if !fields.is_empty() {
        return Err(format!(
            "unknown representation fields: {}",
            fields.keys().cloned().collect::<Vec<_>>().join(", ")
        ));
    }
    Ok(result)
}

impl ScalarDefinition {
    pub fn validate(&self) -> Result<(), String> {
        if self.size == 0
            || self.size > 8
            || !self.align.is_power_of_two()
            || self.align > self.size
            || !self.size.is_multiple_of(self.align)
        {
            return Err(format!(
                "line {}: invalid scalar size/alignment for {}",
                self.line, self.name
            ));
        }
        let valid = match self.represents {
            Representation::Integral {
                signed,
                bits,
                encoding,
                ..
            } => {
                usize::from(bits) == self.size * 8
                    && matches!(bits, 8 | 16 | 32 | 64)
                    && encoding
                        == if signed {
                            IntegralEncoding::TwosComplement
                        } else {
                            IntegralEncoding::Binary
                        }
            }
            Representation::Pointer { bits, .. } => usize::from(bits) == self.size * 8,
            Representation::Boolean | Representation::Unit => self.size == 1,
        };
        if !valid {
            return Err(format!(
                "line {}: representation does not match storage for {}",
                self.line, self.name
            ));
        }
        Ok(())
    }
}

impl Parser {
    pub(super) fn scalar_definition(&mut self) -> Result<ScalarDefinition, String> {
        let line = self.line();
        self.expect("type")?;
        let name = self.name()?;
        self.expect("=")?;
        if !self.eat("make_type") {
            return Err(self.err(
                "type aliases with '=' are not supported; use 'type NonZero usize where self != 0;' for a refined scalar, a struct with a where clause for fields, or make_type(...) for a primitive representation",
            ));
        }
        self.expect("(")?;
        let mut entries = Vec::new();
        if !self.eat(")") {
            loop {
                let field = self.name()?;
                self.expect(":")?;
                entries.push((field, self.expr(0)?));
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
                if self.eat(")") {
                    break;
                }
            }
        }
        self.expect(";")?;
        let mut fields = fields(entries)?;
        let definition = ScalarDefinition {
            name,
            line,
            module: None,
            size: integer(take(&mut fields, "size")?)?,
            align: integer(take(&mut fields, "align")?)?,
            represents: representation(take(&mut fields, "represents")?)?,
        };
        if !fields.is_empty() {
            return Err("make_type accepts only size, align, and represents".into());
        }
        definition.validate()?;
        Ok(definition)
    }
}
