//! Closed const arguments are checked with their declared machine type. Host
//! arithmetic is checked too; overflowing intermediate expressions are errors.

use super::*;

pub(super) fn canonical(expression: &Expr, ty: &Type) -> Result<Expr> {
    let kind = match ty {
        Type::Bool => match expression.kind {
            Kind::Bool(value) => Kind::Bool(value),
            _ => return Err("boolean const arguments require a literal".into()),
        },
        Type::Machine(integer) => Kind::Constant(*integer, integer_value(expression, *integer)?),
        _ => return Err("const parameters currently require machine integers or bool".into()),
    };
    Ok(Expr { kind, line: 0 })
}

fn integer_value(expression: &Expr, ty: crate::syntax::MachineInt) -> Result<i128> {
    let value = match &expression.kind {
        Kind::Number(value) => *value,
        Kind::Constant(actual, value) if *actual == ty => *value,
        Kind::Unary(op, value) if op == "-" => match value.kind {
            Kind::Number(value) => value.checked_neg(),
            _ => integer_value(value, ty)?.checked_neg(),
        }
        .ok_or("const arithmetic exceeds bootstrap numeric resolution")?,
        Kind::Binary(op, a, b) => {
            let a = integer_value(a, ty)?;
            let b = integer_value(b, ty)?;
            match op.as_str() {
                "+" => a.checked_add(b),
                "-" => a.checked_sub(b),
                "*" => a.checked_mul(b),
                _ => return Err("const arguments support closed +, -, and * arithmetic".into()),
            }
            .ok_or("const arithmetic exceeds bootstrap numeric resolution")?
        }
        _ => {
            return Err(
                "const argument must be a closed compile-time value of its declared type".into(),
            )
        }
    };
    let (lo, hi) = ty.bounds();
    if !(lo..=hi).contains(&value) {
        return Err(
            "const argument or intermediate arithmetic exceeds its declared machine type".into(),
        );
    }
    Ok(value)
}
