//! Bounded, source-oriented expressions for diagnostics, not serialization.

use super::{Expr, GenericArgument, Kind, Type};

mod substitution;
pub(crate) use substitution::substituted;

pub(crate) fn expression(expr: &Expr) -> String {
    show(expr, &mut 80)
}

fn show(expr: &Expr, budget: &mut usize) -> String {
    if *budget == 0 {
        return "…".into();
    }
    *budget -= 1;
    match &expr.kind {
        Kind::Field(base, field) if field == super::Struct::SCALAR_VALUE => show(base, budget),
        Kind::Name(name) => name.clone(),
        Kind::Constant(integer, value) if *value == integer.bounds().1 && *value != 0 => {
            format!("{}::MAX", type_name(&Type::Machine(*integer), budget))
        }
        Kind::Constant(integer, value) if *value == integer.bounds().0 && *value != 0 => {
            format!("{}::MIN", type_name(&Type::Machine(*integer), budget))
        }
        Kind::Number(value) | Kind::Constant(_, value) => value.to_string(),
        Kind::Bool(value) => value.to_string(),
        Kind::Unit => "()".into(),
        Kind::Unary(op, value) => {
            let value_text = show(value, budget);
            match (&op[..], &value.kind) {
                ("&", Kind::Unary(inner, _)) if inner == "&" => format!("& {value_text}"),
                ("-", Kind::Unary(inner, _)) if inner == "-" => format!("-({value_text})"),
                _ => format!("{op}{value_text}"),
            }
        }
        Kind::Binary(op, a, b) => format!("({} {op} {})", show(a, budget), show(b, budget)),
        Kind::Field(base, field) => format!("{}.{field}", postfix(base, budget)),
        Kind::FactAt(base, fact) => format!("{}::{fact}", show(base, budget)),
        Kind::Index(base, index) => format!("{}[{}]", postfix(base, budget), show(index, budget)),
        Kind::Call(name, arguments) => format!("{name}({})", expressions(arguments, budget)),
        Kind::Type(ty) => type_name(ty, budget),
        Kind::Forall {
            variable,
            domain,
            body,
        } => format!(
            "forall({variable}: integer) where {} {{{}}}",
            show(domain, budget),
            show(body, budget)
        ),
        Kind::If(condition, a, b) => format!(
            "if {} {{{}}} else {{{}}}",
            show(condition, budget),
            show(a, budget),
            show(b, budget)
        ),
        Kind::Array(values) => format!(
            "[{}{}]",
            values
                .iter()
                .take(8)
                .map(|v| show(v, budget))
                .collect::<Vec<_>>()
                .join(", "),
            if values.len() > 8 { ", …" } else { "" }
        ),
        Kind::Record(name, _) => format!("{name} {{…}}"),
        Kind::Bytes(_) => "<string literal>".into(),
        Kind::Block(_, _) => "{…}".into(),
        Kind::Generic {
            value,
            arguments,
            member,
        } => {
            let arguments = arguments_text(arguments, budget);
            let member = member
                .as_ref()
                .map(|member| format!("::{member}"))
                .unwrap_or_default();
            match &value.kind {
                Kind::Call(name, values) => format!(
                    "{name}::<{arguments}>{member}({})",
                    expressions(values, budget)
                ),
                Kind::Record(name, _) => format!("{name}::<{arguments}> {{…}}"),
                _ => format!("{}::<{arguments}>{member}", show(value, budget)),
            }
        }
    }
}

fn postfix(expr: &Expr, budget: &mut usize) -> String {
    let text = show(expr, budget);
    match expr.kind {
        Kind::Name(_)
        | Kind::Field(..)
        | Kind::Index(..)
        | Kind::Call(..)
        | Kind::Generic { .. } => text,
        _ => format!("({text})"),
    }
}

fn argument(arg: &GenericArgument, budget: &mut usize) -> String {
    match arg {
        GenericArgument::Type(ty) => type_name(ty, budget),
        GenericArgument::Const(expr) => show(expr, budget),
    }
}

fn type_name(ty: &Type, budget: &mut usize) -> String {
    if *budget == 0 {
        return "…".into();
    }
    *budget -= 1;
    match ty {
        Type::Named(name) => name.clone(),
        Type::Machine(integer) if integer.domain == super::IntegerDomain::Zero => "Null".into(),
        Type::Machine(integer) => match (integer.signed, integer.bits) {
            (false, 64) => "usize".into(),
            (true, 64) => "isize".into(),
            (signed, bits) => format!("{}{bits}", if signed { "i" } else { "u" }),
        },
        Type::Int => "integer".into(),
        Type::Nat => "nat".into(),
        Type::Bool => "bool".into(),
        Type::Unit => "()".into(),
        Type::Ref(inner) => {
            let text = type_name(inner, budget);
            if matches!(inner.as_ref(), Type::Union(_)) {
                format!("&({text})")
            } else if matches!(inner.as_ref(), Type::Ref(_)) {
                format!("& {text}")
            } else {
                format!("&{text}")
            }
        }
        Type::Unique(inner) => format!("unique({})", type_name(inner, budget)),
        Type::Shared(inner) => format!("shared({})", type_name(inner, budget)),
        Type::Shape(inner) => format!("shape({})", type_name(inner, budget)),
        Type::Array(inner, extent) => {
            format!("[{}; {}]", type_name(inner, budget), show(extent, budget))
        }
        Type::Union(members) => {
            let mut items = members
                .iter()
                .take(8)
                .map(|ty| type_name(ty, budget))
                .collect::<Vec<_>>();
            if members.len() > 8 {
                items.push("…".into());
            }
            items.join(" | ")
        }
        Type::Apply(name, arguments) => format!("{name}<{}>", arguments_text(arguments, budget)),
    }
}

fn expressions(values: &[Expr], budget: &mut usize) -> String {
    let mut items = values
        .iter()
        .take(12)
        .map(|value| show(value, budget))
        .collect::<Vec<_>>();
    if values.len() > 12 {
        items.push("…".into());
    }
    items.join(", ")
}

fn arguments_text(values: &[GenericArgument], budget: &mut usize) -> String {
    let mut items = values
        .iter()
        .take(8)
        .map(|value| argument(value, budget))
        .collect::<Vec<_>>();
    if values.len() > 8 {
        items.push("…".into());
    }
    items.join(", ")
}
