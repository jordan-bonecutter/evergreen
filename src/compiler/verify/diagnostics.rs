//! Bounded normalized obligations for failed proof diagnostics.

use super::{Formula, Linear, Ty};
use std::collections::{BTreeMap, BTreeSet};

mod types;

pub(super) fn obligation(goal: &Formula, types: &BTreeMap<String, Ty>) -> String {
    let labels = scalar_labels(goal, types);
    show(goal, &mut 64, &labels, types)
}

fn scalar_labels(goal: &Formula, types: &BTreeMap<String, Ty>) -> BTreeMap<String, String> {
    let mut used = BTreeMap::<String, BTreeSet<String>>::new();
    let mut pending = vec![goal];
    for _ in 0..64 {
        let Some(goal) = pending.pop() else { break };
        let mut row = |row: &Linear| {
            for name in row.terms.keys().take(12) {
                if let Some(ty) = types.get(name) {
                    let syntax = match ty {
                        Ty::Machine(integer) => crate::syntax::Type::Machine(*integer),
                        Ty::Int => crate::syntax::Type::Int,
                        Ty::Nat => crate::syntax::Type::Nat,
                        Ty::Bool => crate::syntax::Type::Bool,
                        _ => continue,
                    };
                    let expression = crate::syntax::Expr {
                        kind: crate::syntax::Kind::Type(syntax),
                        line: 0,
                    };
                    used.entry(crate::syntax::display::expression(&expression))
                        .or_default()
                        .insert(name.clone());
                }
            }
        };
        match goal {
            Formula::Ge(value) => row(value),
            Formula::Predicate { arguments, .. } => arguments.iter().take(12).for_each(row),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                pending.push(b);
                pending.push(a);
            }
            Formula::Not(value) => pending.push(value),
            Formula::Forall { domain, body, .. } => {
                pending.push(body);
                pending.push(domain);
            }
            Formula::True | Formula::False => {}
        }
    }
    let mut labels = BTreeMap::new();
    for (ty, names) in used {
        let multiple = names.len() > 1;
        for (index, name) in names.into_iter().enumerate() {
            let label = if multiple {
                format!("unknown {ty} #{}", index + 1)
            } else {
                format!("unknown {ty}")
            };
            labels.insert(name, label);
        }
    }
    labels
}

fn show(
    goal: &Formula,
    budget: &mut usize,
    labels: &BTreeMap<String, String>,
    types: &BTreeMap<String, Ty>,
) -> String {
    if *budget == 0 {
        return "…".into();
    }
    *budget -= 1;
    match goal {
        Formula::True => "true".into(),
        Formula::False => "false".into(),
        Formula::Ge(row) => inequality(row, labels, types),
        Formula::Predicate { symbol, arguments } => format!(
            "{symbol}({})",
            arguments
                .iter()
                .take(12)
                .map(|row| linear(row, labels))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Formula::And(_, _) if equality_row(goal).is_some() => {
            format!("{} == 0", linear(equality_row(goal).unwrap(), labels))
        }
        Formula::And(a, b) => format!(
            "({} && {})",
            show(a, budget, labels, types),
            show(b, budget, labels, types)
        ),
        Formula::Or(a, b) => format!(
            "({} || {})",
            show(a, budget, labels, types),
            show(b, budget, labels, types)
        ),
        Formula::Not(value) if equality_row(value).is_some() => {
            format!("{} != 0", linear(equality_row(value).unwrap(), labels))
        }
        Formula::Not(value) => format!("!({})", show(value, budget, labels, types)),
        Formula::Implies(a, b) => format!(
            "({} => {})",
            show(a, budget, labels, types),
            show(b, budget, labels, types)
        ),
        Formula::Forall {
            variable,
            domain,
            body,
        } => format!(
            "forall({variable}) where {} {{{}}}",
            show(domain, budget, labels, types),
            show(body, budget, labels, types)
        ),
    }
}

fn inequality(
    row: &Linear,
    labels: &BTreeMap<String, String>,
    types: &BTreeMap<String, Ty>,
) -> String {
    if row.terms.len() == 1 {
        let (name, coefficient) = row.terms.first_key_value().unwrap();
        let label = labels.get(name).unwrap_or(name);
        if *coefficient == -1 {
            if let Some(Ty::Machine(integer)) = types.get(name) {
                let (_, maximum) = integer.bounds();
                if row.constant.checked_add(1) == Some(maximum) {
                    let constant = crate::syntax::Expr {
                        kind: crate::syntax::Kind::Constant(*integer, maximum),
                        line: 0,
                    };
                    return format!(
                        "{label} < {}",
                        crate::syntax::display::expression(&constant)
                    );
                }
            }
            return format!("{label} <= {}", row.constant);
        }
        if *coefficient == 1 {
            if let Some(bound) = row.constant.checked_neg() {
                return format!("{label} >= {bound}");
            }
        }
    }
    format!("{} >= 0", linear(row, labels))
}

// Equality is encoded by opposite inequalities in the arithmetic kernel.
// Reconstruct its spelling only for diagnostics; proof terms stay unchanged.
fn equality_row(goal: &Formula) -> Option<&Linear> {
    let Formula::And(a, b) = goal else {
        return None;
    };
    let (Formula::Ge(a), Formula::Ge(b)) = (&**a, &**b) else {
        return None;
    };
    (a.constant.checked_neg() == Some(b.constant)
        && a.terms.len() == b.terms.len()
        && a.terms
            .iter()
            .zip(&b.terms)
            .all(|((av, ac), (bv, bc))| av == bv && ac.checked_neg() == Some(*bc)))
    .then_some(a)
}

fn linear(row: &Linear, labels: &BTreeMap<String, String>) -> String {
    let mut out = String::new();
    for (variable, coefficient) in row.terms.iter().take(12) {
        if *coefficient == 0 {
            continue;
        }
        if out.is_empty() {
            if *coefficient < 0 {
                out.push('-');
            }
        } else {
            out.push_str(if *coefficient < 0 { " - " } else { " + " });
        }
        let magnitude = coefficient.unsigned_abs();
        if magnitude != 1 {
            out.push_str(&format!("{magnitude} * "));
        }
        out.push_str(labels.get(variable).unwrap_or(variable));
    }
    if row.terms.len() > 12 {
        out.push_str(" + …");
    }
    if row.constant != 0 || out.is_empty() {
        if out.is_empty() {
            out.push_str(&row.constant.to_string());
        } else {
            out.push_str(if row.constant < 0 { " - " } else { " + " });
            out.push_str(&row.constant.unsigned_abs().to_string());
        }
    }
    out
}

impl super::Context<'_> {
    pub(super) fn requirement_error(
        &mut self,
        error: String,
        expression: &crate::syntax::Expr,
        origin: crate::shared::diagnostics::SourceOrigin,
        kind: &'static str,
    ) -> String {
        self.session
            .note_source_obligation(&error, crate::syntax::display::expression(expression));
        self.session.note_requirement(
            &error,
            crate::shared::diagnostics::Requirement {
                kind,
                text: crate::syntax::display::expression(expression),
                origin,
                line: expression.line,
            },
        );
        error
    }
}

#[cfg(test)]
mod tests;
