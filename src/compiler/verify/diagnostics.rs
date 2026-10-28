//! Bounded normalized obligations for failed proof diagnostics.

use super::{Formula, Linear};

pub(super) fn obligation(goal: &Formula) -> String {
    show(goal, &mut 64)
}

fn show(goal: &Formula, budget: &mut usize) -> String {
    if *budget == 0 {
        return "…".into();
    }
    *budget -= 1;
    match goal {
        Formula::True => "true".into(),
        Formula::False => "false".into(),
        Formula::Ge(row) => format!("{} >= 0", linear(row)),
        Formula::Predicate { symbol, arguments } => format!(
            "{symbol}({})",
            arguments
                .iter()
                .take(12)
                .map(linear)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Formula::And(a, b) => format!("({} && {})", show(a, budget), show(b, budget)),
        Formula::Or(a, b) => format!("({} || {})", show(a, budget), show(b, budget)),
        Formula::Not(value) => format!("!({})", show(value, budget)),
        Formula::Implies(a, b) => format!("({} => {})", show(a, budget), show(b, budget)),
        Formula::Forall {
            variable,
            domain,
            body,
        } => format!(
            "forall({variable}) where {} {{{}}}",
            show(domain, budget),
            show(body, budget)
        ),
    }
}

fn linear(row: &Linear) -> String {
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
        out.push_str(variable);
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
