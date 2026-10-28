//! Simultaneous, capture-rejecting substitution. Inserted terms are never
//! substituted again, even when they contain another parameter's name.

use super::*;
use crate::compiler::verify::{Result, MAX_VALUE_WORK};
use std::collections::BTreeMap;

type Bindings<'a> = BTreeMap<&'a str, &'a Linear>;

impl Formula {
    pub(in crate::compiler::verify) fn substitute(
        &self,
        variable: &str,
        value: &Linear,
    ) -> Result<Self> {
        self.substitute_all(&Bindings::from([(variable, value)]))
    }

    pub(in crate::compiler::verify) fn substitute_all(
        &self,
        bindings: &Bindings<'_>,
    ) -> Result<Self> {
        self.substitute_counted(bindings, &mut 0, MAX_VALUE_WORK)
    }

    pub(in crate::compiler::verify) fn substitute_counted(
        &self,
        bindings: &Bindings<'_>,
        work: &mut usize,
        limit: usize,
    ) -> Result<Self> {
        let limit = limit.min(work.saturating_add(MAX_VALUE_WORK));
        *work = work.saturating_add(self.storage_weight()?);
        if *work > limit {
            return Err("quantified substitution work limit reached".into());
        }
        replace(self, bindings, work, limit)
    }
}

fn row_cost(row: &Linear, bindings: &Bindings<'_>) -> usize {
    let mut terms = 1usize.saturating_add(row.terms.len());
    let mut replacements = 0usize;
    for name in row.terms.keys() {
        if let Some(value) = bindings.get(name.as_str()) {
            terms = terms.saturating_add(value.terms.len());
            replacements += 1;
        }
    }
    terms.saturating_mul(1 + replacements)
}

fn replace_row(row: &Linear, bindings: &Bindings<'_>) -> Result<Linear> {
    let mut out = row.clone();
    // Remove all original parameters before inserting any replacement terms.
    for name in row.terms.keys() {
        if bindings.contains_key(name.as_str()) {
            out.terms.remove(name);
        }
    }
    for (name, coefficient) in &row.terms {
        if let Some(value) = bindings.get(name.as_str()) {
            out = out.add(&value.scale(*coefficient)?)?;
        }
    }
    Ok(out)
}

fn replace(
    part: &Formula,
    bindings: &Bindings<'_>,
    work: &mut usize,
    limit: usize,
) -> Result<Formula> {
    let cost = if bindings.is_empty() {
        part.storage_weight()?
    } else {
        match part {
            Formula::Ge(row) => row_cost(row, bindings),
            Formula::Predicate { symbol, arguments } => arguments
                .iter()
                .fold(1usize.saturating_add(symbol.len()), |cost, row| {
                    cost.saturating_add(row_cost(row, bindings))
                }),
            Formula::Forall { variable, .. } => 1usize
                .saturating_add(variable.len())
                .saturating_add(bindings.len()),
            _ => 1,
        }
    };
    *work = work.saturating_add(cost);
    if *work > limit {
        return Err("quantified substitution work limit reached".into());
    }
    if bindings.is_empty() {
        return Ok(part.clone());
    }
    Ok(match part {
        Formula::Ge(row) => Formula::Ge(replace_row(row, bindings)?),
        Formula::Predicate { symbol, arguments } => Formula::Predicate {
            symbol: symbol.clone(),
            arguments: arguments
                .iter()
                .map(|row| replace_row(row, bindings))
                .collect::<Result<_>>()?,
        },
        Formula::Not(p) => Formula::Not(Box::new(replace(p, bindings, work, limit)?)),
        Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
            let a = Box::new(replace(a, bindings, work, limit)?);
            let b = Box::new(replace(b, bindings, work, limit)?);
            match part {
                Formula::And(..) => Formula::And(a, b),
                Formula::Or(..) => Formula::Or(a, b),
                _ => Formula::Implies(a, b),
            }
        }
        Formula::Forall {
            variable,
            domain,
            body,
        } => {
            let mut scoped;
            let bindings = if bindings.contains_key(variable.as_str()) {
                scoped = bindings.clone();
                scoped.remove(variable.as_str());
                &scoped
            } else {
                bindings
            };
            if bindings
                .values()
                .any(|value| value.terms.contains_key(variable))
            {
                return Err("quantified substitution would capture a free variable".into());
            }
            Formula::Forall {
                variable: variable.clone(),
                domain: Box::new(replace(domain, bindings, work, limit)?),
                body: Box::new(replace(body, bindings, work, limit)?),
            }
        }
        Formula::True | Formula::False => part.clone(),
    })
}
