//! Scoped integer variables in propositions. Substitution rejects capture and
//! charges expansion before cloning a replacement into an arithmetic row.

use super::*;
use crate::compiler::verify::{Result, MAX_VALUE_WORK};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
mod tests;

impl Formula {
    pub(in crate::compiler::verify) fn free_variables(&self) -> Result<BTreeSet<String>> {
        self.storage_weight()?;
        enum Step<'a> {
            Visit(&'a Formula),
            Leave(&'a str),
        }
        let mut pending = vec![Step::Visit(self)];
        let mut bound: BTreeMap<&str, usize> = BTreeMap::new();
        let mut variables = BTreeSet::new();
        while let Some(step) = pending.pop() {
            let part = match step {
                Step::Leave(name) => {
                    let count = bound.get_mut(name).ok_or("missing quantifier scope")?;
                    *count -= 1;
                    if *count == 0 {
                        bound.remove(name);
                    }
                    continue;
                }
                Step::Visit(part) => part,
            };
            match part {
                Formula::Ge(row) => variables.extend(
                    row.terms
                        .keys()
                        .filter(|name| !bound.contains_key(name.as_str()))
                        .cloned(),
                ),
                Formula::Not(p) => pending.push(Step::Visit(p)),
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    pending.push(Step::Visit(b));
                    pending.push(Step::Visit(a));
                }
                Formula::Forall {
                    variable,
                    domain,
                    body,
                } => {
                    *bound.entry(variable).or_default() += 1;
                    pending.push(Step::Leave(variable));
                    pending.push(Step::Visit(body));
                    pending.push(Step::Visit(domain));
                }
                Formula::True | Formula::False => {}
            }
        }
        Ok(variables)
    }

    pub(in crate::compiler::verify) fn substitute(
        &self,
        variable: &str,
        value: &Linear,
    ) -> Result<Self> {
        self.storage_weight()?;
        fn replace(
            part: &Formula,
            variable: &str,
            value: &Linear,
            work: &mut usize,
        ) -> Result<Formula> {
            let cost = match part {
                Formula::Ge(row) => 1usize.saturating_add(row.terms.len()).saturating_add(
                    if row.terms.contains_key(variable) {
                        value.terms.len()
                    } else {
                        0
                    },
                ),
                Formula::Forall {
                    variable: bound, ..
                } if bound == variable => part.storage_weight()?,
                _ => 1,
            };
            *work = work.saturating_add(cost);
            if *work > MAX_VALUE_WORK {
                return Err("quantified substitution work limit reached".into());
            }
            Ok(match part {
                Formula::Ge(row) => {
                    let mut row = row.clone();
                    if let Some(coefficient) = row.terms.remove(variable) {
                        row = row.add(&value.scale(coefficient)?)?;
                    }
                    Formula::Ge(row)
                }
                Formula::Not(p) => Formula::Not(Box::new(replace(p, variable, value, work)?)),
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    let a = Box::new(replace(a, variable, value, work)?);
                    let b = Box::new(replace(b, variable, value, work)?);
                    match part {
                        Formula::And(..) => Formula::And(a, b),
                        Formula::Or(..) => Formula::Or(a, b),
                        _ => Formula::Implies(a, b),
                    }
                }
                Formula::Forall {
                    variable: bound, ..
                } if bound == variable => part.clone(),
                Formula::Forall {
                    variable: bound,
                    domain,
                    body,
                } => {
                    if value.terms.contains_key(bound) {
                        return Err("quantified substitution would capture a free variable".into());
                    }
                    Formula::Forall {
                        variable: bound.clone(),
                        domain: Box::new(replace(domain, variable, value, work)?),
                        body: Box::new(replace(body, variable, value, work)?),
                    }
                }
                Formula::True | Formula::False => part.clone(),
            })
        }
        replace(self, variable, value, &mut 0)
    }
}
