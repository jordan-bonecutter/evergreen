//! Scoped integer variables in propositions. Substitution rejects capture and
//! charges expansion before cloning a replacement into an arithmetic row.

use super::*;
use crate::compiler::verify::{Result, MAX_VALUE_WORK};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
mod predicate_tests;
#[cfg(test)]
mod tests;

impl Formula {
    // Bound spellings carry no mathematical identity. Free names still do.
    pub(in crate::compiler::verify) fn alpha_equal(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        #[derive(PartialEq, Eq, PartialOrd, Ord)]
        enum Variable<'a> {
            Bound(usize),
            Free(&'a str),
        }
        fn terms<'a>(
            row: &'a Linear,
            scope: &[(&str, &str)],
            left: bool,
        ) -> BTreeMap<Variable<'a>, i128> {
            row.terms
                .iter()
                .map(|(name, coefficient)| {
                    let bound = scope
                        .iter()
                        .rev()
                        .position(|(a, b)| name == if left { a } else { b });
                    (
                        bound.map(Variable::Bound).unwrap_or(Variable::Free(name)),
                        *coefficient,
                    )
                })
                .collect()
        }
        enum Step<'a> {
            Pair(&'a Formula, &'a Formula),
            Leave,
        }
        let mut pending = vec![Step::Pair(self, other)];
        let mut scope = Vec::new();
        while let Some(step) = pending.pop() {
            let (a, b) = match step {
                Step::Pair(a, b) => (a, b),
                Step::Leave => {
                    scope.pop();
                    continue;
                }
            };
            match (a, b) {
                (Self::True, Self::True) | (Self::False, Self::False) => {}
                (Self::Ge(a), Self::Ge(b))
                    if a.constant == b.constant
                        && terms(a, &scope, true) == terms(b, &scope, false) => {}
                (
                    Self::Predicate {
                        symbol: a,
                        arguments: aa,
                    },
                    Self::Predicate {
                        symbol: b,
                        arguments: ba,
                    },
                ) if a == b
                    && aa.len() == ba.len()
                    && aa.iter().zip(ba).all(|(a, b)| {
                        a.constant == b.constant
                            && terms(a, &scope, true) == terms(b, &scope, false)
                    }) => {}
                (Self::Not(a), Self::Not(b)) => pending.push(Step::Pair(a, b)),
                (Self::And(a, b), Self::And(c, d))
                | (Self::Or(a, b), Self::Or(c, d))
                | (Self::Implies(a, b), Self::Implies(c, d)) => {
                    pending.push(Step::Pair(b, d));
                    pending.push(Step::Pair(a, c));
                }
                (
                    Self::Forall {
                        variable: a,
                        domain: ad,
                        body: ab,
                    },
                    Self::Forall {
                        variable: b,
                        domain: bd,
                        body: bb,
                    },
                ) => {
                    scope.push((a.as_str(), b.as_str()));
                    pending.push(Step::Leave);
                    pending.push(Step::Pair(ab, bb));
                    pending.push(Step::Pair(ad, bd));
                }
                _ => return false,
            }
        }
        true
    }
    pub(in crate::compiler::verify) fn contains_quantifier(&self) -> bool {
        let mut pending = vec![self];
        while let Some(part) = pending.pop() {
            match part {
                Self::Forall { .. } => return true,
                Self::Not(p) => pending.push(p),
                Self::And(a, b) | Self::Or(a, b) | Self::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                _ => {}
            }
        }
        false
    }
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
                Formula::Predicate { arguments, .. } => {
                    for argument in arguments {
                        variables.extend(
                            argument
                                .terms
                                .keys()
                                .filter(|name| !bound.contains_key(name.as_str()))
                                .cloned(),
                        );
                    }
                }
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
                Formula::Predicate { symbol, arguments } => {
                    arguments
                        .iter()
                        .fold(1usize.saturating_add(symbol.len()), |cost, row| {
                            cost.saturating_add(1 + row.terms.len()).saturating_add(
                                if row.terms.contains_key(variable) {
                                    value.terms.len()
                                } else {
                                    0
                                },
                            )
                        })
                }
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
                Formula::Ge(row) => Formula::Ge(substitute_row(row, variable, value)?),
                Formula::Predicate { symbol, arguments } => Formula::Predicate {
                    symbol: symbol.clone(),
                    arguments: arguments
                        .iter()
                        .map(|row| substitute_row(row, variable, value))
                        .collect::<Result<_>>()?,
                },
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

fn substitute_row(row: &Linear, variable: &str, value: &Linear) -> Result<Linear> {
    let mut row = row.clone();
    if let Some(coefficient) = row.terms.remove(variable) {
        row = row.add(&value.scale(coefficient)?)?;
    }
    Ok(row)
}
