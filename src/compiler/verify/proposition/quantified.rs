//! Scoped integer variables in propositions. Substitution rejects capture and
//! charges expansion before cloning a replacement into an arithmetic row.

use super::*;
use crate::compiler::verify::Result;
#[cfg(test)]
use crate::compiler::verify::MAX_VALUE_WORK;
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

    pub(in crate::compiler::verify) fn is_arithmetic(&self) -> bool {
        let mut pending = vec![self];
        while let Some(part) = pending.pop() {
            match part {
                Self::Forall { .. } | Self::Predicate { .. } => return false,
                Self::Not(p) => pending.push(p),
                Self::And(a, b) | Self::Or(a, b) | Self::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                _ => {}
            }
        }
        true
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
}
