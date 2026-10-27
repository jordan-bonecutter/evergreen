//! Small certificate checker for linear arithmetic over mathematical integers.
//!
//! Every constraint means `constant + sum(coeff * variable) >= 0`. A certificate
//! gives nonnegative integer weights for the original constraints whose sum is
//! a negative constant. The solver is separate; only `check` establishes validity.

use std::collections::BTreeMap;

pub type ArithmeticResult<T> = Result<T, String>;

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Linear {
    pub constant: i128,
    pub terms: BTreeMap<String, i128>,
}

impl Linear {
    pub fn number(constant: i128) -> Self {
        Self {
            constant,
            terms: BTreeMap::new(),
        }
    }

    pub fn variable(name: impl Into<String>) -> Self {
        Self {
            constant: 0,
            terms: BTreeMap::from([(name.into(), 1)]),
        }
    }

    pub fn add(&self, rhs: &Self) -> ArithmeticResult<Self> {
        let mut out = self.clone();
        out.constant = out
            .constant
            .checked_add(rhs.constant)
            .ok_or("proof arithmetic overflow")?;
        for (var, value) in &rhs.terms {
            let old = out.terms.get(var).copied().unwrap_or(0);
            let next = old.checked_add(*value).ok_or("proof arithmetic overflow")?;
            if next == 0 {
                out.terms.remove(var);
            } else {
                out.terms.insert(var.clone(), next);
            }
        }
        Ok(out)
    }

    pub fn scale(&self, factor: i128) -> ArithmeticResult<Self> {
        let mut out = Self::number(
            self.constant
                .checked_mul(factor)
                .ok_or("proof arithmetic overflow")?,
        );
        for (name, coeff) in &self.terms {
            let value = coeff
                .checked_mul(factor)
                .ok_or("proof arithmetic overflow")?;
            if value != 0 {
                out.terms.insert(name.clone(), value);
            }
        }
        Ok(out)
    }

    pub fn sub(&self, rhs: &Self) -> ArithmeticResult<Self> {
        self.add(&rhs.scale(-1)?)
    }
}

/// Sparse nonnegative weights. Private fields prevent bypassing constructors.
#[derive(Clone, Debug)]
pub struct Certificate {
    weights: BTreeMap<usize, i128>,
}

impl Certificate {
    pub(crate) fn weights(&self) -> impl Iterator<Item = (usize, i128)> + '_ {
        self.weights.iter().map(|(i, w)| (*i, *w))
    }

    pub(crate) fn from_weights(weights: BTreeMap<usize, i128>) -> ArithmeticResult<Self> {
        if weights.values().any(|w| *w <= 0) {
            return Err("certificate weights must be positive".into());
        }
        Ok(Self { weights })
    }
}

/// Check a contradiction certificate independently of the search algorithm.
pub fn check(assumptions: &[Linear], certificate: &Certificate) -> ArithmeticResult<()> {
    let mut sum = Linear::default();
    for (&index, &weight) in &certificate.weights {
        if weight < 0 {
            return Err("negative certificate weight".into());
        }
        let original = assumptions
            .get(index)
            .ok_or("certificate index out of range")?;
        sum = sum.add(&original.scale(weight)?)?;
    }
    if !sum.terms.is_empty() || sum.constant >= 0 {
        return Err("certificate does not establish a contradiction".into());
    }
    Ok(())
}

#[derive(Clone)]
struct Derived {
    value: Linear,
    certificate: Certificate,
}

impl Derived {
    fn combine(&self, a: i128, other: &Self, b: i128) -> ArithmeticResult<Self> {
        if a <= 0 || b <= 0 {
            return Err("invalid elimination weights".into());
        }
        let value = self.value.scale(a)?.add(&other.value.scale(b)?)?;
        let mut weights = BTreeMap::new();
        for (index, weight) in &self.certificate.weights {
            weights.insert(
                *index,
                weight.checked_mul(a).ok_or("proof arithmetic overflow")?,
            );
        }
        for (index, weight) in &other.certificate.weights {
            let old = weights.get(index).copied().unwrap_or(0_i128);
            weights.insert(
                *index,
                old.checked_add(weight.checked_mul(b).ok_or("proof arithmetic overflow")?)
                    .ok_or("proof arithmetic overflow")?,
            );
        }
        Ok(Self {
            value,
            certificate: Certificate { weights },
        })
    }
}

/// Bounded Fourier–Motzkin search. Incomplete for integers; failure is an error,
/// never evidence that a program is safe. All returned certificates are checked.
pub fn solve(assumptions: &[Linear]) -> ArithmeticResult<Certificate> {
    const MAX_CONSTRAINTS: usize = 2048;
    const MAX_VARIABLES: usize = 64;
    if assumptions.len() > MAX_CONSTRAINTS {
        return Err("proof search constraint limit reached".into());
    }
    let mut rows: Vec<Derived> = assumptions
        .iter()
        .enumerate()
        .map(|(i, value)| Derived {
            value: value.clone(),
            certificate: Certificate {
                weights: BTreeMap::from([(i, 1)]),
            },
        })
        .collect();
    for _ in 0..=MAX_VARIABLES {
        if let Some(row) = rows
            .iter()
            .find(|r| r.value.terms.is_empty() && r.value.constant < 0)
        {
            check(assumptions, &row.certificate)?;
            return Ok(row.certificate.clone());
        }
        // An equality lets us substitute once into every row, rather than
        // forming every positive/negative pair. Search remains untrusted:
        // the same independent checker validates the resulting certificate.
        let lookup: BTreeMap<Linear, usize> = rows
            .iter()
            .enumerate()
            .map(|(i, r)| (r.value.clone(), i))
            .collect();
        let mut equality = None;
        // New obligations are appended after the context. Prefer substitutions
        // touching the current last row so stale SSA equalities do not consume
        // the elimination budget before we reach the obligation itself.
        let focus = rows.last().map(|row| &row.value.terms);
        for (i, row) in rows.iter().enumerate().rev() {
            if let Some(variable) = row
                .value
                .terms
                .keys()
                .min_by_key(|name| !focus.is_some_and(|terms| terms.contains_key(*name)))
            {
                if let Some(&j) = lookup.get(&row.value.scale(-1)?) {
                    let relevant = focus.is_some_and(|terms| terms.contains_key(variable));
                    if equality.is_none() || relevant {
                        equality = Some((i, j, variable.clone()));
                    }
                    if relevant {
                        break;
                    }
                }
            }
        }
        if let Some((i, j, variable)) = equality {
            let (positive, negative) = if rows[i].value.terms[&variable] > 0 {
                (rows[i].clone(), rows[j].clone())
            } else {
                (rows[j].clone(), rows[i].clone())
            };
            let p = positive.value.terms[&variable];
            let n = negative.value.terms[&variable]
                .checked_neg()
                .ok_or("proof arithmetic overflow")?;
            let mut next = Vec::new();
            let mut seen = std::collections::BTreeSet::new();
            for row in rows {
                let coefficient = row.value.terms.get(&variable).copied().unwrap_or(0);
                let row = if coefficient > 0 {
                    row.combine(n, &negative, coefficient)?
                } else if coefficient < 0 {
                    row.combine(
                        p,
                        &positive,
                        coefficient
                            .checked_neg()
                            .ok_or("proof arithmetic overflow")?,
                    )?
                } else {
                    row
                };
                if seen.insert(row.value.clone()) {
                    next.push(row);
                }
            }
            rows = next;
            continue;
        }
        // Eliminate the cheapest variable to keep common bounds proofs small.
        let mut variables = BTreeMap::<String, (usize, usize)>::new();
        for row in &rows {
            for (name, coeff) in &row.value.terms {
                let entry = variables.entry(name.clone()).or_default();
                if *coeff > 0 {
                    entry.0 += 1;
                } else {
                    entry.1 += 1;
                }
            }
        }
        let Some((variable, _)) = variables
            .into_iter()
            .min_by_key(|(_, (p, n))| p.saturating_mul(*n))
        else {
            break;
        };
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        let mut next = Vec::new();
        for row in rows {
            match row.value.terms.get(&variable).copied().unwrap_or(0).cmp(&0) {
                std::cmp::Ordering::Greater => positive.push(row),
                std::cmp::Ordering::Less => negative.push(row),
                std::cmp::Ordering::Equal => next.push(row),
            }
        }
        if positive
            .len()
            .saturating_mul(negative.len())
            .saturating_add(next.len())
            > MAX_CONSTRAINTS
        {
            return Err("proof search constraint limit reached".into());
        }
        let mut seen: std::collections::BTreeSet<Linear> =
            next.iter().map(|r| r.value.clone()).collect();
        for p in &positive {
            for n in &negative {
                let a = n.value.terms[&variable]
                    .checked_neg()
                    .ok_or("proof arithmetic overflow")?;
                let b = p.value.terms[&variable];
                let derived = p.combine(a, n, b)?;
                if seen.insert(derived.value.clone()) {
                    next.push(derived);
                }
            }
        }
        rows = next;
    }
    Err("cannot prove obligation with bounded linear arithmetic; supply stronger facts or an explicit proof".into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stale_equalities_do_not_exhaust_the_obligation_budget() {
        let mut assumptions = Vec::new();
        for index in 0..100 {
            let stale = Linear::variable(format!("stale_{index}"));
            assumptions.push(stale.clone());
            assumptions.push(stale.scale(-1).unwrap());
        }
        let result = Linear::variable("result");
        let equality = result.sub(&Linear::number(42)).unwrap();
        assumptions.push(equality.clone());
        assumptions.push(equality.scale(-1).unwrap());
        assumptions.push(result.scale(-1).unwrap().add(&Linear::number(41)).unwrap());
        check(&assumptions, &solve(&assumptions).unwrap()).unwrap();
    }

    #[test]
    fn verifies_bounds_certificate() {
        // i >= 0, n - i - 1 >= 0, i - n >= 0 (negated bounds goal).
        let i = Linear::variable("i");
        let n = Linear::variable("n");
        let assumptions = vec![
            i.clone(),
            n.sub(&i).unwrap().add(&Linear::number(-1)).unwrap(),
            i.sub(&n).unwrap(),
        ];
        check(&assumptions, &solve(&assumptions).unwrap()).unwrap();
    }

    #[test]
    fn refuses_forged_certificates() {
        let assumptions = vec![Linear::number(1), Linear::variable("x")];
        for weights in [
            BTreeMap::new(),
            BTreeMap::from([(0, -1)]),
            BTreeMap::from([(2, 1)]),
            BTreeMap::from([(1, 1)]),
            BTreeMap::from([(0, 1)]),
        ] {
            assert!(check(&assumptions, &Certificate { weights }).is_err());
        }
    }

    #[test]
    fn overflow_fails_closed() {
        assert!(Linear::number(i128::MAX).add(&Linear::number(1)).is_err());
        assert!(Linear::number(i128::MIN).scale(-1).is_err());
        assert!(check(
            &[Linear::number(i128::MIN)],
            &Certificate {
                weights: BTreeMap::from([(0, 2)])
            }
        )
        .is_err());
    }

    #[test]
    fn satisfiable_constraints_are_not_proofs() {
        assert!(solve(&[
            Linear::variable("x"),
            Linear::number(10).sub(&Linear::variable("x")).unwrap()
        ])
        .is_err());
    }

    #[test]
    fn eliminates_multiple_variables() {
        let x = Linear::variable("x");
        let y = Linear::variable("y");
        let assumptions = vec![
            x.sub(&y).unwrap(),
            y.clone(),
            x.scale(-1).unwrap().add(&Linear::number(-1)).unwrap(),
        ];
        check(&assumptions, &solve(&assumptions).unwrap()).unwrap();
    }

    #[test]
    fn certificates_agree_with_small_exhaustive_integer_models() {
        // Exercise search and independent checking against a concrete oracle.
        // This is deliberately small and deterministic, not a resource stress test.
        let x = Linear::variable("x");
        for a in -2..=2_i128 {
            for b in -2..=2_i128 {
                for c in -2..=2_i128 {
                    let constraints = vec![
                        x.scale(a).unwrap().add(&Linear::number(b)).unwrap(),
                        x.scale(-1).unwrap().add(&Linear::number(c)).unwrap(),
                    ];
                    if let Ok(certificate) = solve(&constraints) {
                        check(&constraints, &certificate).unwrap();
                        for value in -5..=5_i128 {
                            assert!(!constraints.iter().all(|r| r.constant
                                + r.terms.get("x").copied().unwrap_or(0) * value
                                >= 0));
                        }
                    }
                }
            }
        }
    }
}
