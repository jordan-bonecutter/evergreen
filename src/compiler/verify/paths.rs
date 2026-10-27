//! Bound paths after exact deduplication and certificate-checked pruning.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Origin {
    Unresolved,
    Evidence(evidence::NodeId),
    NegatedGoal,
}

/// Keep mathematical rows and origins in the same order. Mutation is private
/// so a certificate row index always addresses the corresponding origin.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Path {
    rows: Vec<Linear>,
    origins: Vec<Origin>,
}

impl Path {
    pub(super) fn push(&mut self, row: Linear, origin: Origin) {
        self.rows.push(row);
        self.origins.push(origin);
    }

    pub(super) fn origin(&self, index: usize) -> Origin {
        self.origins[index]
    }

    fn annotated(&self) -> impl Iterator<Item = (&Linear, Origin)> {
        self.rows.iter().zip(self.origins.iter().copied())
    }
}

impl From<Vec<Linear>> for Path {
    fn from(rows: Vec<Linear>) -> Self {
        let origins = vec![Origin::Unresolved; rows.len()];
        Self { rows, origins }
    }
}

impl std::ops::Deref for Path {
    type Target = [Linear];

    fn deref(&self) -> &Self::Target {
        &self.rows
    }
}

impl<'a> IntoIterator for &'a Path {
    type Item = &'a Linear;
    type IntoIter = std::slice::Iter<'a, Linear>;

    fn into_iter(self) -> Self::IntoIter {
        self.rows.iter()
    }
}

/// Each path is a conjunction of inequalities. The path list is a disjunction.
pub(super) fn extend(
    paths: &[Path],
    formula: &Formula,
    negated: bool,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Path>> {
    extend_from(paths, formula, negated, Origin::Unresolved, session, work)
}

pub(super) fn extend_from(
    paths: &[Path],
    formula: &Formula,
    negated: bool,
    origin: Origin,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Path>> {
    extend_normalized(paths, &formula.normalized(), negated, origin, session, work)
}

fn extend_normalized(
    paths: &[Path],
    formula: &Formula,
    negated: bool,
    origin: Origin,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Path>> {
    let result = match formula {
        Formula::True => {
            if negated {
                vec![]
            } else {
                paths.to_vec()
            }
        }
        Formula::False => {
            if negated {
                paths.to_vec()
            } else {
                vec![]
            }
        }
        Formula::Ge(value) => {
            let row = if negated {
                value.scale(-1)?.add(&Linear::number(-1))?
            } else {
                value.clone()
            };
            paths
                .iter()
                .map(|p| {
                    let mut p = p.clone();
                    p.push(row.clone(), origin);
                    p
                })
                .collect()
        }
        Formula::Not(p) => return extend_normalized(paths, p, !negated, origin, session, work),
        Formula::Implies(a, b) => {
            if negated {
                extend_normalized(
                    &extend_normalized(paths, a, false, origin, session, work)?,
                    b,
                    true,
                    origin,
                    session,
                    work,
                )?
            } else {
                let mut left = extend_normalized(paths, a, true, origin, session, work)?;
                left.extend(extend_normalized(paths, b, false, origin, session, work)?);
                left
            }
        }
        Formula::And(a, b) | Formula::Or(a, b) => {
            let conjunction = matches!(formula, Formula::And(..)) != negated;
            if conjunction {
                extend_normalized(
                    &extend_normalized(paths, a, negated, origin, session, work)?,
                    b,
                    negated,
                    origin,
                    session,
                    work,
                )?
            } else {
                let mut left = extend_normalized(paths, a, negated, origin, session, work)?;
                left.extend(extend_normalized(paths, b, negated, origin, session, work)?);
                left
            }
        }
    };
    bounded(result, session, work)
}

pub(super) fn bounded(
    paths: Vec<Path>,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Path>> {
    if paths.len() <= 64 {
        return Ok(paths);
    }
    // Compare borrowed rows, not deep copies of their coefficient maps. Work
    // is bounded before sorting or allocating keys for the overflow batch.
    let cost = paths.iter().flatten().fold(0usize, |cost, row| {
        cost.saturating_add(1usize.saturating_add(row.terms.len()))
    });
    *work = work.saturating_add(cost);
    if *work > MAX_VALUE_WORK {
        return Err("verification path deduplication work limit reached".into());
    }
    let mut keep = Vec::with_capacity(paths.len());
    {
        let mut seen = BTreeSet::new();
        for path in &paths {
            let mut key = path.annotated().collect::<Vec<_>>();
            key.sort_unstable();
            key.dedup();
            keep.push(seen.insert(key));
        }
    }
    let unique = paths
        .into_iter()
        .zip(keep)
        .filter_map(|(path, keep)| keep.then_some(path))
        .collect::<Vec<_>>();
    if unique.len() > 64 {
        let mut feasible = Vec::new();
        for path in unique {
            // The search result alone has no authority. Session checks every
            // supplied contradiction certificate and records it for replay.
            if !session.probe(&path)? {
                feasible.push(path);
                if feasible.len() > 64 {
                    return Err("verification path limit reached (64)".into());
                }
            }
        }
        return Ok(feasible);
    }
    // Retain the first path's original rows and order for certificates. No
    // inequality is removed and no possibly feasible alternative is forgotten.
    Ok(unique)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn path_pruning_preserves_models_and_replays_checked_certificates() {
        let x = Linear::variable("x");
        let first = Path::from(vec![x.clone(), Linear::number(7), x.clone()]);
        let mut duplicates = vec![first.clone(); 65];
        duplicates[1] = Path::from(first.iter().cloned().rev().collect::<Vec<_>>());
        let mut session = Session::recording();
        let mut work = 0;
        assert_eq!(
            bounded(duplicates, &mut session, &mut work).unwrap(),
            vec![first]
        );
        let mut paths = (1..=65)
            .map(|n| Path::from(vec![Linear::number(-n)]))
            .collect::<Vec<_>>();
        paths.push(Path::from(vec![x.clone()]));
        assert_eq!(
            bounded(paths.clone(), &mut session, &mut work).unwrap(),
            vec![Path::from(vec![x.clone()])]
        );
        let bundle = session.bundle("path pruning").unwrap();
        let mut replay = Session::replay(&bundle);
        assert_eq!(
            bounded(paths.clone(), &mut replay, &mut 0).unwrap(),
            vec![Path::from(vec![x])]
        );
        replay.finish().unwrap();
        assert_eq!(replay.search_count(), 0);
        let text = bundle.to_text();
        assert!(text.contains(" 0:1"));
        let corrupted = ProofBundle::parse(&text.replacen(" 0:1", " 9:1", 1)).unwrap();
        assert!(bounded(paths, &mut Session::replay(&corrupted), &mut 0).is_err());
    }

    #[test]
    fn equal_arithmetic_rows_do_not_merge_distinct_proof_origins() {
        let mut graph = evidence::Evidence::default();
        let claim = Formula::Ge(Linear::variable("x"));
        let a = graph.insert(claim.clone(), vec![], true).unwrap();
        let b = graph.insert(claim, vec![], true).unwrap();
        let mut first = Path::default();
        first.push(Linear::variable("x"), Origin::Evidence(a));
        let mut second = Path::default();
        second.push(Linear::variable("x"), Origin::Evidence(b));
        let mut paths = vec![first.clone(); 64];
        paths.push(second.clone());
        assert_eq!(
            bounded(paths, &mut Session::search(), &mut 0).unwrap(),
            vec![first, second]
        );
    }

    #[test]
    fn genuinely_distinct_feasible_paths_still_exceed_the_limit() {
        let x = Linear::variable("x");
        let paths = (0..65)
            .map(|n| {
                Path::from(vec![
                    x.sub(&Linear::number(n)).unwrap(),
                    Linear::number(n).sub(&x).unwrap(),
                ])
            })
            .collect();
        let error = bounded(paths, &mut Session::search(), &mut 0).unwrap_err();
        assert!(error.contains("path limit"));
    }
}
