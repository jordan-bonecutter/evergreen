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

/// Dependencies of checked contradictions and arithmetic derivations. Unknown
/// origins are explicit; an empty parent set alone does not mean independence.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Support {
    pub(super) parents: BTreeSet<evidence::NodeId>,
    pub(super) unresolved: bool,
    pub(super) context_variables: BTreeSet<String>,
}

impl Support {
    fn add_origin(&mut self, origin: Origin) {
        match origin {
            Origin::Evidence(node) => {
                self.parents.insert(node);
            }
            Origin::Unresolved => self.unresolved = true,
            Origin::NegatedGoal => {}
        }
    }

    pub(super) fn add_rows(&mut self, path: &Path, rows: &[usize]) {
        for &index in rows {
            self.add_origin(path.origin(index));
            if path.origin(index) == Origin::Unresolved {
                self.context_variables
                    .extend(path[index].terms.keys().cloned());
            }
        }
    }

    fn merge(&mut self, other: Self) {
        self.parents.extend(other.parents);
        self.unresolved |= other.unresolved;
        self.context_variables.extend(other.context_variables);
    }
}

/// A disjunction keeps the explanations for removed alternatives alongside its
/// live alternatives. An empty live list is not an unexplained proof of false.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Paths {
    live: Vec<Path>,
    pub(super) closed: Support,
}

impl Paths {
    pub(super) fn unit() -> Self {
        Self::from(vec![Path::default()])
    }

    pub(super) fn extend(&mut self, other: Self) {
        self.live.extend(other.live);
        self.closed.merge(other.closed);
    }

    pub(super) fn append(&mut self, other: &mut Self) {
        self.extend(std::mem::take(other));
    }
}

impl Default for Paths {
    fn default() -> Self {
        Self::from(Vec::new())
    }
}

impl From<Vec<Path>> for Paths {
    fn from(live: Vec<Path>) -> Self {
        // Empty paths supplied without an explanation must not appear to be a
        // checked contradiction. Known closures use an explicit Support.
        let closed = Support {
            unresolved: live.is_empty(),
            ..Support::default()
        };
        Self { live, closed }
    }
}

impl std::ops::Deref for Paths {
    type Target = [Path];
    fn deref(&self) -> &Self::Target {
        &self.live
    }
}

/// Each path is a conjunction of inequalities. The path set is a disjunction.
pub(super) fn extend(
    paths: &Paths,
    formula: &Formula,
    negated: bool,
    session: &mut Session,
    work: &mut usize,
) -> Result<Paths> {
    extend_from(paths, formula, negated, Origin::Unresolved, session, work)
}

pub(super) fn extend_from(
    paths: &Paths,
    formula: &Formula,
    negated: bool,
    origin: Origin,
    session: &mut Session,
    work: &mut usize,
) -> Result<Paths> {
    extend_normalized(paths, &formula.normalized(), negated, origin, session, work)
}

fn extend_normalized(
    paths: &Paths,
    formula: &Formula,
    negated: bool,
    origin: Origin,
    session: &mut Session,
    work: &mut usize,
) -> Result<Paths> {
    *work = work.saturating_add(paths.closed.parents.len());
    if *work > MAX_VALUE_WORK {
        return Err("verification path evidence work limit reached".into());
    }
    let result = match formula {
        Formula::True | Formula::False => {
            let contradiction = matches!(formula, Formula::False) != negated;
            if contradiction {
                // This formula alone closes every alternative. For a negated
                // goal, that is a tautology, not a dependency on the goal node.
                let mut closed = Support::default();
                closed.add_origin(origin);
                Paths {
                    live: vec![],
                    closed,
                }
            } else {
                paths.clone()
            }
        }
        Formula::Ge(value) => {
            let row = if negated {
                value.scale(-1)?.add(&Linear::number(-1))?
            } else {
                value.clone()
            };
            let mut result = paths.clone();
            for path in &mut result.live {
                path.push(row.clone(), origin);
            }
            result
        }
        Formula::Forall { .. } => {
            return Err(
                "quantified propositions require universal proof rules before arithmetic".into(),
            )
        }
        Formula::Predicate { .. } => {
            return Err("predicate atoms require logical proof rules before arithmetic".into())
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

pub(super) fn feasible(mut paths: Paths, session: &mut Session) -> Result<Paths> {
    if paths.len() <= 1 {
        return Ok(paths);
    }
    let mut live = Vec::new();
    for path in paths.live {
        match session.probe_with_support(&path)? {
            Some(support) => paths.closed.add_rows(&path, &support),
            None => live.push(path),
        }
    }
    paths.live = live;
    Ok(paths)
}

pub(super) fn bounded(paths: Paths, session: &mut Session, work: &mut usize) -> Result<Paths> {
    if paths.len() <= 64 {
        return Ok(paths);
    }
    // Compare borrowed rows and origins, retaining the first path's original
    // row order so certificate indices keep their meaning.
    let cost = paths
        .iter()
        .flatten()
        .fold(paths.closed.parents.len(), |cost, row| {
            cost.saturating_add(1usize.saturating_add(row.terms.len()))
        });
    *work = work.saturating_add(cost);
    if *work > MAX_VALUE_WORK {
        return Err("verification path deduplication work limit reached".into());
    }
    let mut keep = Vec::with_capacity(paths.len());
    {
        let mut seen = BTreeSet::new();
        for path in paths.iter() {
            let mut key = path.annotated().collect::<Vec<_>>();
            key.sort_unstable();
            key.dedup();
            keep.push(seen.insert(key));
        }
    }
    let live = paths
        .live
        .into_iter()
        .zip(keep)
        .filter_map(|(path, keep)| keep.then_some(path))
        .collect::<Vec<_>>();
    let mut unique = Paths {
        live,
        closed: paths.closed,
    };
    if unique.len() > 64 {
        let mut live = Vec::new();
        for path in unique.live {
            match session.probe_with_support(&path)? {
                Some(support) => unique.closed.add_rows(&path, &support),
                None => {
                    live.push(path);
                    if live.len() > 64 {
                        return Err("verification path limit reached (64)".into());
                    }
                }
            }
        }
        unique.live = live;
    }
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
            bounded(duplicates.into(), &mut session, &mut work)
                .unwrap()
                .live,
            vec![first]
        );
        let mut paths = (1..=65)
            .map(|n| Path::from(vec![Linear::number(-n)]))
            .collect::<Vec<_>>();
        paths.push(Path::from(vec![x.clone()]));
        assert_eq!(
            bounded(paths.clone().into(), &mut session, &mut work)
                .unwrap()
                .live,
            vec![Path::from(vec![x.clone()])]
        );
        let bundle = session.bundle("path pruning").unwrap();
        let mut replay = Session::replay(&bundle);
        assert_eq!(
            bounded(paths.clone().into(), &mut replay, &mut 0)
                .unwrap()
                .live,
            vec![Path::from(vec![x])]
        );
        replay.finish().unwrap();
        assert_eq!(replay.search_count(), 0);
        let text = bundle.to_text();
        assert!(text.contains(" 0:1"));
        let corrupted = ProofBundle::parse(&text.replacen(" 0:1", " 9:1", 1)).unwrap();
        assert!(bounded(paths.into(), &mut Session::replay(&corrupted), &mut 0).is_err());
    }

    #[test]
    fn removed_alternatives_keep_only_checked_contradiction_support_on_replay() {
        fn check(session: &mut Session) -> Support {
            let mut graph = evidence::Evidence::default();
            let used = graph.insert(Formula::False, vec![], true).unwrap();
            let unused = graph.insert(Formula::True, vec![], true).unwrap();
            let mut impossible = Path::default();
            impossible.push(Linear::number(-1), Origin::Evidence(used));
            impossible.push(Linear::variable("unrelated"), Origin::Evidence(unused));
            let mut live = Path::default();
            live.push(Linear::variable("live"), Origin::NegatedGoal);
            let result = feasible(Paths::from(vec![impossible, live.clone()]), session).unwrap();
            assert_eq!(result.live, vec![live]);
            assert_eq!(result.closed.parents, BTreeSet::from([used]));
            assert!(!result.closed.unresolved);
            result.closed
        }
        let mut recording = Session::recording();
        let expected = check(&mut recording);
        recording.finish().unwrap();
        let bundle = recording.bundle("pruning evidence").unwrap();
        let mut replay = Session::replay(&bundle);
        assert_eq!(check(&mut replay), expected);
        replay.finish().unwrap();
        assert_eq!(replay.search_count(), 0);
    }

    #[test]
    fn overflow_pruning_preserves_explanations_for_every_removed_path() {
        let mut graph = evidence::Evidence::default();
        let source = graph.insert(Formula::False, vec![], true).unwrap();
        let live = Path::from(vec![Linear::variable("live")]);
        let mut alternatives = (1..=65)
            .map(|n| {
                let mut path = Path::default();
                path.push(Linear::number(-n), Origin::Evidence(source));
                path
            })
            .collect::<Vec<_>>();
        alternatives.push(live.clone());
        let result = bounded(alternatives.into(), &mut Session::search(), &mut 0).unwrap();
        assert_eq!(result.live, vec![live]);
        assert_eq!(result.closed.parents, BTreeSet::from([source]));
        assert!(!result.closed.unresolved);
    }

    #[test]
    fn unexplained_empty_context_is_not_independent_evidence() {
        assert!(Paths::default().closed.unresolved);
        assert!(!Paths::unit().closed.unresolved);
    }

    #[test]
    fn pruning_unknown_origins_does_not_invent_complete_evidence() {
        let input = Paths::from(vec![Path::from(vec![Linear::number(-1)]), Path::default()]);
        let result = feasible(input, &mut Session::search()).unwrap();
        assert_eq!(result.live, vec![Path::default()]);
        assert!(result.closed.parents.is_empty());
        assert!(result.closed.unresolved);
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
            bounded(paths.into(), &mut Session::search(), &mut 0)
                .unwrap()
                .live,
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
            .collect::<Vec<_>>();
        let error = bounded(paths.into(), &mut Session::search(), &mut 0).unwrap_err();
        assert!(error.contains("path limit"));
    }
}
