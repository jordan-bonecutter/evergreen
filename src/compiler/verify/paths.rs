//! Bound paths after exact deduplication and certificate-checked pruning.

use super::*;

pub(super) fn bounded(
    paths: Vec<Vec<Linear>>,
    session: &mut Session,
    work: &mut usize,
) -> Result<Vec<Vec<Linear>>> {
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
            let mut key = path.iter().collect::<Vec<_>>();
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
        let first = vec![x.clone(), Linear::number(7), x.clone()];
        let mut duplicates = vec![first.clone(); 65];
        duplicates[1].reverse();
        let mut session = Session::recording();
        let mut work = 0;
        assert_eq!(
            bounded(duplicates, &mut session, &mut work).unwrap(),
            vec![first]
        );
        let mut paths = (1..=65)
            .map(|n| vec![Linear::number(-n)])
            .collect::<Vec<_>>();
        paths.push(vec![x.clone()]);
        assert_eq!(
            bounded(paths.clone(), &mut session, &mut work).unwrap(),
            vec![vec![x.clone()]]
        );
        let bundle = session.bundle("path pruning").unwrap();
        let mut replay = Session::replay(&bundle);
        assert_eq!(
            bounded(paths.clone(), &mut replay, &mut 0).unwrap(),
            vec![vec![x]]
        );
        replay.finish().unwrap();
        assert_eq!(replay.search_count(), 0);
        let text = bundle.to_text();
        assert!(text.contains(" 0:1"));
        let corrupted = ProofBundle::parse(&text.replacen(" 0:1", " 9:1", 1)).unwrap();
        assert!(bounded(paths, &mut Session::replay(&corrupted), &mut 0).is_err());
    }

    #[test]
    fn genuinely_distinct_feasible_paths_still_exceed_the_limit() {
        let x = Linear::variable("x");
        let paths = (0..65)
            .map(|n| {
                vec![
                    x.sub(&Linear::number(n)).unwrap(),
                    Linear::number(n).sub(&x).unwrap(),
                ]
            })
            .collect();
        let error = bounded(paths, &mut Session::search(), &mut 0).unwrap_err();
        assert!(error.contains("path limit"));
    }
}
