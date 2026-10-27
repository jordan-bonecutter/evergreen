//! Append-only plane transitions and demand-driven projection versions.
//! Nodes contain arena IDs, so long histories neither copy predecessor states
//! nor recursively destroy linked allocations. Memoization never changes a node.

use super::*;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::compiler::verify) struct Revision(usize);

#[derive(Debug)]
enum Transition {
    Root,
    Write {
        prior: Revision,
        path: Vec<Projection<Linear>>,
    },
    Join {
        left: Revision,
        right: Revision,
        branch: CaseId,
    },
}

#[derive(Clone, Copy, Debug)]
pub(in crate::compiler::verify) struct CaseId(usize);

#[derive(Debug)]
struct Case {
    base: WorldId,
    condition: Arc<Formula>,
}

#[derive(Debug)]
pub(in crate::compiler::verify) struct History {
    nodes: Vec<Transition>,
    cases: Vec<Case>,
    cache: BTreeMap<(Revision, usize), Revision>,
    work: usize,
    storage: usize,
}

impl Default for History {
    fn default() -> Self {
        Self {
            nodes: vec![Transition::Root],
            cases: Vec::new(),
            cache: BTreeMap::new(),
            work: 0,
            storage: 1,
        }
    }
}

impl History {
    pub(in crate::compiler::verify) fn write(
        &mut self,
        prior: Revision,
        path: &[Projection<Linear>],
    ) -> Result<Revision> {
        self.insert(Transition::Write {
            prior,
            path: path.to_vec(),
        })
    }

    pub(in crate::compiler::verify) fn case(
        &mut self,
        base: WorldId,
        condition: &Formula,
    ) -> Result<CaseId> {
        let cost = condition.storage_weight()?.saturating_add(1);
        if cost > MAX_VALUE_WORK.saturating_sub(self.storage) {
            return Err("lazy proof case storage limit reached".into());
        }
        let id = CaseId(self.cases.len());
        self.cases.push(Case {
            base,
            condition: Arc::new(condition.clone()),
        });
        self.storage += cost;
        Ok(id)
    }

    pub(super) fn join(
        &mut self,
        left: Revision,
        right: Revision,
        branch: CaseId,
    ) -> Result<Revision> {
        if left == right {
            return Ok(left);
        }
        if self.cases.get(branch.0).is_none() {
            return Err("missing proof case".into());
        }
        self.insert(Transition::Join {
            left,
            right,
            branch,
        })
    }

    pub(in crate::compiler::verify) fn join_view(
        &self,
        revision: Revision,
    ) -> Option<(WorldId, Arc<Formula>, Revision, Revision)> {
        match self.nodes.get(revision.0)? {
            Transition::Join {
                left,
                right,
                branch,
            } => {
                let case = &self.cases[branch.0];
                Some((case.base, Arc::clone(&case.condition), *left, *right))
            }
            _ => None,
        }
    }

    fn insert(&mut self, transition: Transition) -> Result<Revision> {
        let (parents, cost) = match &transition {
            Transition::Root => return Err("duplicate proof history root".into()),
            Transition::Write { prior, path } => (vec![*prior], 1 + path.len()),
            Transition::Join { left, right, .. } => (vec![*left, *right], 1),
        };
        if parents.iter().any(|id| id.0 >= self.nodes.len()) {
            return Err("proof revision refers to a missing predecessor".into());
        }
        if cost > MAX_VALUE_WORK.saturating_sub(self.storage) {
            return Err("lazy proof transition limit reached".into());
        }
        let version = Revision(self.nodes.len());
        self.nodes.push(transition);
        self.storage += cost;
        Ok(version)
    }

    pub(in crate::compiler::verify) fn charge(&mut self, cost: usize) -> Result<()> {
        self.work = self.work.saturating_add(cost);
        if self.work > MAX_VALUE_WORK {
            return Err("lazy proof query work limit reached".into());
        }
        Ok(())
    }

    pub(in crate::compiler::verify) fn region(
        &mut self,
        root: Revision,
        subject: usize,
        path: &[Projection<Linear>],
    ) -> Result<Revision> {
        let mut pending = vec![(root, false)];
        while let Some((version, expanded)) = pending.pop() {
            if self.cache.contains_key(&(version, subject)) {
                continue;
            }
            self.charge(1)?;
            let transition = self
                .nodes
                .get(version.0)
                .ok_or("missing lazy proof transition")?;
            let value = match transition {
                Transition::Root => Some(Revision::default()),
                Transition::Write {
                    prior,
                    path: written,
                } => {
                    let prior = *prior;
                    let cost = path.len().min(written.len()).saturating_add(1);
                    let overlaps = subjects::overlap(path, written);
                    self.charge(cost)?;
                    if overlaps {
                        Some(version)
                    } else if expanded {
                        Some(self.cache[&(prior, subject)])
                    } else {
                        pending.push((version, true));
                        pending.push((prior, false));
                        None
                    }
                }
                Transition::Join { left, right, .. } => {
                    if expanded {
                        let a = self.cache[&(*left, subject)];
                        let b = self.cache[&(*right, subject)];
                        Some(if a == b { a } else { version })
                    } else {
                        pending.push((version, true));
                        pending.push((*right, false));
                        pending.push((*left, false));
                        None
                    }
                }
            };
            if let Some(value) = value {
                self.cache.insert((version, subject), value);
            }
        }
        Ok(self.cache[&(root, subject)])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn field(name: &str) -> Vec<Projection<Linear>> {
        vec![Projection::Field(name.into())]
    }

    #[test]
    fn writes_and_joins_are_dormant_until_the_requested_region_is_read() {
        let mut history = History::default();
        let base = history.write(Revision::default(), &[]).unwrap();
        let left = history.write(base, &field("left")).unwrap();
        let right = history.write(base, &field("right")).unwrap();
        let branch = history.case(WorldId::default(), &Formula::True).unwrap();
        let joined = history.join(left, right, branch).unwrap();
        assert!(history.cache.is_empty());
        assert_eq!(history.work, 0);
        assert_eq!(history.region(joined, 0, &field("left")).unwrap(), joined);
        assert!(history.cache.keys().all(|(_, subject)| *subject == 0));
        let work = history.work;
        assert_eq!(history.region(joined, 0, &field("left")).unwrap(), joined);
        assert_eq!(history.work, work);
        assert_eq!(
            history.region(joined, 1, &field("untouched")).unwrap(),
            base
        );
        assert_eq!(history.region(base, 0, &field("left")).unwrap(), base);
    }

    #[test]
    fn deep_histories_are_queried_and_destroyed_without_recursion() {
        let mut history = History::default();
        let mut root = Revision::default();
        for _ in 1..=20_000 {
            root = history.write(root, &field("other")).unwrap();
        }
        assert_eq!(
            history.region(root, 0, &field("requested")).unwrap(),
            Revision::default()
        );
        let work = history.work;
        assert_eq!(
            history.region(root, 0, &field("requested")).unwrap(),
            Revision::default()
        );
        assert_eq!(history.work, work);
    }
}
