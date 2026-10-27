//! Immutable per-plane proof state. Snapshot cloning shares every unchanged
//! trie node. Writes record revisions; projection versions are queried lazily.

use super::*;
mod lazy;
pub(super) use lazy::{CaseId, History, Revision};
mod persistent;
use persistent::Map;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct WorldId(pub(super) usize);

#[derive(Clone, Debug, Default)]
struct PlaneState {
    version: Revision,
    evidence: Map<evidence::NodeId>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct State {
    planes: Map<PlaneState>,
    ambient: Map<evidence::NodeId>,
}

impl State {
    pub(super) fn version(&self, plane: PlaneId) -> Revision {
        self.planes
            .get(plane.state_key())
            .map_or(Revision::default(), |state| state.version)
    }

    pub(super) fn write(&self, plane: PlaneId, version: Revision) -> Self {
        let mut next = self.clone();
        let mut state = self
            .planes
            .get(plane.state_key())
            .cloned()
            .unwrap_or_default();
        state.version = version;
        next.planes = self.planes.insert(plane.state_key(), state);
        next
    }

    pub(super) fn merge(
        &self,
        left: &Self,
        right: &Self,
        history: &mut History,
        branch: CaseId,
    ) -> Result<Self> {
        let mut next = self.clone();
        let mut keys = self.planes.changed_keys(&left.planes);
        keys.extend(self.planes.changed_keys(&right.planes));
        for key in keys {
            let base = self.planes.get(key).cloned().unwrap_or_default();
            let a = left.planes.get(key).cloned().unwrap_or_default();
            let b = right.planes.get(key).cloned().unwrap_or_default();
            if a.version == base.version && b.version == base.version {
                continue;
            }
            let mut joined = base;
            joined.version = history.join(a.version, b.version, branch)?;
            // Branch-local evidence still requires a join proof. Projection
            // versions are computed only if a later obligation requests them.
            next.planes = next.planes.insert(key, joined);
        }
        Ok(next)
    }

    pub(super) fn publish(&self, proof: evidence::NodeId, planes: &BTreeSet<PlaneId>) -> Self {
        let mut next = self.clone();
        if planes.is_empty() {
            next.ambient = self.ambient.insert(proof.key(), proof);
        }
        for &plane in planes {
            let mut state = next
                .planes
                .get(plane.state_key())
                .cloned()
                .unwrap_or_default();
            state.evidence = state.evidence.insert(proof.key(), proof);
            next.planes = next.planes.insert(plane.state_key(), state);
        }
        next
    }

    pub(super) fn candidates(&self, planes: &BTreeSet<PlaneId>) -> BTreeSet<evidence::NodeId> {
        let mut facts = self
            .ambient
            .iter()
            .map(|(_, &proof)| proof)
            .collect::<BTreeSet<_>>();
        for &plane in planes {
            if let Some(state) = self.planes.get(plane.state_key()) {
                facts.extend(state.evidence.iter().map(|(_, &proof)| proof));
            }
        }
        facts
    }

    pub(super) fn all_candidates(&self) -> Result<(BTreeSet<evidence::NodeId>, usize)> {
        let mut facts = BTreeSet::new();
        let mut work = 0usize;
        for (_, &proof) in self.ambient.iter() {
            work += 1;
            facts.insert(proof);
        }
        for (_, state) in self.planes.iter() {
            work += 1;
            for (_, &proof) in state.evidence.iter() {
                work += 1;
                if work > MAX_VALUE_WORK {
                    return Err("historical proof index work limit reached".into());
                }
                facts.insert(proof);
            }
            if work > MAX_VALUE_WORK {
                return Err("historical proof index work limit reached".into());
            }
        }
        Ok((facts, work))
    }
}
