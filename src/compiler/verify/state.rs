//! Immutable per-plane proof state. Snapshot cloning shares every unchanged
//! trie node; writes replace only the affected plane and region entries.

use super::*;
mod persistent;
use persistent::Map;

#[derive(Clone, Debug, Default)]
struct PlaneState {
    version: u64,
    regions: Map<u64>,
    evidence: Map<evidence::NodeId>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct State {
    planes: Map<PlaneState>,
    ambient: Map<evidence::NodeId>,
}

impl State {
    pub(super) fn region(&self, plane: PlaneId, subject: usize) -> u64 {
        self.planes.get(plane.state_key()).map_or(0, |state| {
            state
                .regions
                .get(subject as u128)
                .copied()
                .unwrap_or(state.version)
        })
    }

    pub(super) fn observe(&self, plane: PlaneId, subject: usize) -> Self {
        let mut next = self.clone();
        let mut state = self
            .planes
            .get(plane.state_key())
            .cloned()
            .unwrap_or_default();
        if state.regions.get(subject as u128).is_none() {
            state.regions = state.regions.insert(subject as u128, state.version);
            next.planes = self.planes.insert(plane.state_key(), state);
        }
        next
    }

    pub(super) fn write(&self, plane: PlaneId, version: u64, regions: &[(usize, bool)]) -> Self {
        let mut next = self.clone();
        let mut state = self
            .planes
            .get(plane.state_key())
            .cloned()
            .unwrap_or_default();
        for &(id, changed) in regions {
            let prior = state
                .regions
                .get(id as u128)
                .copied()
                .unwrap_or(state.version);
            let selected = if changed { version } else { prior };
            if state.regions.get(id as u128) != Some(&selected) {
                state.regions = state.regions.insert(id as u128, selected);
            }
        }
        state.version = version;
        next.planes = self.planes.insert(plane.state_key(), state);
        next
    }

    pub(super) fn merge(
        &self,
        left: &Self,
        right: &Self,
        version: u64,
        regions: &BTreeMap<PlaneId, Vec<usize>>,
    ) -> Self {
        let mut next = self.clone();
        let mut keys = self.planes.changed_keys(&left.planes);
        keys.extend(self.planes.changed_keys(&right.planes));
        let by_key = regions
            .iter()
            .map(|(plane, ids)| (plane.state_key(), ids))
            .collect::<BTreeMap<_, _>>();
        for key in keys {
            let base = self.planes.get(key).cloned().unwrap_or_default();
            let a = left.planes.get(key).cloned().unwrap_or_default();
            let b = right.planes.get(key).cloned().unwrap_or_default();
            if a.version == base.version && b.version == base.version {
                continue;
            }
            let mut joined = base.clone();
            joined.version = version;
            if let Some(ids) = by_key.get(&key) {
                for &id in ids.iter() {
                    let a = a.regions.get(id as u128).copied().unwrap_or(a.version);
                    let b = b.regions.get(id as u128).copied().unwrap_or(b.version);
                    joined.regions = joined
                        .regions
                        .insert(id as u128, if a == b { a } else { version });
                }
            }
            // Branch-local claims need an explicit join proof. Existing facts
            // remain candidates, validated lazily against their dependencies.
            next.planes = next.planes.insert(key, joined);
        }
        next
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
}
