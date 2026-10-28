//! State subjects are separate from simplified arithmetic. A snapshot names
//! actual plane projections and revisions; aliases share the same state entry.

use super::*;
use std::sync::Arc;

const MAX_SUBJECTS: usize = 16_384;
type SubjectPath = Arc<[Projection<Linear>]>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Stamp {
    subject: usize,
    revision: state::Revision,
}

mod branches;
mod snapshot;
pub(super) use snapshot::{ClaimKey, Snapshot};

#[derive(Debug)]
struct Subject {
    plane: PlaneId,
    reference: Reference,
    path: SubjectPath,
}

#[derive(Debug, Default)]
pub(super) struct Subjects {
    identities: BTreeMap<(Reference, SubjectPath), usize>,
    entries: Vec<Subject>,
    state: state::State,
    history: state::History,
    worlds: Vec<state::State>,
}

impl Subjects {
    pub(super) fn availability(
        &mut self,
        snapshot: &Snapshot,
        memory: &Memory<Symbol>,
        world: Option<state::WorldId>,
    ) -> Result<Formula> {
        if !snapshot.complete {
            return Ok(Formula::False);
        };
        let (guarded, reads) = snapshot.guarded_reads(true)?;
        if !guarded {
            let available = match world {
                Some(world) => self.historical(snapshot, world)?,
                None => self.current(snapshot, memory)?,
            };
            return Ok(if available {
                Formula::True
            } else {
                Formula::False
            });
        }
        let state = match world {
            Some(world) => self
                .worlds
                .get(world.0)
                .ok_or("missing guarded historical state")?,
            None => &self.state,
        };
        let mut available = Formula::True;
        for (stamp, guard) in reads {
            let subject = self
                .entries
                .get(stamp.subject)
                .ok_or("missing guarded read subject")?;
            let live =
                world.is_some() || memory.plane(subject.reference).ok() == Some(subject.plane);
            let revision =
                self.history
                    .region(state.version(subject.plane), stamp.subject, &subject.path)?;
            if !live || revision != stamp.revision {
                available = available.and(guard.not());
            }
        }
        Ok(available)
    }

    pub(super) fn same_read_region(&self, a: Stamp, b: Stamp) -> Result<Formula> {
        let a = self
            .entries
            .get(a.subject)
            .ok_or("unknown guarded proof subject")?;
        let b = self
            .entries
            .get(b.subject)
            .ok_or("unknown guarded proof subject")?;
        if a.reference != b.reference || a.path.len() != b.path.len() {
            return Ok(Formula::False);
        };
        let mut equal_path = Formula::True;
        for (a, b) in a.path.iter().zip(b.path.iter()) {
            equal_path = equal_path.and(match (a, b) {
                (Projection::Field(a), Projection::Field(b)) if a == b => Formula::True,
                (Projection::Index(a), Projection::Index(b)) => equal(a, b)?,
                (
                    Projection::Member {
                        index: a,
                        expected: at,
                    },
                    Projection::Member {
                        index: b,
                        expected: bt,
                    },
                ) if a == b && at == bt => Formula::True,
                _ => Formula::False,
            });
        }
        Ok(equal_path)
    }

    pub(super) fn observe(
        &mut self,
        memory: &Memory<Symbol>,
        reference: Reference,
        path: Vec<Projection<Linear>>,
    ) -> Result<Stamp> {
        let plane = memory.plane(reference)?;
        self.observe_in(&self.state.clone(), plane, reference, path)
    }

    fn observe_in(
        &mut self,
        state: &state::State,
        plane: PlaneId,
        reference: Reference,
        path: Vec<Projection<Linear>>,
    ) -> Result<Stamp> {
        let path = Arc::<[Projection<Linear>]>::from(path);
        let key = (reference, Arc::clone(&path));
        let cost =
            (path.len() + 1).saturating_mul((self.identities.len() + 1).ilog2() as usize + 1);
        self.history.charge(cost)?;
        let subject = if let Some(&id) = self.identities.get(&key) {
            id
        } else {
            if self.entries.len() >= MAX_SUBJECTS {
                return Err("proof state subject limit reached".into());
            }
            let id = self.entries.len();
            self.identities.insert(key, id);
            self.entries.push(Subject {
                plane,
                reference,
                path,
            });
            id
        };
        Ok(Stamp {
            subject,
            revision: self.history.region(
                state.version(plane),
                subject,
                &self.entries[subject].path,
            )?,
        })
    }

    pub(super) fn write(&mut self, plane: PlaneId, path: &[Projection<Linear>]) -> Result<()> {
        let prior = self.state.version(plane);
        let version = self.history.write(prior, path)?;
        self.state = self.state.write(plane, version);
        Ok(())
    }

    pub(super) fn save_world(&mut self) -> Result<state::WorldId> {
        if self.worlds.len() >= MAX_VALUE_WORK {
            return Err("historical proof state limit reached".into());
        }
        let id = state::WorldId(self.worlds.len());
        self.worlds.push(self.state.clone());
        Ok(id)
    }

    fn old_read(
        &mut self,
        world: state::WorldId,
        reference: Reference,
        path: Vec<Projection<Linear>>,
    ) -> Result<Stamp> {
        let state = self
            .worlds
            .get(world.0)
            .ok_or("missing historical proof state")?
            .clone();
        self.observe_in(&state, reference.plane_identity(), reference, path)
    }

    pub(super) fn historical(
        &mut self,
        snapshot: &Snapshot,
        world: state::WorldId,
    ) -> Result<bool> {
        if !snapshot.complete {
            return Ok(false);
        }
        let state = self
            .worlds
            .get(world.0)
            .ok_or("missing historical proof state")?;
        for stamp in &snapshot.reads {
            let Some(subject) = self.entries.get(stamp.subject) else {
                return Ok(false);
            };
            let revision =
                self.history
                    .region(state.version(subject.plane), stamp.subject, &subject.path)?;
            if revision != stamp.revision {
                return Ok(false);
            }
        }
        Ok(true)
    }

    pub(super) fn joined_predecessor(
        &mut self,
        stamp: Stamp,
    ) -> Result<Option<(state::WorldId, Stamp, Formula)>> {
        let Some((world, condition, left, right)) = self.history.join_view(stamp.revision) else {
            return Ok(None);
        };
        let state = self
            .worlds
            .get(world.0)
            .ok_or("missing branch predecessor proof state")?;
        let subject = self
            .entries
            .get(stamp.subject)
            .ok_or("missing proof projection")?;
        let revision =
            self.history
                .region(state.version(subject.plane), stamp.subject, &subject.path)?;
        let a = self.history.region(left, stamp.subject, &subject.path)?;
        let b = self.history.region(right, stamp.subject, &subject.path)?;
        let guard = match (a == revision, b == revision) {
            (true, true) => Formula::True,
            (true, false) => (*condition).clone(),
            (false, true) => (*condition).clone().not(),
            (false, false) => return Ok(None),
        };
        Ok(Some((
            world,
            Stamp {
                subject: stamp.subject,
                revision,
            },
            guard,
        )))
    }

    pub(super) fn historical_candidates(
        &self,
        world: state::WorldId,
    ) -> Result<(BTreeSet<evidence::NodeId>, usize)> {
        self.worlds
            .get(world.0)
            .ok_or("missing historical proof state")?
            .all_candidates()
    }

    pub(super) fn snapshot(&self) -> state::State {
        self.state.clone()
    }
    pub(super) fn restore(&mut self, state: state::State) {
        self.state = state;
    }

    pub(super) fn merge(
        &mut self,
        base: &state::State,
        a: &state::State,
        b: &state::State,
        condition: &Formula,
    ) -> Result<()> {
        if self.worlds.len() >= MAX_VALUE_WORK {
            return Err("historical proof state limit reached".into());
        }
        let world = state::WorldId(self.worlds.len());
        self.worlds.push(base.clone());
        let branch = self.history.case(world, condition)?;
        self.state = base.merge(a, b, &mut self.history, branch)?;
        Ok(())
    }

    pub(super) fn publish(&mut self, node: evidence::NodeId, snapshot: &Snapshot) {
        let planes = snapshot
            .reads
            .iter()
            .map(|stamp| self.entries[stamp.subject].plane)
            .collect();
        self.state = self.state.publish(node, &planes);
    }

    pub(super) fn candidates(&self, snapshot: &Snapshot) -> BTreeSet<evidence::NodeId> {
        let planes = snapshot
            .reads
            .iter()
            .map(|stamp| self.entries[stamp.subject].plane)
            .collect();
        self.state.candidates(&planes)
    }

    pub(super) fn current(&mut self, snapshot: &Snapshot, memory: &Memory<Symbol>) -> Result<bool> {
        if !snapshot.complete {
            return Ok(false);
        }
        for stamp in &snapshot.reads {
            let Some(subject) = self.entries.get(stamp.subject) else {
                return Ok(false);
            };
            if memory.plane(subject.reference).ok() != Some(subject.plane) {
                return Ok(false);
            }
            let revision = self.history.region(
                self.state.version(subject.plane),
                stamp.subject,
                &subject.path,
            )?;
            if revision != stamp.revision {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

pub(super) fn overlap(a: &[Projection<Linear>], b: &[Projection<Linear>]) -> bool {
    let a_owners = matches!(a.first(), Some(Projection::Owners));
    let b_owners = matches!(b.first(), Some(Projection::Owners));
    if a_owners || b_owners {
        return a_owners && b_owners;
    }
    for (a, b) in a.iter().zip(b) {
        match (a, b) {
            (Projection::Field(a), Projection::Field(b)) if a != b => return false,
            (Projection::Index(a), Projection::Index(b))
                if a.terms.is_empty() && b.terms.is_empty() && a != b =>
            {
                return false
            }
            _ => {}
        }
    }
    true
}

impl Context<'_> {
    pub(super) fn publish_evidence(
        &mut self,
        node: evidence::NodeId,
        snapshot: Snapshot,
    ) -> Result<()> {
        self.proof
            .evidence
            .record_subjects(node, snapshot.clone())?;
        self.proof.subjects.publish(node, &snapshot);
        Ok(())
    }

    pub(super) fn note_state_write(
        &mut self,
        plane: PlaneId,
        path: &[Projection<Linear>],
    ) -> Result<()> {
        self.charge_value_work(1usize.saturating_add(path.len()))?;
        self.check_loop_write(plane, path)?;
        // A union interpretation overlaps its entire slot. Preserve no field
        // fact across a write through any of that slot's member views.
        let path = path
            .iter()
            .position(|step| matches!(step, Projection::Member { .. }))
            .map_or(path, |index| &path[..index]);
        self.proof.subjects.write(plane, path)
    }

    pub(super) fn allocate_symbol(&mut self, value: Symbol) -> Result<PlaneId> {
        let plane = self.storage.memory.allocate(value)?;
        if self.execution.materializing_input {
            // This is an existing caller plane being observed for the first
            // time, not a source allocation or a change to its contents.
            self.record_input_presence(plane)?;
            return Ok(plane);
        }
        self.record_plane_presence(plane)?;
        // Each allocation gets a fresh identity, including across snapshots.
        self.note_state_write(plane, &[])?;
        Ok(plane)
    }

    pub(super) fn take_symbol(&mut self, plane: PlaneId) -> Result<Symbol> {
        self.note_state_write(plane, &[])?;
        self.storage.memory.take(plane)
    }
}

mod collect;
mod places;

#[cfg(test)]
mod tests;
