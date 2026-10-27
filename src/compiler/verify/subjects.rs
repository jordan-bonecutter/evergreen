//! State subjects are separate from simplified arithmetic. A snapshot names
//! actual plane projections and their content epochs, never source spellings.

use super::*;

const MAX_SUBJECTS: usize = 16_384;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Stamp {
    subject: usize,
    epoch: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ClaimKey {
    Unit,
    Number(i128),
    Bool(bool),
    Read(Stamp),
    Unary(String, Box<Self>),
    Binary(String, Box<Self>, Box<Self>),
    Array(Vec<Self>),
    Record(String, Vec<(String, Self)>),
}

#[derive(Clone, Debug, Default)]
pub(super) struct Snapshot {
    pub(super) reads: BTreeSet<Stamp>,
    pub(super) complete: bool,
    pub(super) key: Option<ClaimKey>,
}

impl Snapshot {
    pub(super) fn from_key(key: ClaimKey) -> Self {
        let mut reads = BTreeSet::new();
        let mut pending = vec![&key];
        while let Some(key) = pending.pop() {
            match key {
                ClaimKey::Read(stamp) => {
                    reads.insert(*stamp);
                }
                ClaimKey::Unary(_, value) => pending.push(value),
                ClaimKey::Binary(_, a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                ClaimKey::Array(values) => pending.extend(values.iter()),
                ClaimKey::Record(_, fields) => pending.extend(fields.iter().map(|(_, key)| key)),
                _ => {}
            }
        }
        Self {
            reads,
            complete: true,
            key: Some(key),
        }
    }

    pub(super) fn replace_read(&mut self, original: &Self, replacement: &Self) {
        let (Some(ClaimKey::Read(original)), Some(replacement), Some(key)) =
            (&original.key, &replacement.key, &mut self.key)
        else {
            return;
        };
        fn replace(key: &mut ClaimKey, original: Stamp, replacement: &ClaimKey) {
            match key {
                ClaimKey::Read(stamp) if *stamp == original => *key = replacement.clone(),
                ClaimKey::Unary(_, key) => replace(key, original, replacement),
                ClaimKey::Binary(_, a, b) => {
                    replace(a, original, replacement);
                    replace(b, original, replacement);
                }
                ClaimKey::Array(values) => {
                    for key in values {
                        replace(key, original, replacement);
                    }
                }
                ClaimKey::Record(_, fields) => {
                    for (_, key) in fields {
                        replace(key, original, replacement);
                    }
                }
                _ => {}
            }
        }
        replace(key, *original, replacement);
        *self = Self::from_key(key.clone());
    }

    pub(super) fn branch(&self, operator: &str, right: bool) -> Option<Self> {
        if let Some(ClaimKey::Binary(op, a, b)) = &self.key {
            if op != operator {
                return None;
            }
            Some(Self::from_key(if right {
                (**b).clone()
            } else {
                (**a).clone()
            }))
        } else {
            None
        }
    }
}

#[derive(Debug)]
struct Subject {
    plane: PlaneId,
    reference: Reference,
    path: Vec<Projection<Linear>>,
    epoch: u64,
}

#[derive(Debug, Default)]
pub(super) struct Subjects {
    places: BTreeMap<PlaneId, Vec<usize>>,
    entries: Vec<Subject>,
    clock: u64,
}

impl Subjects {
    fn cost(&self, plane: PlaneId) -> usize {
        self.places.get(&plane).map_or(1, |entries| {
            entries.iter().fold(1usize, |cost, &id| {
                cost.saturating_add(1 + self.entries[id].path.len())
            })
        })
    }

    pub(super) fn observe(
        &mut self,
        memory: &Memory<Symbol>,
        reference: Reference,
        path: Vec<Projection<Linear>>,
    ) -> Result<Stamp> {
        let plane = memory.plane(reference)?;
        let entries = self.places.entry(plane).or_default();
        if let Some(&subject) = entries.iter().find(|&&id| {
            let entry = &self.entries[id];
            entry.reference == reference && entry.path == path
        }) {
            return Ok(Stamp {
                subject,
                epoch: self.entries[subject].epoch,
            });
        }
        if self.entries.len() >= MAX_SUBJECTS {
            return Err("proof state subject limit reached".into());
        }
        let subject = self.entries.len();
        entries.push(subject);
        self.entries.push(Subject {
            plane,
            reference,
            path,
            epoch: self.clock,
        });
        Ok(Stamp {
            subject,
            epoch: self.clock,
        })
    }

    /// Epochs never rewind when symbolic memory is restored for another branch.
    /// A write on either branch conservatively invalidates affected old claims.
    pub(super) fn write(&mut self, plane: PlaneId, path: &[Projection<Linear>]) -> Result<()> {
        self.clock = self
            .clock
            .checked_add(1)
            .ok_or("proof state epoch exhausted")?;
        if let Some(entries) = self.places.get(&plane) {
            for &id in entries {
                let subject = &mut self.entries[id];
                if overlap(&subject.path, path) {
                    subject.epoch = self.clock;
                }
            }
        }
        Ok(())
    }

    pub(super) fn current(&self, snapshot: &Snapshot, memory: &Memory<Symbol>) -> bool {
        snapshot.complete
            && snapshot.reads.iter().all(|stamp| {
                self.entries.get(stamp.subject).is_some_and(|subject| {
                    subject.epoch == stamp.epoch
                        && memory.plane(subject.reference).ok() == Some(subject.plane)
                })
            })
    }
}

fn overlap(a: &[Projection<Linear>], b: &[Projection<Linear>]) -> bool {
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
    pub(super) fn note_state_write(
        &mut self,
        plane: PlaneId,
        path: &[Projection<Linear>],
    ) -> Result<()> {
        self.charge_value_work(self.proof.subjects.cost(plane).saturating_add(path.len()))?;
        self.proof.subjects.write(plane, path)
    }

    pub(super) fn allocate_symbol(&mut self, value: Symbol) -> Result<PlaneId> {
        let plane = self.storage.memory.allocate(value)?;
        // Branch memory snapshots may reuse a slot. Allocating there cannot
        // revive a stamp for a different allocation in an earlier branch.
        self.note_state_write(plane, &[])?;
        Ok(plane)
    }

    pub(super) fn take_symbol(&mut self, plane: PlaneId) -> Result<Symbol> {
        self.note_state_write(plane, &[])?;
        self.storage.memory.take(plane)
    }
}

impl Context<'_> {
    pub(super) fn claim_subjects(&mut self, expression: &Expr) -> Result<Snapshot> {
        let mut snapshot = Snapshot::default();
        snapshot.key = self.collect_subjects(expression, &mut snapshot, 0)?;
        snapshot.complete = snapshot.key.is_some();
        Ok(snapshot)
    }

    fn collect_subjects(
        &mut self,
        expression: &Expr,
        snapshot: &mut Snapshot,
        depth: usize,
    ) -> Result<Option<ClaimKey>> {
        self.charge_value_work(1)?;
        if depth >= 32 {
            return Ok(None);
        }
        let key = match &expression.kind {
            Kind::Name(name) if !self.locals.values.contains_key(name) => {
                if let Some(fact) = self.proof.facts.get(name).cloned() {
                    return self.collect_subjects(&fact, snapshot, depth + 1);
                }
                None
            }
            Kind::Name(_) | Kind::Field(..) | Kind::Index(..) => {
                return self.collect_place_subject(expression, snapshot, depth + 1);
            }
            Kind::Unary(op, place) if op == "&" => self
                .collect_place_subject(place, snapshot, depth + 1)?
                .map(|key| ClaimKey::Unary(op.clone(), Box::new(key))),
            Kind::Unary(op, _) if op == "*" => {
                return self.collect_place_subject(expression, snapshot, depth + 1);
            }
            Kind::Binary(op, a, b) => {
                let a = self.collect_subjects(a, snapshot, depth + 1)?;
                let b = self.collect_subjects(b, snapshot, depth + 1)?;
                a.zip(b)
                    .map(|(a, b)| ClaimKey::Binary(op.clone(), Box::new(a), Box::new(b)))
            }
            Kind::Unary(op, value) => self
                .collect_subjects(value, snapshot, depth + 1)?
                .map(|key| ClaimKey::Unary(op.clone(), Box::new(key))),
            Kind::Array(items) => {
                let mut keys = Vec::new();
                let mut complete = true;
                for item in items {
                    if let Some(key) = self.collect_subjects(item, snapshot, depth + 1)? {
                        keys.push(key);
                    } else {
                        complete = false;
                    }
                }
                complete.then_some(ClaimKey::Array(keys))
            }
            Kind::Record(name, fields) => {
                let mut keys = Vec::new();
                let mut complete = true;
                for (field, value) in fields {
                    if let Some(key) = self.collect_subjects(value, snapshot, depth + 1)? {
                        keys.push((field.clone(), key));
                    } else {
                        complete = false;
                    }
                }
                complete.then_some(ClaimKey::Record(name.clone(), keys))
            }
            Kind::Call(_, arguments) => {
                // Call-result subjects need value-flow provenance through
                // parameter renaming. Never re-evaluate a call to discover it.
                for argument in arguments {
                    self.collect_subjects(argument, snapshot, depth + 1)?;
                }
                None
            }
            Kind::If(condition, _, _) | Kind::FactAt(condition, _) => {
                self.collect_subjects(condition, snapshot, depth + 1)?;
                None
            }
            Kind::Unit => Some(ClaimKey::Unit),
            Kind::Number(n) | Kind::Constant(_, n) => Some(ClaimKey::Number(*n)),
            Kind::Bool(b) => Some(ClaimKey::Bool(*b)),
        };
        Ok(key)
    }

    fn collect_place_subject(
        &mut self,
        expression: &Expr,
        snapshot: &mut Snapshot,
        depth: usize,
    ) -> Result<Option<ClaimKey>> {
        if let Some((reference, path)) = self.subject_place(expression, depth)? {
            let plane = self.storage.memory.plane(reference)?;
            self.charge_value_work(self.proof.subjects.cost(plane).saturating_add(path.len()))?;
            let stamp = self
                .proof
                .subjects
                .observe(&self.storage.memory, reference, path)?;
            snapshot.reads.insert(stamp);
            Ok(Some(ClaimKey::Read(stamp)))
        } else {
            Ok(None)
        }
    }

    /// Resolve only existing storage and simple index values. This deliberately
    /// does not call `eval`, user functions, or expression elaboration twice.
    fn subject_place(
        &mut self,
        expression: &Expr,
        depth: usize,
    ) -> Result<Option<(Reference, Vec<Projection<Linear>>)>> {
        self.charge_value_work(1)?;
        if depth >= 32 {
            return Ok(None);
        }
        match &expression.kind {
            Kind::Name(name) => {
                let plane = if let Some(&plane) = self.locals.places.get(name) {
                    plane
                } else if let Some(value) = self.locals.values.get(name).cloned() {
                    let plane = self.allocate_symbol(value)?;
                    self.locals.places.insert(name.clone(), plane);
                    plane
                } else {
                    return Ok(None);
                };
                Ok(self
                    .storage
                    .memory
                    .borrow(plane)
                    .ok()
                    .map(|reference| (reference, vec![])))
            }
            Kind::Field(base, field) => {
                let Some((reference, mut path)) = self.subject_place(base, depth + 1)? else {
                    return Ok(None);
                };
                path.push(Projection::Field(field.clone()));
                Ok(Some((reference, path)))
            }
            Kind::Index(base, index) => {
                let Some((reference, mut path)) = self.subject_place(base, depth + 1)? else {
                    return Ok(None);
                };
                let index = match &index.kind {
                    Kind::Number(n) | Kind::Constant(_, n) => Some(Linear::number(*n)),
                    Kind::Name(name) => {
                        let value = self
                            .locals
                            .places
                            .get(name)
                            .and_then(|&id| self.storage.memory.get(id).ok())
                            .or_else(|| self.locals.values.get(name));
                        match value {
                            Some(Symbol::Number(_, number)) => Some(number.clone()),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let Some(index) = index else {
                    return Ok(None);
                };
                path.push(Projection::Index(index));
                Ok(Some((reference, path)))
            }
            Kind::Unary(op, base) if op == "*" => {
                let Some((reference, path)) = self.subject_place(base, depth + 1)? else {
                    return Ok(None);
                };
                match self
                    .storage
                    .memory
                    .read(reference)
                    .ok()
                    .and_then(|value| project(value, &path).ok())
                {
                    Some(Symbol::Ref(_, reference, path)) => Ok(Some((*reference, path.clone()))),
                    Some(Symbol::Plane(_, reference)) => Ok(Some((*reference, vec![]))),
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests;
