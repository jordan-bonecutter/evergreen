//! Immutable read dependencies and saved scalar values used by proof queries.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::compiler::verify) enum ClaimKey {
    Type(Ty),
    Unit,
    Number(i128),
    Bool(bool),
    Read(Stamp),
    Entry(state::WorldId, String),
    OldRead(state::WorldId, Stamp),
    SavedScalar(state::WorldId, Option<Stamp>, Scalar),
    Unary(String, Box<Self>),
    Binary(String, Box<Self>, Box<Self>),
    Array(Vec<Self>),
    Record(String, Vec<(String, Self)>),
    Guarded(Vec<(Formula, Self)>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::compiler::verify) enum Scalar {
    Number(Linear),
    Bool(Formula),
    Unit,
}

impl Scalar {
    fn variables(&self) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        let mut pending = Vec::new();
        match self {
            Self::Number(n) => names.extend(n.terms.keys().cloned()),
            Self::Bool(p) => pending.push(p),
            Self::Unit => {}
        }
        while let Some(p) = pending.pop() {
            match p {
                Formula::Ge(n) => names.extend(n.terms.keys().cloned()),
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                Formula::Not(p) => pending.push(p),
                _ => {}
            }
        }
        names
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::compiler::verify) struct Snapshot {
    pub(in crate::compiler::verify) reads: BTreeSet<Stamp>,
    pub(in crate::compiler::verify) past: BTreeMap<state::WorldId, BTreeSet<Stamp>>,
    pub(in crate::compiler::verify) values: BTreeMap<state::WorldId, BTreeSet<String>>,
    pub(in crate::compiler::verify) complete: bool,
    pub(in crate::compiler::verify) key: Option<ClaimKey>,
}

impl Snapshot {
    pub(in crate::compiler::verify) fn guarded_reads(
        &self,
        live_only: bool,
    ) -> Result<(bool, Vec<(Stamp, Formula)>)> {
        let mut guarded = false;
        let mut reads: BTreeMap<Stamp, Formula> = BTreeMap::new();
        let mut pending = self
            .key
            .iter()
            .map(|key| (key, Formula::True))
            .collect::<Vec<_>>();
        let mut work = 0usize;
        while let Some((key, guard)) = pending.pop() {
            work = work.saturating_add(1 + guard.storage_weight()?);
            if work > MAX_VALUE_WORK {
                return Err("guarded proof read work limit reached".into());
            };
            match key {
                ClaimKey::Read(stamp) => {
                    let prior = reads.entry(*stamp).or_insert(Formula::False);
                    *prior = prior.clone().or(guard);
                }
                ClaimKey::OldRead(_, stamp) | ClaimKey::SavedScalar(_, Some(stamp), _)
                    if !live_only =>
                {
                    let prior = reads.entry(*stamp).or_insert(Formula::False);
                    *prior = prior.clone().or(guard);
                }
                ClaimKey::Guarded(cases) => {
                    guarded = true;
                    pending.extend(
                        cases
                            .iter()
                            .map(|(condition, key)| (key, guard.clone().and(condition.clone()))),
                    );
                }
                ClaimKey::Unary(_, key) => pending.push((key, guard)),
                ClaimKey::Binary(_, a, b) => {
                    pending.push((a, guard.clone()));
                    pending.push((b, guard));
                }
                ClaimKey::Array(values) => {
                    pending.extend(values.iter().map(|key| (key, guard.clone())))
                }
                ClaimKey::Record(_, fields) => {
                    pending.extend(fields.iter().map(|(_, key)| (key, guard.clone())))
                }
                _ => {}
            }
        }
        Ok((guarded, reads.into_iter().collect()))
    }

    pub(in crate::compiler::verify) fn from_key(key: ClaimKey) -> Self {
        let mut reads = BTreeSet::new();
        let mut past: BTreeMap<state::WorldId, BTreeSet<Stamp>> = BTreeMap::new();
        let mut values: BTreeMap<state::WorldId, BTreeSet<String>> = BTreeMap::new();
        let mut pending = vec![&key];
        while let Some(key) = pending.pop() {
            match key {
                ClaimKey::Read(stamp) => {
                    reads.insert(*stamp);
                }
                ClaimKey::OldRead(world, stamp) => {
                    past.entry(*world).or_default().insert(*stamp);
                }
                ClaimKey::SavedScalar(world, source, scalar) => {
                    past.entry(*world).or_default().extend(source);
                    values.entry(*world).or_default().extend(scalar.variables());
                }
                ClaimKey::Unary(_, value) => pending.push(value),
                ClaimKey::Binary(_, a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                ClaimKey::Array(values) => pending.extend(values.iter()),
                ClaimKey::Record(_, fields) => pending.extend(fields.iter().map(|(_, key)| key)),
                ClaimKey::Guarded(cases) => pending.extend(cases.iter().map(|(_, key)| key)),
                _ => {}
            }
        }
        Self {
            reads,
            past,
            values,
            complete: true,
            key: Some(key),
        }
    }

    pub(in crate::compiler::verify) fn storage_weight(&self) -> Result<usize> {
        let mut weight = self.reads.len()
            + self
                .past
                .values()
                .map(|reads| reads.len() + 1)
                .sum::<usize>()
            + self
                .values
                .values()
                .map(|names| names.len() + 1)
                .sum::<usize>();
        let mut pending = self.key.iter().collect::<Vec<_>>();
        while let Some(key) = pending.pop() {
            weight = weight.saturating_add(1);
            match key {
                ClaimKey::Type(ty) => {
                    weight =
                        weight.saturating_add(symbol_weight(&Symbol::Shape(Box::new(ty.clone())))?)
                }
                ClaimKey::Unary(_, key) => pending.push(key),
                ClaimKey::Binary(_, a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                ClaimKey::Array(keys) => pending.extend(keys),
                ClaimKey::Record(_, fields) => pending.extend(fields.iter().map(|(_, key)| key)),
                ClaimKey::Guarded(cases) => {
                    for (guard, key) in cases {
                        weight = weight.saturating_add(guard.storage_weight()?);
                        pending.push(key);
                    }
                }
                ClaimKey::SavedScalar(_, _, Scalar::Number(n)) => {
                    weight = weight.saturating_add(n.terms.len())
                }
                ClaimKey::SavedScalar(_, _, Scalar::Bool(p)) => {
                    weight = weight.saturating_add(p.storage_weight()?)
                }
                _ => {}
            }
            if weight > MAX_VALUE_WORK {
                return Err("proof subject storage limit reached".into());
            }
        }
        Ok(weight)
    }

    pub(in crate::compiler::verify) fn saved_scalar(
        world: state::WorldId,
        source: Option<&Self>,
        value: &Symbol,
    ) -> Option<Self> {
        let scalar = match value {
            Symbol::Number(_, n) => Scalar::Number(n.clone()),
            Symbol::Bool(p) => Scalar::Bool(p.clone()),
            Symbol::Unit => Scalar::Unit,
            _ => return None,
        };
        let stamp = source.and_then(|s| match s.key {
            Some(ClaimKey::Read(stamp)) => Some(stamp),
            _ => None,
        });
        Some(Self::from_key(ClaimKey::SavedScalar(world, stamp, scalar)))
    }

    pub(in crate::compiler::verify) fn old_at(&self, world: state::WorldId) -> Self {
        fn freeze(key: &mut ClaimKey, world: state::WorldId) {
            match key {
                ClaimKey::Read(stamp) => *key = ClaimKey::OldRead(world, *stamp),
                ClaimKey::Unary(_, key) => freeze(key, world),
                ClaimKey::Binary(_, a, b) => {
                    freeze(a, world);
                    freeze(b, world);
                }
                ClaimKey::Array(keys) => {
                    for key in keys {
                        freeze(key, world);
                    }
                }
                ClaimKey::Record(_, fields) => {
                    for (_, key) in fields {
                        freeze(key, world);
                    }
                }
                ClaimKey::Guarded(cases) => {
                    for (_, key) in cases {
                        freeze(key, world);
                    }
                }
                _ => {}
            }
        }
        let Some(mut key) = self.key.clone() else {
            return Self::default();
        };
        freeze(&mut key, world);
        Self::from_key(key)
    }

    pub(in crate::compiler::verify) fn replace_read(
        &mut self,
        original: &Self,
        replacement: &Self,
    ) {
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
                ClaimKey::Guarded(cases) => {
                    for (_, key) in cases {
                        replace(key, original, replacement);
                    }
                }
                _ => {}
            }
        }
        replace(key, *original, replacement);
        *self = Self::from_key(key.clone());
    }

    pub(in crate::compiler::verify) fn branch(&self, operator: &str, right: bool) -> Option<Self> {
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
