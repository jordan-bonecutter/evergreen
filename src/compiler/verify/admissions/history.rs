//! Demand-driven lookup in saved states and branch predecessors. A frame from
//! an unchanged branch is usable only under that branch's condition.

use super::*;

fn frame_guard(a: &Formula, b: &Formula) -> Formula {
    let mut pending = vec![a, b];
    let mut conditions = BTreeSet::new();
    while let Some(condition) = pending.pop() {
        match condition {
            Formula::False => return Formula::False,
            Formula::True => {}
            Formula::And(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            condition => {
                conditions.insert(condition.clone());
            }
        }
    }
    conditions.into_iter().fold(Formula::True, Formula::and)
}

pub(in crate::compiler::verify) struct RecursiveContext {
    node: evidence::NodeId,
    snapshot: subjects::Snapshot,
    guard: Formula,
}

#[derive(Clone, Default, PartialEq, Eq)]
struct Seeds {
    reads: BTreeSet<subjects::Stamp>,
    values: BTreeSet<String>,
}

#[derive(Default)]
pub(super) struct Demand {
    requests: BTreeMap<(state::WorldId, Formula), Seeds>,
}

impl Demand {
    pub(super) fn from_subjects(subjects: Option<&subjects::Snapshot>) -> Self {
        let mut demand = Self::default();
        if let Some(subjects) = subjects {
            demand.extend(subjects);
        }
        demand
    }

    pub(super) fn extend(&mut self, snapshot: &subjects::Snapshot) {
        self.extend_under(snapshot, &Formula::True);
    }

    pub(super) fn extend_under(&mut self, snapshot: &subjects::Snapshot, guard: &Formula) {
        for (world, reads) in &snapshot.past {
            self.requests
                .entry((*world, guard.clone()))
                .or_default()
                .reads
                .extend(reads);
        }
        for (world, names) in &snapshot.values {
            self.requests
                .entry((*world, guard.clone()))
                .or_default()
                .values
                .extend(names.iter().cloned());
        }
    }

    fn frame(
        &mut self,
        subjects: &mut subjects::Subjects,
        stamp: subjects::Stamp,
        guard: &Formula,
    ) -> Result<()> {
        if let Some((world, previous, condition)) = subjects.joined_predecessor(stamp)? {
            let guard = guard.clone().and(condition);
            if !matches!(guard, Formula::False) {
                self.requests
                    .entry((world, guard))
                    .or_default()
                    .reads
                    .insert(previous);
            }
        }
        Ok(())
    }

    fn weight(&self) -> Result<usize> {
        self.requests
            .iter()
            .try_fold(0usize, |weight, ((_, guard), seeds)| {
                Ok(weight
                    .saturating_add(guard.storage_weight()?)
                    .saturating_add(seeds.reads.len())
                    .saturating_add(seeds.values.len()))
            })
    }
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn record_recursive_context(
        &mut self,
        node: evidence::NodeId,
        snapshot: subjects::Snapshot,
    ) -> Result<()> {
        if self
            .evidence_dependencies(node)?
            .pending_summaries
            .is_empty()
        {
            return Ok(());
        }
        let guard = self.proof.control.as_ref().unwrap_or(&Formula::True);
        let cost = snapshot
            .storage_weight()?
            .saturating_add(guard.storage_weight()?);
        self.charge_value_work(cost)?;
        self.proof.recursive_contexts.push(RecursiveContext {
            node,
            snapshot,
            guard: self.proof.control.clone().unwrap_or(Formula::True),
        });
        Ok(())
    }

    pub(super) fn recursive_demands(
        &mut self,
        demand: &mut Demand,
        variables: &BTreeSet<String>,
    ) -> Result<()> {
        if self.proof.recursive_contexts.is_empty() {
            return Ok(());
        }
        let mut connected = variables.clone();
        let mut origins = BTreeSet::new();
        loop {
            let before = connected.len();
            for path in self.proof.paths.iter() {
                for (index, row) in path.iter().enumerate() {
                    self.work.value_work = self.work.value_work.saturating_add(row.terms.len() + 1);
                    if self.work.value_work > MAX_VALUE_WORK {
                        return Err("recursive proof dependency work limit reached".into());
                    }
                    if row.terms.keys().any(|name| connected.contains(name)) {
                        connected.extend(row.terms.keys().cloned());
                        if let paths::Origin::Evidence(node) = path.origin(index) {
                            origins.insert(node);
                        }
                    }
                }
            }
            if connected.len() == before {
                break;
            }
        }
        for source in &self.proof.recursive_contexts {
            if origins.contains(&source.node) {
                demand.extend_under(&source.snapshot, &source.guard);
            }
        }
        Ok(())
    }

    pub(super) fn follow_history(
        &mut self,
        mut demand: Demand,
        subjects: Option<&subjects::Snapshot>,
    ) -> Result<Vec<evidence::NodeId>> {
        let mut relevant = Vec::new();
        if let Some(goal) = subjects {
            for stamp in &goal.reads {
                demand.frame(&mut self.proof.subjects, *stamp, &Formula::True)?;
            }
        }
        let mut seen = BTreeSet::new();
        loop {
            self.charge_value_work(demand.weight()?)?;
            let before = demand.requests.clone();
            for ((_, guard), seeds) in &before {
                for stamp in &seeds.reads {
                    demand.frame(&mut self.proof.subjects, *stamp, guard)?;
                }
            }
            for ((world, guard), seeds) in &before {
                let (candidates, work) = self.proof.subjects.historical_candidates(*world)?;
                self.charge_value_work(work)?;
                let candidates = candidates
                    .intersection(&self.proof.claims)
                    .copied()
                    .collect::<Vec<_>>();
                for node in candidates {
                    if seen.contains(&(*world, guard.clone(), node)) {
                        continue;
                    }
                    let Some(snapshot) = self.proof.evidence.subjects(node).cloned() else {
                        continue;
                    };
                    let variables = self
                        .proof
                        .evidence
                        .claim(node)?
                        .variables(&mut self.work.value_work)?;
                    let same_revision = !snapshot.reads.is_disjoint(&seeds.reads)
                        || snapshot
                            .past
                            .values()
                            .any(|reads| !reads.is_disjoint(&seeds.reads));
                    let has_live_value = !snapshot.reads.is_empty() || snapshot.past.is_empty();
                    let related_value = has_live_value && !seeds.values.is_disjoint(&variables);
                    if !same_revision && !related_value {
                        continue;
                    }
                    let available = self.proof.subjects.availability(
                        &snapshot,
                        &self.storage.memory,
                        Some(*world),
                    )?;
                    if available == Formula::False {
                        continue;
                    }
                    seen.insert((*world, guard.clone(), node));
                    let scope = self
                        .reference_claim_scope(&snapshot, subjects)?
                        .and(available);
                    let effective = frame_guard(guard, &scope);
                    relevant.push(self.proof.evidence.guard(node, &effective)?);
                    demand
                        .requests
                        .entry((*world, effective.clone()))
                        .or_default()
                        .values
                        .extend(variables);
                    demand.extend_under(&snapshot, &effective);
                }
            }
            if demand.requests == before {
                break;
            }
        }
        Ok(relevant)
    }
}
