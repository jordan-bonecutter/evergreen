//! A loop head retains immutable plane facts and a bounded symbolic store.
//! Restoring it discards iteration-local equalities and lexical witnesses.

use super::*;

pub(super) struct Head {
    pub(super) memory: Memory<Symbol>,
    pub(super) control: Option<Formula>,
    state: state::State,
    env: BTreeMap<String, Symbol>,
    roots: BTreeMap<String, PlaneId>,
    paths: paths::Paths,
    claims: BTreeSet<evidence::NodeId>,
    values: Vec<evidence::NodeId>,
    ideal: BTreeSet<String>,
    results: usize,
    contexts: usize,
    censuses: BTreeMap<Reference, Linear>,
}

impl Head {
    pub(super) fn capture(ctx: &mut Context<'_>) -> Result<Self> {
        let mut cost = ctx.proof.paths.closed.parents.len();
        for path in ctx.proof.paths.iter() {
            for row in path.iter() {
                cost = cost.saturating_add(row.terms.len() + 1);
            }
        }
        cost = cost
            .saturating_add(ctx.proof.claims.len())
            .saturating_add(ctx.proof.value_claims.len())
            .saturating_add(ctx.locals.places.len())
            .saturating_add(ctx.locals.ideal_bindings.len());
        if let Some(control) = &ctx.proof.control {
            cost = cost.saturating_add(control.storage_weight()?);
        }
        ctx.charge_value_work(cost)?;
        Ok(Self {
            memory: ctx.snapshot_memory()?,
            state: ctx.proof.subjects.snapshot(),
            env: ctx.clone_env()?,
            roots: ctx.locals.places.clone(),
            paths: ctx.proof.paths.clone(),
            claims: ctx.proof.claims.clone(),
            values: ctx.proof.value_claims.clone(),
            ideal: ctx.locals.ideal_bindings.clone(),
            results: ctx.proof.results.len(),
            contexts: ctx.proof.recursive_contexts.len(),
            censuses: ctx.censuses.clone(),
            control: ctx.proof.control.clone(),
        })
    }

    pub(super) fn check_generations(&self, memory: &Memory<Symbol>, line: usize) -> Result<()> {
        let after = memory.states();
        for (index, (plane, generation, old)) in self.memory.states().into_iter().enumerate() {
            if old.is_some()
                && after.get(index).is_none_or(|(id, current, value)| {
                    *id != plane || *current != generation || value.is_none()
                })
            {
                return Err(format!("line {line}: loop iterations must preserve surrounding ownership and plane generations"));
            }
        }
        Ok(())
    }

    pub(super) fn restore(self, ctx: &mut Context<'_>) {
        ctx.censuses = self.censuses;
        ctx.storage.memory = self.memory;
        ctx.proof.subjects.restore(self.state);
        ctx.locals.values = self.env;
        ctx.locals.places = self.roots;
        ctx.locals.ideal_bindings = self.ideal;
        ctx.proof.paths = self.paths;
        ctx.proof.claims = self.claims;
        ctx.proof.value_claims = self.values;
        ctx.proof.results.truncate(self.results);
        ctx.proof.recursive_contexts.truncate(self.contexts);
        ctx.proof.control = self.control;
    }
}
