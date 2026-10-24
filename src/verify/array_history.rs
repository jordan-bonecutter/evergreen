//! Immutable array versions preserve cells first observed after a store or join.
use super::*;

impl Context<'_> {
    pub(super) fn read_projection_value(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
    ) -> Result<Symbol> {
        let root = self.memory.read(reference)?;
        self.charge_value_work(symbol_weight(project(root, path)?)?)?;
        let root = self.memory.read(reference)?;
        let value = project(root, path)?.clone();
        if let Some((Projection::Index(index), prefix)) = path.split_last() {
            if let Symbol::Array {
                element, identity, ..
            } = project(root, prefix)?
            {
                if matches!(
                    **element,
                    Ty::Machine(_) | Ty::Bool | Ty::Unit | Ty::Int | Ty::Nat
                ) {
                    let element = (**element).clone();
                    let identity = identity.clone();
                    let key = (identity.clone(), index.clone());
                    if let Some(existing) = self.array_reads.get(&key).cloned() {
                        if existing != value {
                            self.assume(&self.symbol_equal(&existing, &value)?)?;
                        }
                    } else {
                        self.array_reads.insert(key, value);
                    }
                    return self.array_read(&element, &identity, index);
                }
            }
        }
        Ok(value)
    }

    pub(super) fn replay_array_history(
        &mut self,
        element: &Ty,
        identity: &str,
        index: &Linear,
        value: &Symbol,
    ) -> Result<()> {
        let Some(history) = self.array_history.get(identity) else {
            return Ok(());
        };
        let cost = match history {
            ArrayHistory::Store { index, value, .. } => {
                index.terms.len().saturating_add(symbol_weight(value)?)
            }
            ArrayHistory::Choice { condition, .. } => {
                symbol_weight(&Symbol::Bool(condition.clone()))?
            }
        };
        self.charge_value_work(cost)?;
        let history = self
            .array_history
            .get(identity)
            .cloned()
            .ok_or("array history disappeared")?;
        match history {
            ArrayHistory::Store {
                base,
                index: target,
                value: stored,
            } => {
                let previous = self.array_read(element, &base, index)?;
                let aliases = equal(index, &target)?;
                let relation = aliases
                    .clone()
                    .and(self.symbol_equal(value, &stored)?)
                    .or(aliases.not().and(self.symbol_equal(value, &previous)?));
                self.assume(&relation)
            }
            ArrayHistory::Choice {
                condition,
                left,
                right,
            } => {
                // Branch-born cache values are only meaningful in that branch.
                // Read each predecessor under its guard, never unconditionally.
                let cost = self
                    .paths
                    .iter()
                    .flatten()
                    .fold(0usize, |sum, row| sum.saturating_add(row.terms.len() + 1));
                self.charge_value_work(cost)?;
                let base = self.paths.clone();
                let checked = (|| {
                    self.paths =
                        extend(&base, &condition, false, self.session, &mut self.value_work)?;
                    let a = self.array_read(element, &left, index)?;
                    self.assume(&self.symbol_equal(value, &a)?)?;
                    let mut paths = std::mem::take(&mut self.paths);
                    self.paths =
                        extend(&base, &condition, true, self.session, &mut self.value_work)?;
                    let b = self.array_read(element, &right, index)?;
                    self.assume(&self.symbol_equal(value, &b)?)?;
                    paths.append(&mut self.paths);
                    self.feasible_paths(paths)
                })();
                self.paths = base;
                self.paths = paths::bounded(checked?, self.session, &mut self.value_work)?;
                Ok(())
            }
        }
    }
}
