//! Immutable array versions preserve cells first observed after a store or join.

use super::*;

impl Context<'_> {
    pub(super) fn assume_history_type(&mut self, value: &Symbol, nominal: bool) -> Result<()> {
        // A derived version may be an intermediate state between summary
        // writes. Its nominal invariant is never an assumption, even when a
        // later read replays it after the call has completed.
        if !nominal {
            if let Symbol::Record(_, fields) = value {
                for field in fields.values() {
                    self.assume_history_type(field, false)?;
                }
                return Ok(());
            }
        }
        self.assume_element_type(value)
    }

    // A merge candidate is a structural value, not evidence that its record
    // invariant holds. Stores are checked before publishing the new root;
    // modular calls assume only their finalized declared input types.
    pub(super) fn history_value(&mut self, ty: &Ty) -> Result<Symbol> {
        let Ty::Record(name) = ty else {
            return self.arbitrary(ty);
        };
        self.charge_value_work(1)?;
        let definition = self
            .declarations
            .structs
            .get(name)
            .cloned()
            .ok_or("unknown history record")?;
        let mut fields = BTreeMap::new();
        for (field, ty) in definition.fields {
            let ty = self.resolve(&ty)?;
            fields.insert(field, self.history_value(&ty)?);
        }
        Ok(Symbol::Record(name.clone(), fields))
    }

    pub(super) fn read_projection_value(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        line: usize,
    ) -> Result<Symbol> {
        self.validate_member_path(reference, path, line)?;
        self.charge_value_work(symbol_weight(self.storage.memory.read(reference)?)?)?;
        let root = self.storage.memory.read(reference)?;
        let value = project(root, path)?.clone();
        for (offset, projection) in path.iter().enumerate() {
            let Projection::Index(index) = projection else {
                continue;
            };
            let prefix = &path[..offset];
            if let Symbol::Array {
                element,
                identity,
                items,
                cells,
                ..
            } = project(root, prefix)?
            {
                if self.history_element(element) {
                    let element = (**element).clone();
                    let identity = identity.clone();
                    let items = items.clone();
                    let cells = cells.clone();
                    let selected =
                        self.read_array(&element, &identity, index, items.as_deref(), &cells)?;
                    return Ok(project(&selected, &path[offset + 1..])?.clone());
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
        let Some(history) = self.arrays.history.get(identity) else {
            return Ok(());
        };
        let cost = match history {
            ArrayHistory::Fill(value) | ArrayHistory::Uninitialized(value) => symbol_weight(value)?,
            ArrayHistory::Store { index, value, .. } => {
                index.terms.len().saturating_add(symbol_weight(value)?)
            }
            ArrayHistory::Choice { condition, .. } => {
                symbol_weight(&Symbol::Bool(condition.clone()))?
            }
        };
        self.charge_value_work(cost)?;
        let history = self
            .arrays
            .history
            .get(identity)
            .cloned()
            .ok_or("array history disappeared")?;
        match history {
            ArrayHistory::Fill(initial) => self.assume(&self.symbol_equal(value, &initial)?),
            ArrayHistory::Uninitialized(_) => {
                Err("uninitialized arrays require sparse ownership reads".into())
            }
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
                    .proof
                    .paths
                    .iter()
                    .flatten()
                    .fold(0usize, |sum, row| sum.saturating_add(row.terms.len() + 1));
                self.charge_value_work(cost)?;
                let base = self.proof.paths.clone();
                let checked = (|| {
                    self.proof.paths = extend(
                        &base,
                        &condition,
                        false,
                        self.session,
                        &mut self.work.value_work,
                    )?;
                    let a = self.array_read(element, &left, index)?;
                    self.assume(&self.symbol_equal(value, &a)?)?;
                    let mut paths = std::mem::take(&mut self.proof.paths);
                    self.proof.paths = extend(
                        &base,
                        &condition,
                        true,
                        self.session,
                        &mut self.work.value_work,
                    )?;
                    let b = self.array_read(element, &right, index)?;
                    self.assume(&self.symbol_equal(value, &b)?)?;
                    paths.append(&mut self.proof.paths);
                    self.feasible_paths(paths)
                })();
                self.proof.paths = base;
                self.proof.paths =
                    paths::bounded(checked?, self.session, &mut self.work.value_work)?;
                Ok(())
            }
        }
    }
}
