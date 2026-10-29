//! Deferred reference-bearing input cells. An array extent never enumerates
//! its pointees. Immutable recipes give each observed cell stable identities
//! across branch restores and entry-memory observations.

use super::*;

#[cfg(test)]
mod symbolic_tests;
#[cfg(test)]
mod tests;

impl Context<'_> {
    /// Observing a cell does not change the array's contents identity. Merge
    /// only sparse metadata for that identity; differing actual values fail.
    pub(super) fn merge_observations(
        &mut self,
        a: &Symbol,
        b: &Symbol,
        inputs: &mut Vec<Symbol>,
    ) -> Result<Symbol> {
        self.charge_value_work(symbol_weight(a)?.saturating_add(symbol_weight(b)?))?;
        if a == b {
            return Ok(a.clone());
        }
        match (a, b) {
            (
                Symbol::Array {
                    element,
                    len,
                    items: a_items,
                    cells: a_cells,
                    identity,
                },
                Symbol::Array {
                    element: b_element,
                    len: b_len,
                    items: b_items,
                    cells: b_cells,
                    identity: b_id,
                },
            ) if element == b_element && len == b_len && identity == b_id => {
                let items = match (a_items, b_items) {
                    (None, None) => None,
                    (Some(a), Some(b)) if a.len() == b.len() => Some(
                        a.iter()
                            .zip(b)
                            .map(|(a, b)| self.merge_observations(a, b, inputs))
                            .collect::<Result<Vec<_>>>()?,
                    ),
                    _ => {
                        return Err(
                            "one array contents identity has inconsistent storage recipes".into(),
                        )
                    }
                };
                let mut cells = a_cells.clone();
                for (index, b) in b_cells {
                    let value = if let Some(a) = cells.get(index) {
                        self.merge_observations(a, b, inputs)?
                    } else {
                        b.clone()
                    };
                    cells.insert(index.clone(), value);
                }
                if self.arrays.inputs.contains(identity) {
                    inputs.extend(cells.values().cloned());
                } else if let Some(origin) = self.array_input_origin(identity)? {
                    // New views of a stored input version still describe
                    // immutable input symbols. Replay their initial bounds,
                    // never nominal invariants of replacement values which
                    // may currently be part of an open update.
                    let cost = self
                        .arrays
                        .ports
                        .get(&origin)
                        .map(|cells| values_weight(cells.values()))
                        .transpose()?
                        .unwrap_or(0);
                    self.charge_value_work(cost)?;
                    inputs.extend(
                        self.observed_input_ports(&origin)
                            .into_iter()
                            .map(|(_, value)| value),
                    );
                }
                Ok(Symbol::Array {
                    element: element.clone(),
                    len: len.clone(),
                    items,
                    cells,
                    identity: identity.clone(),
                })
            }
            (Symbol::Record(name, a), Symbol::Record(b_name, b))
                if name == b_name && a.keys().eq(b.keys()) =>
            {
                let fields = a
                    .iter()
                    .map(|(name, a)| {
                        Ok((name.clone(), self.merge_observations(a, &b[name], inputs)?))
                    })
                    .collect::<Result<BTreeMap<_, _>>>()?;
                Ok(Symbol::Record(name.clone(), fields))
            }
            _ => Err("inconsistent observations of one immutable array contents identity".into()),
        }
    }

    pub(super) fn observed_projection<'a>(
        &'a self,
        mut value: &'a Symbol,
        path: &[Projection<Linear>],
    ) -> Option<&'a Symbol> {
        for step in path {
            value = match (value, step) {
                (
                    Symbol::Union {
                        members, payloads, ..
                    },
                    Projection::Member { index, expected },
                ) if members.get(*index) == Some(expected) => payloads.get(*index)?.as_ref()?,
                (Symbol::Record(_, fields), Projection::Field(name)) => fields.get(name)?,
                (
                    Symbol::Array {
                        items,
                        cells,
                        identity,
                        ..
                    },
                    Projection::Index(index),
                ) => constant_index(index)
                    .and_then(|index| items.as_ref().and_then(|items| items.get(index)))
                    .or_else(|| cells.get(index))
                    .or_else(|| {
                        self.arrays
                            .ports
                            .get(identity)
                            .and_then(|cells| cells.get(index))
                    })?,
                _ => return None,
            };
        }
        Some(value)
    }

    /// Stores keep the same physical input slots while assigning each contents
    /// version its own selector. Resolve identities against that input census.
    pub(super) fn array_input_origin(&mut self, identity: &str) -> Result<Option<String>> {
        let mut current = identity.to_owned();
        loop {
            self.charge_value_work(1 + current.len())?;
            if self.arrays.inputs.contains(&current) {
                return Ok(Some(current));
            }
            match self.arrays.history.get(&current) {
                Some(ArrayHistory::Store { base, .. }) => current = base.clone(),
                _ => return Ok(None),
            }
        }
    }

    pub(super) fn read_resource_version(
        &mut self,
        element: &Ty,
        identity: &str,
        index: &Linear,
    ) -> Result<Symbol> {
        let mut current = identity.to_owned();
        loop {
            self.charge_value_work(1 + current.len())?;
            match self.arrays.history.get(&current) {
                Some(ArrayHistory::Store {
                    index: at, value, ..
                }) => {
                    self.charge_value_work(at.terms.len() + symbol_weight(value)?)?;
                    let ArrayHistory::Store {
                        base,
                        index: at,
                        value,
                    } = self.arrays.history[&current].clone()
                    else {
                        return Err("missing resource array store recipe".into());
                    };
                    let same = equal(index, &at)?;
                    if index == &at || self.checked_entails(&same)? {
                        return Ok(value);
                    }
                    if !self.checked_entails(&same.not())? {
                        return Err(
                            "resource store selection needs proven index equality or separation"
                                .into(),
                        );
                    }
                    current = base;
                }
                _ => return self.input_array_port(element, &current, index),
            }
        }
    }

    /// Demanded input cells share one identity whenever their indices are
    /// provably equal. Distinct recipes require a current, admission-free
    /// separation proof; uncertain aliasing cannot manufacture another owner.
    pub(super) fn input_array_index(&mut self, identity: &str, index: &Linear) -> Result<Linear> {
        let cost = self.arrays.ports.get(identity).map_or(1, |cells| {
            cells
                .keys()
                .fold(1, |cost: usize, at| cost.saturating_add(1 + at.terms.len()))
        });
        self.charge_value_work(cost.saturating_add(index.terms.len()))?;
        let indices = self
            .arrays
            .ports
            .get(identity)
            .map(|cells| cells.keys().cloned().collect::<Vec<_>>())
            .unwrap_or_default();
        let mut selected = None;
        for at in indices {
            let same = equal(index, &at)?;
            if index == &at || self.checked_entails(&same)? {
                if selected.replace(at).is_some() {
                    return Err("input cell recipes overlap in this state; conditional plane identities are required".into());
                }
            } else if !self.checked_entails(&same.not())? {
                return Err("input indices may alias; prove equality or separation before observing another cell".into());
            }
        }
        Ok(selected.unwrap_or_else(|| index.clone()))
    }

    pub(super) fn input_array_port(
        &mut self,
        element: &Ty,
        identity: &str,
        index: &Linear,
    ) -> Result<Symbol> {
        if !self.arrays.inputs.contains(identity) {
            return Err(
                "reference array selection requires a known cell, a deferred input, or an alias contract".into(),
            );
        }
        if let Some(value) = self
            .arrays
            .ports
            .get(identity)
            .and_then(|cells| cells.get(index))
            .cloned()
        {
            self.materialize_input_planes()?;
            self.register_loop_input_port(identity, &value)?;
            self.assume_input_bounds(&value)?;
            return Ok(value);
        }
        if self.deferred_shared_owners(element) {
            return Err("deferred shared-owner elements need census snapshots".into());
        }
        let checkpoint = self.storage.memory.materialization_checkpoint();
        let previous = std::mem::replace(&mut self.execution.materializing_input, true);
        let value = self.arbitrary(element);
        self.execution.materializing_input = previous;
        let value = value?;
        for (plane, initial) in self.storage.memory.materialized_since(checkpoint) {
            self.arrays.initial_planes.insert(plane, initial.clone());
        }
        self.register_loop_input_port(identity, &value)?;
        self.arrays
            .ports
            .entry(identity.to_owned())
            .or_default()
            .insert(index.clone(), value.clone());
        Ok(value)
    }

    fn deferred_shared_owners(&self, ty: &Ty) -> bool {
        fn contains(ty: &Type, structs: &BTreeMap<String, Struct>) -> bool {
            match ty {
                Type::Shared(_) => true,
                Type::Ref(inner) | Type::Unique(inner) | Type::Array(inner, _) => {
                    contains(inner, structs)
                }
                Type::Named(name) => structs.get(name).is_some_and(|record| {
                    record.fields.iter().any(|(_, ty)| contains(ty, structs))
                }),
                Type::Union(members) => members.iter().any(|ty| contains(ty, structs)),
                _ => false,
            }
        }
        heap::syntax_type(ty, 0).map_or(true, |ty| contains(&ty, self.declarations.structs))
    }

    pub(super) fn materialize_input_planes(&mut self) -> Result<()> {
        self.charge_value_work(values_weight(self.arrays.initial_planes.values())?)?;
        for (&plane, initial) in &self.arrays.initial_planes {
            self.storage.memory.materialize_input(plane, initial)?;
        }
        Ok(())
    }

    // Replay facts about immutable INPUT symbols, never assume an invariant
    // about live contents which may since have changed. Reference-bearing
    // nominal invariants need their own revision-dependent evidence.
    pub(super) fn assume_input_bounds(&mut self, value: &Symbol) -> Result<()> {
        self.charge_value_work(1)?;
        if let Symbol::Union {
            members,
            active,
            payloads,
        } = value
        {
            self.assume(&Formula::Ge(active.clone()))?;
            self.assume(&Formula::Ge(
                Linear::number(members.len() as i128 - 1).sub(active)?,
            ))?;
            let base = self.proof.paths.clone();
            let mut alternatives = paths::Paths::default();
            for (index, payload) in payloads.iter().enumerate() {
                let Some(payload) = payload else { continue };
                self.proof.paths = extend(
                    &base,
                    &equal(active, &Linear::number(index as i128))?,
                    false,
                    self.session,
                    &mut self.work.value_work,
                )?;
                let result = self.assume_input_bounds(payload);
                alternatives.extend(self.proof.paths.clone());
                self.proof.paths = base.clone();
                result?;
            }
            self.proof.paths =
                paths::bounded(alternatives, self.session, &mut self.work.value_work)?;
            return Ok(());
        }
        if !self.ty_has_reference(&value.ty()) {
            return self.assume_element_type(value);
        }
        match value {
            Symbol::Ref(_, reference, _) | Symbol::Unique(_, reference) => {
                if let Some(initial) = self
                    .arrays
                    .initial_planes
                    .get(&reference.plane_identity())
                    .cloned()
                {
                    self.assume_input_bounds(&initial)?;
                }
                Ok(())
            }
            Symbol::Record(_, fields) => {
                for field in fields.values() {
                    self.assume_input_bounds(field)?;
                }
                Ok(())
            }
            Symbol::Array { items, cells, .. } => {
                for cell in items.iter().flatten().chain(cells.values()) {
                    self.assume_input_bounds(cell)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    pub(super) fn observed_input_ports(&self, identity: &str) -> Vec<(Linear, Symbol)> {
        self.arrays
            .ports
            .get(identity)
            .into_iter()
            .flat_map(|cells| cells.iter())
            .map(|(index, value)| (index.clone(), value.clone()))
            .collect()
    }
}

pub(super) fn contains_reference_array(ty: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match ty {
        Type::Array(element, _) => {
            type_has_reference(element, structs) || contains_reference_array(element, structs)
        }
        Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) => {
            contains_reference_array(inner, structs)
        }
        Type::Named(name) => structs.get(name).is_some_and(|record| {
            record
                .fields
                .iter()
                .any(|(_, ty)| contains_reference_array(ty, structs))
        }),
        Type::Union(members) => members
            .iter()
            .any(|ty| contains_reference_array(ty, structs)),
        _ => false,
    }
}
