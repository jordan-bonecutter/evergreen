//! Compose range relations through immutable scalar leaves. Saved proof states
//! authorize mathematical observations, never reads of a dead allocation.

use super::*;

impl Context<'_> {
    pub(super) fn historical_scalar_value(
        &mut self,
        contents: &Contents,
        index: &Linear,
        ty: &Ty,
        source: Source,
    ) -> Result<Symbol> {
        self.charge_value_work(contents.fields.len() + index.terms.len() + 1)?;
        let key = (contents.clone(), index.clone());
        let value = if let Some(value) = self.arrays.captured_scalars.get(&key) {
            value.clone()
        } else {
            if !scalar(ty) {
                return Err("historical array observation requires a scalar".into());
            }
            let value = self.arbitrary(ty)?;
            self.bind_scalar_leaf(contents, index, &value)?;
            self.arrays
                .captured_scalars
                .insert(key.clone(), value.clone());
            value
        };
        self.compatible(&value.ty(), ty, 0)?;
        self.assume_element_type(&value)?;
        if self.arrays.observing_scalars.contains(&key) {
            return Ok(value);
        }
        if self.arrays.observing_scalars.len() >= 64 {
            return Err("historical scalar observation depth limit reached".into());
        }
        let mut worlds = BTreeSet::from([source.world]);
        if let Some(snapshot) = self.proof.evidence.subjects(source.theorem) {
            worlds.extend(snapshot.past.keys().copied().map(Some));
        }
        self.charge_value_work(worlds.len())?;
        self.arrays.observing_scalars.insert(key.clone());
        let observed = Observation {
            identity: &contents.identity,
            index,
            value: &value,
            fields: &contents.fields,
        };
        // Cache only the scalar's identity. Facts are rechecked in the current
        // proof context; a successful branch must not populate a global truth.
        let result = worlds
            .into_iter()
            .try_for_each(|world| self.observe_values(&observed, world));
        self.arrays.observing_scalars.remove(&key);
        result?;
        Ok(value)
    }
}
