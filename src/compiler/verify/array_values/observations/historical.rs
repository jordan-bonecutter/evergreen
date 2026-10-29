//! Compose range relations through immutable, reference-free payloads. Saved proof states
//! authorize mathematical observations, never reads of a dead allocation.

use super::*;

fn payload_type(ty: &Type, structs: &BTreeMap<String, Struct>) -> bool {
    match ty {
        Type::Int | Type::Nat | Type::Bool | Type::Unit | Type::Machine(_) | Type::Shape(_) => true,
        Type::Union(members) => members.iter().all(|ty| payload_type(ty, structs)),
        Type::Named(name) => structs.get(name).is_some_and(|definition| {
            definition
                .fields
                .iter()
                .all(|(_, ty)| payload_type(ty, structs))
        }),
        _ => false,
    }
}

impl Context<'_> {
    pub(super) fn historical_payload_type(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Union(members) => members.iter().all(|ty| self.historical_payload_type(ty)),
            Ty::Shape(_) | Ty::Unit => true,
            Ty::Record(name) => payload_type(&Type::Named(name.clone()), self.declarations.structs),
            _ => scalar(ty),
        }
    }

    // A historical proxy describes mathematical contents, not an initialized
    // runtime value. In particular, inactive union members must not contribute
    // nominal invariants or require exploring every member's storage world.
    fn historical_payload(&mut self, ty: &Ty) -> Result<Symbol> {
        self.charge_value_work(1)?;
        match ty {
            Ty::Union(members) => {
                let active = self.fresh_union_tag(members.len())?;
                let payloads = members
                    .iter()
                    .map(|ty| self.historical_payload(ty).map(Some))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Symbol::Union {
                    members: members.clone(),
                    active,
                    payloads,
                })
            }
            Ty::Record(name) => {
                let fields = self
                    .declarations
                    .structs
                    .get(name)
                    .ok_or("unknown historical record")?
                    .fields
                    .clone();
                let mut values = BTreeMap::new();
                for (field, ty) in fields {
                    let ty = self.resolve(&ty)?;
                    values.insert(field, self.historical_payload(&ty)?);
                }
                Ok(Symbol::Record(name.clone(), values))
            }
            Ty::Shape(ty) => Ok(Symbol::Shape(ty.clone())),
            Ty::Unit => Ok(Symbol::Unit),
            ty if scalar(ty) => self.arbitrary(ty),
            _ => Err("historical payload must contain only scalar fields and shapes".into()),
        }
    }

    pub(super) fn historical_value(
        &mut self,
        contents: &Contents,
        index: &Linear,
        ty: &Ty,
        source: Source,
        observations: &mut Observations,
    ) -> Result<Symbol> {
        self.charge_value_work(contents.fields.len() + index.terms.len() + 1)?;
        let key = (contents.clone(), index.clone());
        let cached_weight = self
            .arrays
            .captured_values
            .get(&key)
            .map(symbol_weight)
            .transpose()?
            .unwrap_or(0);
        self.charge_value_work(cached_weight)?;
        let value = if let Some(value) = self.arrays.captured_values.get(&key) {
            value.clone()
        } else {
            if !scalar(ty) && !(contents.whole && self.historical_payload_type(ty)) {
                return Err("historical array observation requires a scalar".into());
            }
            let value = if contents.whole {
                self.historical_payload(ty)?
            } else {
                self.arbitrary(ty)?
            };
            if !contents.whole {
                self.bind_scalar_leaf(contents, index, &value)?;
            }
            self.charge_value_work(symbol_weight(&value)?)?;
            self.arrays
                .captured_values
                .insert(key.clone(), value.clone());
            value
        };
        self.compatible(&value.ty(), ty, 0)?;
        if !contents.whole {
            self.assume_element_type(&value)?;
        }
        if self.arrays.observing_values.contains(&key) {
            return Ok(value);
        }
        if self.arrays.observing_values.len() >= 64 {
            return Err("historical scalar observation depth limit reached".into());
        }
        let mut worlds = BTreeSet::from([source.world]);
        if let Some(snapshot) = self.proof.evidence.subjects(source.theorem) {
            worlds.extend(snapshot.past.keys().copied().map(Some));
        }
        self.charge_value_work(worlds.len())?;
        self.arrays.observing_values.insert(key.clone());
        let observed = Observation {
            identity: &contents.identity,
            index,
            value: &value,
            fields: &contents.fields,
        };
        // Cache only the mathematical value's identity. Facts are rechecked in the current
        // proof context; a successful branch must not populate a global truth.
        let result: Result<()> = worlds.into_iter().try_for_each(|world| {
            self.charge_value_work(contents.fields.len() + index.terms.len() + 1)?;
            let lookup = (contents.clone(), index.clone(), world);
            if observations.completed.get(&lookup) == Some(&observations.revision) {
                return Ok(());
            }
            let revision = observations.revision;
            self.observe_values(&observed, world, observations)?;
            // New interpreted facts may enable previously unavailable domains.
            // Retry in that case, but not when this read's knowledge is unchanged.
            observations.completed.insert(lookup, revision);
            Ok(())
        });
        self.arrays.observing_values.remove(&key);
        result?;
        Ok(value)
    }
}
