//! Resource array frames abstract a forest of unique payload allocations.
//! Borrowed links and shared censuses need a richer frame and remain excluded.

use super::*;

enum Visit {
    Type(Type),
    RecordEnd(String),
}

#[derive(Default)]
pub(super) struct Payloads {
    pub(super) planes: BTreeSet<PlaneId>,
    pub(super) arrays: BTreeSet<String>,
}

impl Context<'_> {
    pub(super) fn resource_loop_array(&mut self, ty: &Ty) -> Result<bool> {
        let Ty::Array(element, _) = ty else {
            return Ok(false);
        };
        let Ty::Union(members) = element.as_ref() else {
            return Ok(false);
        };
        if members.len() != 2 {
            return Ok(false);
        }
        let Some(Ty::Shape(payload)) = members.iter().find(|ty| matches!(ty, Ty::Shape(_))) else {
            return Ok(false);
        };
        if !members.contains(payload.as_ref()) {
            return Ok(false);
        }
        let mut pending = vec![Visit::Type(heap::syntax_type(payload, 0)?)];
        let mut records = BTreeSet::new();
        let mut active = BTreeSet::new();
        while let Some(visit) = pending.pop() {
            self.charge_value_work(1)?;
            let ty = match visit {
                Visit::Type(ty) => ty,
                Visit::RecordEnd(name) => {
                    active.remove(&name);
                    records.insert(name);
                    continue;
                }
            };
            match ty {
                Type::Fact | Type::Ref(_) | Type::Shared(_) | Type::Apply(..) => return Ok(false),
                Type::Unique(inner) | Type::Array(inner, _) => pending.push(Visit::Type(*inner)),
                Type::Union(members) => pending.extend(members.into_iter().map(Visit::Type)),
                Type::Named(name) => {
                    if active.contains(&name) {
                        return Ok(false);
                    }
                    if !records.contains(&name) {
                        active.insert(name.clone());
                        pending.push(Visit::RecordEnd(name.clone()));
                        let record = self
                            .declarations
                            .structs
                            .get(&name)
                            .ok_or("unknown resource frame type")?;
                        pending.extend(record.fields.iter().map(|(_, ty)| Visit::Type(ty.clone())));
                    }
                }
                Type::Shape(_)
                | Type::Int
                | Type::Nat
                | Type::Bool
                | Type::Unit
                | Type::Machine(_) => {}
            }
        }
        Ok(true)
    }

    pub(super) fn loop_owned_payloads(&mut self, value: &Symbol) -> Result<Payloads> {
        let mut payloads = Payloads::default();
        let mut pending = vec![(value.clone(), Formula::True)];
        while let Some((value, guard)) = pending.pop() {
            self.charge_value_work(symbol_weight(&value)?.saturating_add(guard.storage_weight()?))?;
            if self.checked_impossible(&self.proof.paths.clone(), &guard)? {
                continue;
            }
            match value {
                Symbol::Unique(_, reference) => {
                    let plane = self.storage.memory.plane(reference)?;
                    if payloads.planes.insert(plane) {
                        pending.push((self.storage.memory.read(reference)?.clone(), guard));
                    }
                }
                Symbol::Record(_, fields) => {
                    pending.extend(fields.into_values().map(|value| (value, guard.clone())));
                }
                Symbol::Union {
                    active, payloads, ..
                } => {
                    for (tag, payload) in payloads.into_iter().enumerate() {
                        if let Some(payload) = payload {
                            pending.push((
                                payload,
                                guard
                                    .clone()
                                    .and(equal(&active, &Linear::number(tag as i128))?),
                            ));
                        }
                    }
                }
                Symbol::Array {
                    element,
                    identity,
                    len,
                    items,
                    cells,
                } => {
                    let at = |index: &Linear| -> Result<Formula> {
                        Ok(guard
                            .clone()
                            .and(Formula::Ge(index.clone()))
                            .and(Formula::Ge(len.sub(index)?.add(&Linear::number(-1))?)))
                    };
                    for (index, value) in items.into_iter().flatten().enumerate() {
                        pending.push((value, at(&Linear::number(index as i128))?));
                    }
                    if let Some(origin) = self.array_input_origin(&identity)? {
                        payloads.arrays.insert(origin.clone());
                        for (index, _) in self.observed_input_ports(&origin) {
                            let guard = at(&index)?;
                            if !cells.contains_key(&index)
                                && !self.checked_impossible(&self.proof.paths.clone(), &guard)?
                            {
                                let value =
                                    self.read_resource_version(&element, &identity, &index)?;
                                pending.push((value, guard));
                            }
                        }
                    }
                    for (index, value) in cells {
                        pending.push((value, at(&index)?));
                    }
                }
                Symbol::Shared(..) | Symbol::Ref(..) | Symbol::RefCases(..) => {
                    return Err(
                        "resource loop frame contains a shared owner or borrowed payload".into(),
                    );
                }
                _ => {}
            }
        }
        Ok(payloads)
    }
}
