//! Resource arrays retain one empty initializer and only demanded cells. Every
//! materialized index denotes a distinct location under the current path.

use super::*;

#[cfg(test)]
mod tests;

impl Context<'_> {
    pub(super) fn empty_array_target(source: &Ty, target: &Ty) -> bool {
        matches!((source, target), (Ty::Array(source, _), Ty::Array(target, _))
            if matches!(target.as_ref(), Ty::Shape(_))
                && matches!(source.as_ref(), Ty::Union(members) if members.contains(target)))
    }

    fn cell_has_shape(&mut self, value: &Symbol, target: &Ty) -> Result<bool> {
        match value {
            Symbol::Shape(_) => Ok(&value.ty() == target),
            Symbol::Union {
                members, active, ..
            } => {
                let Some(index) = members.iter().position(|member| member == target) else {
                    return Ok(false);
                };
                self.checked_entails(&equal(active, &Linear::number(index as i128))?)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn narrow_empty_array(
        &mut self,
        source: &Ty,
        reference: Reference,
        target: &Ty,
        line: usize,
    ) -> Result<Symbol> {
        if self.execution.phase != Phase::Runtime || !self.storage.opened_planes.is_empty() {
            return Err(
                "empty array transitions require runtime execution with closed invariants".into(),
            );
        }
        let (Ty::Array(_, source_len), Ty::Array(element, target_len)) = (source, target) else {
            return Err("empty array conversion requires array storage".into());
        };
        self.prove(
            &equal(source_len, target_len)?,
            "empty array extent is unchanged",
            line,
        )?;
        self.charge_value_work(symbol_weight(self.storage.memory.read(reference)?)?)?;
        let Symbol::Array {
            element: stored_element,
            len,
            items,
            cells,
            identity,
        } = self.storage.memory.read(reference)?.clone()
        else {
            return Err("empty array conversion requires array storage".into());
        };
        let initial = match self.arrays.history.get(&identity).cloned() {
            Some(ArrayHistory::Uninitialized(initial)) => Some(initial),
            _ => None,
        };
        let default_empty = if let Some(initial) = initial {
            self.cell_has_shape(&initial, element)?
        } else {
            false
        };
        let covered = if default_empty {
            true
        } else if let Some(items) = &items {
            self.checked_entails(&equal(&len, &Linear::number(items.len() as i128))?)?
        } else {
            self.empty_array_coverage(&len, &cells)?
        };
        if !covered {
            return Err(
                "empty array conversion requires an empty default or complete cell coverage".into(),
            );
        }
        let before = crate::compiler::layout::of(
            &heap::syntax_type(&stored_element, line)?,
            self.declarations.structs,
        )?;
        let after = crate::compiler::layout::of(
            &heap::syntax_type(element, line)?,
            self.declarations.structs,
        )?;
        if before.size != after.size || before.align != after.align {
            return Err("empty array conversion must preserve element size and alignment".into());
        }
        let Ty::Shape(inner) = element.as_ref() else {
            unreachable!();
        };
        let empty = Symbol::Shape(inner.clone());
        let items = items
            .map(|items| {
                items
                    .into_iter()
                    .map(|value| {
                        if !self.cell_has_shape(&value, element)? {
                            return Err(
                                "empty array conversion would discard an initialized member".into(),
                            );
                        }
                        Ok(empty.clone())
                    })
                    .collect::<Result<Vec<_>>>()
            })
            .transpose()?;
        let mut converted = BTreeMap::new();
        for (index, value) in cells {
            self.charge_value_work(1 + index.terms.len())?;
            if !self.cell_has_shape(&value, element)? {
                return Err("empty array conversion would discard an initialized member".into());
            }
            converted.insert(index, empty.clone());
        }
        let identity = self.fresh_name();
        self.arrays
            .history
            .insert(identity.clone(), ArrayHistory::Uninitialized(empty));
        let value = Symbol::Array {
            element: element.clone(),
            len,
            items,
            cells: converted,
            identity,
        };
        let plane = self.storage.memory.plane(reference)?;
        self.note_state_write(plane, &[])?;
        // Geometry is unchanged. Existing slot references observe shapes in
        // the current proof state; freeing the allocation invalidates them.
        self.storage.memory.write(plane, value, false)?;
        Ok(Symbol::Unique(
            Box::new(target.clone()),
            self.storage.memory.borrow(plane)?,
        ))
    }

    // Coverage visits only existing cells. The zero-length case follows from
    // the same rule, without demanding or generating any element.
    fn empty_array_coverage(
        &mut self,
        len: &Linear,
        cells: &BTreeMap<Linear, Symbol>,
    ) -> Result<bool> {
        for (index, observed) in cells.keys().enumerate() {
            self.charge_value_work(1)?;
            if *observed != Linear::number(index as i128) {
                return Ok(false);
            }
        }
        self.checked_entails(&equal(len, &Linear::number(cells.len() as i128))?)
    }

    pub(super) fn uninitialized_index_reference(
        &mut self,
        array: &guarded_references::Case,
        index: &Linear,
        element: &Ty,
        identity: &str,
        cells: &BTreeMap<Linear, Symbol>,
        line: usize,
    ) -> Result<Symbol> {
        if cells.contains_key(index) {
            let mut path = array.path.clone();
            path.push(Projection::Index(index.clone()));
            return Ok(Symbol::Ref(
                Box::new(element.clone()),
                array.reference,
                path,
            ));
        }
        let mut cases = Vec::new();
        let mut distinct = Formula::True;
        for observed in cells.keys() {
            self.charge_value_work(1 + observed.terms.len())?;
            let aliases = equal(index, observed)?;
            let mut path = array.path.clone();
            path.push(Projection::Index(observed.clone()));
            cases.push(guarded_references::Case {
                reference: array.reference,
                path,
                guard: array.guard.clone().and(aliases.clone()),
            });
            distinct = distinct.and(aliases.not());
        }
        let mut path = array.path.clone();
        path.push(Projection::Index(index.clone()));
        cases.push(guarded_references::Case {
            reference: array.reference,
            path,
            guard: array.guard.clone().and(distinct),
        });
        self.on_reference_places(
            &cases,
            Some(&Ty::Ref(Box::new(element.clone()))),
            line,
            &|ctx, case| {
                let Some(Projection::Index(selected)) = case.path.last() else {
                    return Err("invalid sparse array cell".into());
                };
                if !cells.contains_key(selected) {
                    let value = ctx.read_uninitialized_array(identity, selected, cells)?;
                    ctx.charge_value_work(symbol_weight(
                        ctx.storage.memory.read(case.reference)?,
                    )?)?;
                    let mut root = ctx.storage.memory.read(case.reference)?.clone();
                    let Symbol::Array { cells, .. } = project_mut(&mut root, &array.path)? else {
                        return Err("invalid sparse array root".into());
                    };
                    cells.insert(selected.clone(), value);
                    let plane = ctx.storage.memory.plane(case.reference)?;
                    ctx.storage.memory.write(plane, root, false)?;
                }
                Ok(Symbol::Ref(
                    Box::new(element.clone()),
                    case.reference,
                    case.path.clone(),
                ))
            },
        )
    }

    pub(super) fn shape_initializer(&self, value: &Symbol) -> bool {
        match value {
            Symbol::Shape(_) => true,
            Symbol::Union {
                members,
                active,
                payloads,
            } if active.terms.is_empty() => {
                let Some(index) = constant_index(active) else {
                    return false;
                };
                matches!(members.get(index), Some(Ty::Shape(_)))
                    && matches!(payloads.get(index), Some(Some(Symbol::Shape(_))))
                    && payloads
                        .iter()
                        .enumerate()
                        .all(|(other, value)| other == index || value.is_none())
            }
            _ => false,
        }
    }

    pub(super) fn read_uninitialized_array(
        &mut self,
        identity: &str,
        index: &Linear,
        cells: &BTreeMap<Linear, Symbol>,
    ) -> Result<Symbol> {
        if let Some(value) = cells.get(index) {
            self.charge_value_work(symbol_weight(value)?)?;
            return Ok(value.clone());
        }
        for (observed, value) in cells {
            self.charge_value_work(1 + observed.terms.len())?;
            if self.checked_entails(&equal(index, observed)?)? {
                self.charge_value_work(symbol_weight(value)?)?;
                return Ok(value.clone());
            }
            if !self.checked_entails(&equal(index, observed)?.not())? {
                return Err(
                    "sparse ownership reads require resolving whether indices alias".into(),
                );
            }
        }
        let Some(ArrayHistory::Uninitialized(value)) = self.arrays.history.get(identity) else {
            return Err("missing uninitialized array storage".into());
        };
        let cost = symbol_weight(value)?;
        self.charge_value_work(cost)?;
        let Some(ArrayHistory::Uninitialized(value)) = self.arrays.history.get(identity) else {
            unreachable!();
        };
        Ok(value.clone())
    }
}
