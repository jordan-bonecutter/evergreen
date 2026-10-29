//! Deferred input observations keep their enclosing loop permissions.
//! A late observation is not a runtime allocation born in the iteration.

use super::*;

impl Context<'_> {
    /// Deferred input planes existed before the loop, even when first read in
    /// its body. Only a declared resource family licenses their consumption.
    pub(in crate::compiler::verify) fn register_loop_input_port(
        &mut self,
        origin: &str,
        value: &Symbol,
    ) -> Result<()> {
        if self.storage.loops.is_empty() {
            return Ok(());
        }
        let mut pending = vec![value.clone()];
        let mut planes = BTreeSet::new();
        let mut arrays = BTreeSet::new();
        while let Some(value) = pending.pop() {
            self.charge_value_work(symbol_weight(&value)?)?;
            match value {
                Symbol::Unique(_, reference) | Symbol::Ref(_, reference, _) => {
                    let plane = reference.plane_identity();
                    if planes.insert(plane) {
                        if let Some(initial) = self.arrays.initial_planes.get(&plane) {
                            pending.push(initial.clone());
                        }
                    }
                }
                Symbol::Record(_, fields) => pending.extend(fields.into_values()),
                Symbol::Union { payloads, .. } => pending.extend(payloads.into_iter().flatten()),
                Symbol::Array {
                    identity,
                    items,
                    cells,
                    ..
                } => {
                    if self.arrays.inputs.contains(&identity) {
                        arrays.insert(identity);
                    }
                    pending.extend(items.into_iter().flatten());
                    pending.extend(cells.into_values());
                }
                Symbol::RefCases(_, cases) => {
                    for case in cases {
                        let plane = case.reference.plane_identity();
                        if planes.insert(plane) {
                            if let Some(initial) = self.arrays.initial_planes.get(&plane) {
                                pending.push(initial.clone());
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        self.charge_value_work(self.storage.loops.iter().fold(0usize, |cost, frame| {
            cost.saturating_add(
                planes
                    .len()
                    .saturating_mul(frame.writes.len() + planes.len() + 1),
            )
            .saturating_add(arrays.len() + 1)
        }))?;
        for frame in &mut self.storage.loops {
            if frame.input_arrays.contains(origin) {
                frame.protected.extend(&planes);
                frame.input_arrays.extend(arrays.iter().cloned());
                if frame.resource_arrays.contains(origin) {
                    for &plane in &planes {
                        if !frame
                            .writes
                            .iter()
                            .any(|(known, path)| *known == plane && path.is_empty())
                        {
                            frame.writes.push((plane, Vec::new()));
                        }
                    }
                    frame.resource_arrays.extend(arrays.iter().cloned());
                }
            }
        }
        Ok(())
    }
}
