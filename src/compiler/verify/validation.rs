//! Complete observations and retained-invariant checks on actual storage.

use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Validation {
    Complete,
    Retained,
}

impl Context<'_> {
    pub(super) fn record_valid(&mut self, value: &Symbol, line: usize) -> Result<()> {
        self.validate_value(value, line, &BTreeSet::new(), Validation::Complete)
    }

    pub(super) fn validate_opened_planes(&mut self, line: usize) -> Result<()> {
        let planes = self
            .storage
            .opened_planes
            .keys()
            .copied()
            .collect::<Vec<_>>();
        for plane in planes {
            self.charge_value_work(symbol_weight(self.storage.memory.get(plane)?)?)?;
            let value = self.storage.memory.get(plane)?.clone();
            let lifted = self.storage.opened_planes[&plane].clone();
            self.retained_valid_with(&value, line, &lifted)?;
        }
        Ok(())
    }

    pub(super) fn retained_valid_with(
        &mut self,
        value: &Symbol,
        line: usize,
        lifted: &BTreeSet<String>,
    ) -> Result<()> {
        // Dormant containers may still carry an open plane. Check retained
        // requirements through their ownership/borrow edges without publishing
        // the lifted facts. Expression and argument observations use full
        // validation instead, so they cannot rely on a suspended invariant.
        self.validate_value(value, line, lifted, Validation::Retained)
    }

    fn validate_value(
        &mut self,
        value: &Symbol,
        line: usize,
        lifted: &BTreeSet<String>,
        mode: Validation,
    ) -> Result<()> {
        self.charge_value_work(1)?;
        match value {
            Symbol::Union {
                active, payloads, ..
            } => {
                let paths = self.proof.paths.clone();
                for (index, value) in payloads.iter().enumerate() {
                    if let Some(value) = value {
                        self.proof.paths = extend(
                            &paths,
                            &equal(active, &Linear::number(index as i128))?,
                            false,
                            self.session,
                            &mut self.work.value_work,
                        )?;
                        let case = self.proof.paths.clone();
                        let checked = if self.checked_impossible(&case, &Formula::True)? {
                            Ok(())
                        } else {
                            self.validate_argument_mode(value, line, mode)
                        };
                        self.proof.paths = paths.clone();
                        checked?;
                    }
                }
                Ok(())
            }
            Symbol::Owner(ty, owner) => {
                let reference = self.storage.memory.borrow_owned(*owner)?;
                self.validate_value(&Symbol::Plane(ty.clone(), reference), line, lifted, mode)
            }
            Symbol::Plane(_, reference) => {
                let selected = if mode == Validation::Retained {
                    self.storage
                        .opened_planes
                        .get(&self.storage.memory.plane(*reference)?)
                        .cloned()
                        .unwrap_or_default()
                } else {
                    BTreeSet::new()
                };
                self.charge_value_work(symbol_weight(self.storage.memory.read(*reference)?)?)?;
                let stored = self.storage.memory.read(*reference)?.clone();
                self.validate_value(&stored, line, &selected, mode)
            }
            Symbol::Array { .. } => self.validate_array(value, line, mode),
            Symbol::Record(..) => self.validate_record(value, line, lifted, mode),
            _ => Ok(()),
        }
    }

    fn validate_array(&mut self, value: &Symbol, line: usize, mode: Validation) -> Result<()> {
        let Symbol::Array {
            element,
            items,
            cells,
            identity,
            ..
        } = value
        else {
            return Err("array validation requires an array".into());
        };
        if matches!(**element, Ty::Record(_)) && self.history_element(element) {
            let indices = cells
                .keys()
                .cloned()
                .chain(
                    (0..items.as_ref().map_or(0, Vec::len))
                        .map(|index| Linear::number(index as i128)),
                )
                .collect::<BTreeSet<_>>();
            for index in indices {
                // Joined stores may contain views born in either branch.
                // Replay their value definitions and primitive type bounds
                // before checking nominal invariants in the merged context.
                let element =
                    self.read_array(element, identity, &index, items.as_deref(), cells)?;
                self.validate_argument_mode(&element, line, mode)?;
            }
            return Ok(());
        }
        for v in items.iter().flatten().chain(cells.values()) {
            self.validate_argument_mode(v, line, mode)?;
        }
        Ok(())
    }

    fn validate_record(
        &mut self,
        value: &Symbol,
        line: usize,
        lifted: &BTreeSet<String>,
        mode: Validation,
    ) -> Result<()> {
        let Symbol::Record(name, fields) = value else {
            return Ok(());
        };
        let def = self
            .declarations
            .structs
            .get(name)
            .ok_or("unknown struct")?;
        if def.fields.len() != fields.len() {
            return Err(format!("line {line}: wrong fields for {name}"));
        }
        let saved = std::mem::take(&mut self.locals.values);
        let saved_roots = std::mem::take(&mut self.locals.places);
        let saved_facts = std::mem::take(&mut self.proof.facts);
        let saved_module = std::mem::replace(&mut self.locals.module, def.module.clone());
        let saved_phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        self.proof.facts = def.facts.iter().cloned().collect();
        self.locals.places.clear();
        self.locals.values.clear();
        for (n, t) in &def.fields {
            let v = fields
                .get(n)
                .ok_or_else(|| format!("line {line}: missing field {n}"))?;
            self.validate_argument_mode(v, line, mode)?;
            let t = self.resolve(t)?;
            self.compatible(&v.ty(), &t, line)?;
            self.locals.values.insert(n.clone(), v.clone());
        }
        self.locals.values.insert("self".into(), value.clone());
        if let Some(p) = &def.invariant {
            let mut requirements = Vec::new();
            clauses(p, &mut requirements);
            for requirement in requirements {
                if matches!(&requirement.kind, Kind::Name(n) if lifted.contains(n)) {
                    continue;
                }
                let p = self.proposition(requirement)?;
                self.prove(&p, &format!("invariant of {name}"), line)?;
            }
        }
        self.locals.values = saved;
        self.locals.places = saved_roots;
        self.proof.facts = saved_facts;
        self.locals.module = saved_module;
        self.execution.phase = saved_phase;
        Ok(())
    }

    fn validate_reference(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        line: usize,
    ) -> Result<()> {
        self.charge_value_work(symbol_weight(project(
            self.storage.memory.read(reference)?,
            path,
        )?)?)?;
        let target = project(self.storage.memory.read(reference)?, path)?.clone();
        self.validate_argument(&target, line)
    }

    pub(super) fn validate_argument(&mut self, value: &Symbol, line: usize) -> Result<()> {
        self.validate_argument_mode(value, line, Validation::Complete)
    }

    fn validate_argument_mode(
        &mut self,
        value: &Symbol,
        line: usize,
        mode: Validation,
    ) -> Result<()> {
        if let Symbol::Ref(_, reference, path) = value {
            if mode == Validation::Retained {
                self.validate_retained_reference(*reference, path, line)
            } else {
                self.validate_reference(*reference, path, line)
            }
        } else {
            self.validate_value(value, line, &BTreeSet::new(), mode)
        }
    }

    fn validate_retained_reference(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        line: usize,
    ) -> Result<()> {
        let selected = if path.is_empty() {
            self.storage
                .opened_planes
                .get(&self.storage.memory.plane(reference)?)
                .cloned()
                .unwrap_or_default()
        } else {
            BTreeSet::new()
        };
        self.charge_value_work(symbol_weight(project(
            self.storage.memory.read(reference)?,
            path,
        )?)?)?;
        let target = project(self.storage.memory.read(reference)?, path)?.clone();
        self.retained_valid_with(&target, line, &selected)
    }

    pub(super) fn validate_live(&mut self, line: usize) -> Result<()> {
        let values = self
            .locals
            .values
            .iter()
            .filter_map(|(name, value)| {
                if let Some(id) = self.locals.places.get(name) {
                    self.storage
                        .memory
                        .get(*id)
                        .ok()
                        .cloned()
                        .map(|value| (Some(*id), value))
                } else {
                    Some((None, value.clone()))
                }
            })
            .collect::<Vec<_>>();
        for (plane, value) in values {
            if let Symbol::Ref(_, reference, path) = &value {
                // A stale plain reference can remain as never until observed.
                if self.storage.memory.read(*reference).is_err() {
                    continue;
                }
                // A dormant whole-object view cannot be observed while its
                // invariant is lifted. Its own future use still checks the
                // complete target type; remaining requirements are checked here.
                if path.is_empty()
                    && self
                        .storage
                        .opened_planes
                        .contains_key(&self.storage.memory.plane(*reference)?)
                {
                    continue;
                }
                self.validate_argument_mode(&value, line, Validation::Retained)?;
            } else {
                let lifted = plane
                    .and_then(|plane| self.storage.opened_planes.get(&plane))
                    .cloned()
                    .unwrap_or_default();
                self.retained_valid_with(&value, line, &lifted)?;
            }
        }
        // Rebinding a parameter cannot discard the caller's original typed
        // view. Borrowed input storage must remain valid at this boundary.
        let inputs = std::mem::take(&mut self.storage.inputs);
        let result = inputs.iter().try_for_each(|input| {
            self.validate_retained_reference(input.reference, &input.path, line)
        });
        self.storage.inputs = inputs;
        result?;
        self.validate_opened_planes(line)
    }
}
