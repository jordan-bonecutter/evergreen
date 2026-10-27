//! Reference identity and the independent-input boundary of modular contracts.

use super::*;

impl Context<'_> {
    pub(super) fn reference_equality(&mut self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        let (Symbol::Ref(_, a, a_path), Symbol::Ref(_, b, b_path)) = (a, b) else {
            return Err("reference equality requires reference operands".into());
        };
        // Identity comparisons do not make stale generations observable again.
        project(self.storage.memory.read(*a)?, a_path)?;
        project(self.storage.memory.read(*b)?, b_path)?;
        self.charge_value_work(a_path.len().saturating_add(b_path.len()))?;
        if a != b || a_path.len() != b_path.len() {
            return Ok(Formula::False);
        }
        let mut same = Formula::True;
        for (a, b) in a_path.iter().zip(b_path) {
            let component = match (a, b) {
                (Projection::Field(a), Projection::Field(b)) if a == b => Formula::True,
                (Projection::Index(a), Projection::Index(b)) => equal(a, b)?,
                _ => return Ok(Formula::False),
            };
            same = same.and(component);
        }
        Ok(same)
    }

    pub(super) fn reference_ports_overlap(&mut self, inputs: &[InputReference]) -> Result<bool> {
        // Distinct planes need no pairwise arithmetic checks. Charge every
        // input and every same-plane comparison to the common proof-work budget.
        let mut planes: BTreeMap<PlaneId, Vec<usize>> = BTreeMap::new();
        for (index, input) in inputs.iter().enumerate() {
            self.charge_value_work(1)?;
            let plane = self.storage.memory.plane(input.reference)?;
            let previous = planes.entry(plane).or_default();
            for other in previous.iter().map(|index| &inputs[*index]) {
                self.charge_value_work(1)?;
                if !self.paths_disjoint(&input.path, &other.path)? {
                    return Ok(true);
                }
            }
            previous.push(index);
        }
        Ok(false)
    }
}

impl Context<'_> {
    // Join constraints must be installed before checking the selected index or
    // materializing its view. No new plane is allocated for a conditional borrow.
    pub(super) fn materialize_joined_reference(
        &mut self,
        value: &Symbol,
        line: usize,
    ) -> Result<()> {
        let Symbol::Ref(target, reference, path) = value else {
            return Err("invalid joined reference".into());
        };
        let Some((offset, Projection::Index(index))) = path
            .iter()
            .enumerate()
            .rfind(|(_, step)| matches!(step, Projection::Index(_)))
        else {
            return Err("joined references require an array element".into());
        };
        let prefix = &path[..offset];
        let suffix = &path[offset + 1..];
        self.charge_value_work(symbol_weight(self.storage.memory.read(*reference)?)?)?;
        let mut root = self.storage.memory.read(*reference)?.clone();
        let Symbol::Array {
            element,
            len,
            items,
            cells,
            identity,
        } = project(&root, prefix)?
        else {
            return Err("joined reference prefix requires array storage".into());
        };
        if !self.history_element(element) {
            return Err(
                "joined references require scalars or reference-free record elements without runtime cleanup".into(),
            );
        }
        self.prove(
            &Formula::Ge(index.clone()),
            "joined reference index is nonnegative",
            line,
        )?;
        self.prove(
            &Formula::Ge(len.sub(index)?.add(&Linear::number(-1))?),
            "joined reference index < length",
            line,
        )?;
        let value = self.read_array(element, identity, index, items.as_deref(), cells)?;
        if project(&value, suffix)?.ty() != **target {
            return Err("joined reference target type changed".into());
        }
        let Symbol::Array { cells, .. } = project_mut(&mut root, prefix)? else {
            return Err("invalid joined array storage".into());
        };
        cells.insert(index.clone(), value);
        let plane = self.storage.memory.plane(*reference)?;
        self.storage.memory.write(plane, root, false)
    }
}

impl Context<'_> {
    pub(super) fn materialize_live_reference_views(
        &mut self,
        value: &Symbol,
        line: usize,
    ) -> Result<()> {
        self.charge_value_work(1)?;
        match value {
            Symbol::Ref(_, reference, path) => {
                // An old stale handle stays stale; observing it later will
                // fail. Never replace its generation or allocate new storage.
                if let Ok(root) = self.storage.memory.read(*reference) {
                    if project(root, path).is_err() {
                        self.materialize_joined_reference(value, line)?;
                    }
                }
            }
            Symbol::Record(_, fields) => {
                for value in fields.values() {
                    self.materialize_live_reference_views(value, line)?;
                }
            }
            Symbol::Array { items, cells, .. } => {
                for value in items.iter().flatten().chain(cells.values()) {
                    self.materialize_live_reference_views(value, line)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
}

impl Context<'_> {
    pub(super) fn incoming_references(
        &mut self,
        function: &Function,
        strict: bool,
    ) -> Result<Vec<InputReference>> {
        fn visit(
            ctx: &mut Context<'_>,
            value: &Symbol,
            origin: String,
            mode: (bool, bool),
            inputs: &mut Vec<InputReference>,
            work: &mut usize,
            limit: usize,
        ) -> Result<()> {
            let (strict, borrowed) = mode;
            *work = work.saturating_add(1 + origin.len() / 32);
            if *work > limit {
                return Err(
                    "symbolic value work limit reached while checking incoming references".into(),
                );
            }
            match value {
                Symbol::Ref(pointee, reference, path) => {
                    if inputs.len() >= 8192 {
                        return Err("incoming reference graph limit reached (8192)".into());
                    }
                    for step in path {
                        *work = work.saturating_add(
                            1 + match step {
                                Projection::Field(name) => name.len() / 32,
                                Projection::Index(index) => index.terms.len(),
                            },
                        );
                    }
                    if *work > limit {
                        return Err(
                            "symbolic value work limit reached while checking incoming references"
                                .into(),
                        );
                    }
                    inputs.push(InputReference {
                        origin: origin.clone(),
                        reference: *reference,
                        path: path.clone(),
                        pointee: pointee.clone(),
                    });
                    let target = project(ctx.storage.memory.read(*reference)?, path)?;
                    *work = work.saturating_add(symbol_weight(target)?);
                    let target = target.clone();
                    visit(
                        ctx,
                        &target,
                        format!("(*{origin})"),
                        (strict, true),
                        inputs,
                        work,
                        limit,
                    )?;
                }
                Symbol::Plane(pointee, reference) => {
                    if borrowed {
                        if inputs.len() >= 8192 {
                            return Err("incoming reference graph limit reached (8192)".into());
                        }
                        inputs.push(InputReference {
                            origin: origin.clone(),
                            reference: *reference,
                            path: Vec::new(),
                            pointee: pointee.clone(),
                        });
                    }
                    let target = ctx.storage.memory.read(*reference)?;
                    *work = work.saturating_add(symbol_weight(target)?);
                    let target = target.clone();
                    visit(
                        ctx,
                        &target,
                        format!("(*{origin})"),
                        mode,
                        inputs,
                        work,
                        limit,
                    )?;
                }
                Symbol::Union {
                    active, payloads, ..
                } if borrowed => {
                    for (index, payload) in payloads.iter().enumerate() {
                        let Some(payload) = payload else {
                            continue;
                        };
                        if !ctx.ty_has_reference(&payload.ty()) {
                            continue;
                        }
                        let guard = equal(active, &Linear::number(index as i128))?;
                        // A pointer port exists only in its checked active case.
                        // An undecided union is still rechecked with actual storage
                        // at calls; it cannot grant a conditional write contract.
                        if ctx.checked_entails(&guard)? {
                            visit(ctx, payload, origin.clone(), mode, inputs, work, limit)?;
                        }
                    }
                }
                Symbol::Record(_, fields) => {
                    for (name, value) in fields {
                        visit(
                            ctx,
                            value,
                            format!("{origin}.{name}"),
                            mode,
                            inputs,
                            work,
                            limit,
                        )?;
                    }
                }
                Symbol::Array {
                    element,
                    len,
                    items,
                    ..
                } if ctx.ty_has_reference(element) => {
                    if let Some(items) = items {
                        for (index, value) in items.iter().enumerate() {
                            visit(
                                ctx,
                                value,
                                format!("{origin}[{index}]"),
                                mode,
                                inputs,
                                work,
                                limit,
                            )?;
                        }
                    } else if strict && *len != Linear::number(0) {
                        return Err(
                            "write contracts cannot summarize opaque arrays containing references"
                                .into(),
                        );
                    }
                }
                _ => {}
            }
            Ok(())
        }
        let mut inputs = Vec::new();
        let mut work = 0usize;
        let remaining = MAX_VALUE_WORK.saturating_sub(self.work.value_work);
        for (name, _) in &function.params {
            let value = self
                .locals
                .values
                .get(name)
                .ok_or("missing input parameter")?;
            let weight = symbol_weight(value)?;
            let value = value.clone();
            work = work.saturating_add(weight);
            if self.ty_has_reference(&value.ty()) {
                visit(
                    self,
                    &value,
                    name.clone(),
                    (strict, false),
                    &mut inputs,
                    &mut work,
                    remaining,
                )?;
            }
        }
        self.charge_value_work(work)?;
        Ok(inputs)
    }
}
