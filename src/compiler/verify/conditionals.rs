//! Conditional evaluation and storage joins. Branches retain distinct symbolic
//! paths and may join only compatible live storage and ownership generations.

use super::*;

struct BranchView {
    memory: Memory<Symbol>,
    facts: state::State,
    censuses: BTreeMap<Reference, Linear>,
}

impl Context<'_> {
    pub(super) fn eval_conditional(
        &mut self,
        condition: &Expr,
        yes: &Expr,
        no: &Expr,
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        let p = self
            .scoped_eval(condition, Some(&Ty::Bool))?
            .proposition()?;
        // The declaration already checked both branches. A body recheck can
        // follow an actual, admission-free decision without manufacturing the
        // allocations or ownership states of an unreachable branch.
        if self.execution.rechecking != 0 || self.execution.cleanup_depth != 0 {
            if self.checked_entails(&p)? {
                return self.scoped_eval(yes, expected);
            }
            if self.checked_entails(&p.clone().not())? {
                return self.scoped_eval(no, expected);
            }
        }
        let base = self.proof.paths.clone();
        let control_weight = self
            .proof
            .control
            .as_ref()
            .map(Formula::storage_weight)
            .transpose()?
            .unwrap_or(1);
        self.charge_value_work(
            control_weight
                .saturating_add(p.storage_weight()?)
                .saturating_mul(4),
        )?;
        let control = self.proof.control.clone().unwrap_or(Formula::True);
        let claims = self.proof.claims.clone();
        let value_claims = self.proof.value_claims.clone();
        // Give caller bindings stable storage identities before forking.
        for (name, value) in self.clone_env()? {
            if !self.locals.places.contains_key(&name) {
                let plane = self.allocate_symbol(value)?;
                self.locals.places.insert(name, plane);
            }
        }
        let env = self.clone_env()?;
        let roots = self.locals.places.clone();
        let store = self.branch_view()?;
        self.proof.paths = extend(&base, &p, false, self.session, &mut self.work.value_work)?;
        self.proof.control = Some(control.clone().and(p.clone()));
        let a = self.scoped_eval(yes, expected)?;
        let a_paths = self.proof.paths.clone();
        let a_store = self.branch_view()?;
        self.proof.claims = claims.clone();
        self.proof.value_claims = value_claims.clone();
        self.proof.paths = extend(&base, &p, true, self.session, &mut self.work.value_work)?;
        self.charge_value_work(values_weight(env.values())?)?;
        self.locals.values = env.clone();
        self.locals.places = roots.clone();
        self.restore_branch_view(&store)?;
        self.proof.control = Some(control.clone().and(p.clone().not()));
        let b = self.scoped_eval(no, Some(&a.ty()))?;
        let b_paths = self.proof.paths.clone();
        let b_store = self.branch_view()?;
        self.proof.claims = claims;
        self.proof.value_claims = value_claims;
        self.proof.paths = base;
        self.proof.control = Some(control);
        self.locals.values = env;
        self.locals.places = roots;
        self.restore_branch_view(&store)?;
        self.proof
            .subjects
            .merge(&store.facts, &a_store.facts, &b_store.facts, &p)?;
        let mut state_a = Formula::True;
        let mut state_b = Formula::True;
        let mut views = Vec::new();
        let a_states = a_store.memory.states();
        let b_states = b_store.memory.states();
        for (index, (id, generation, original)) in store.memory.states().into_iter().enumerate() {
            let (_, ag, av) = a_states.get(index).ok_or("missing branch plane")?;
            let (_, bg, bv) = b_states.get(index).ok_or("missing branch plane")?;
            // A union's virtual allocation exists only in its active case.
            // Consuming it there also consumes the counterfactual slot in the
            // other branch, provided that branch proves it never existed.
            let absent_in = match (av, bv) {
                (Some(_), None) if *ag == generation && *bg == generation.saturating_add(1) => {
                    Some(&a_paths)
                }
                (None, Some(_)) if *bg == generation && *ag == generation.saturating_add(1) => {
                    Some(&b_paths)
                }
                _ => None,
            };
            if let Some(live_paths) = absent_in {
                if original.is_some()
                    && self.checked_impossible(live_paths, &self.plane_presence(id))?
                {
                    self.take_symbol(id)?;
                    continue;
                }
            }
            if ag != bg {
                return Err("conditional branches have different ownership or storage generations; conditional shapes are not implemented".into());
            }
            match (av, bv) {
                (Some(av), Some(bv)) if *ag == generation => {
                    let (joined, left, right) = self.join_value(av, bv, &mut views)?;
                    self.storage.memory.write(id, joined, false)?;
                    state_a = state_a.and(left);
                    state_b = state_b.and(right);
                }
                (None, None) => {
                    let expected = if original.is_some() {
                        generation
                            .checked_add(1)
                            .ok_or("plane generation exhausted")?
                    } else {
                        generation
                    };
                    if *ag != expected {
                        return Err("conditional storage generation cannot be joined".into());
                    }
                    if original.is_some() {
                        self.take_symbol(id)?;
                    }
                }
                _ => {
                    return Err(
                        "conditional branches must leave the same live bindings and storage layout"
                            .into(),
                    )
                }
            }
        }
        self.storage
            .memory
            .import_new_planes(&a_store.memory, &store.memory)?;
        self.storage
            .memory
            .import_new_planes(&b_store.memory, &store.memory)?;
        for (name, id) in &self.locals.places {
            if let Ok(value) = self.storage.memory.get(*id) {
                self.locals.values.insert(name.clone(), value.clone());
            }
        }
        let (result, left, right) = self.join_value(&a, &b, &mut views)?;
        let relation_a = state_a.and(left);
        let relation_b = state_b.and(right);
        let mut paths = extend(
            &a_paths,
            &relation_a,
            false,
            self.session,
            &mut self.work.value_work,
        )?;
        paths.extend(extend(
            &b_paths,
            &relation_b,
            false,
            self.session,
            &mut self.work.value_work,
        )?);
        // Drop infeasible branch combinations only with a checked
        // contradiction certificate; a failed probe keeps the path.
        paths = self.feasible_paths(paths)?;
        self.proof.paths = paths::bounded(paths, self.session, &mut self.work.value_work)?;
        for view in views {
            self.materialize_joined_reference(&view, line)?;
        }
        for (name, id) in &self.locals.places {
            if let Ok(value) = self.storage.memory.get(*id) {
                self.locals.values.insert(name.clone(), value.clone());
            }
        }
        Ok(result)
    }

    fn branch_view(&mut self) -> Result<BranchView> {
        Ok(BranchView {
            memory: self.snapshot_memory()?,
            facts: self.proof.subjects.snapshot(),
            censuses: self.censuses.clone(),
        })
    }

    fn restore_branch_view(&mut self, view: &BranchView) -> Result<()> {
        if self.censuses != view.censuses {
            return Err(
                "conditional owner-census transitions require guarded token joins; unsupported"
                    .into(),
            );
        }
        self.storage.memory = self.clone_store(&view.memory)?;
        self.proof.subjects.restore(view.facts.clone());
        Ok(())
    }

    fn join_value(
        &mut self,
        a: &Symbol,
        b: &Symbol,
        views: &mut Vec<Symbol>,
    ) -> Result<(Symbol, Formula, Formula)> {
        self.charge_value_work(1)?;
        if a == b {
            return Ok((a.clone(), Formula::True, Formula::True));
        }
        match (a, b) {
            (
                Symbol::Union {
                    members: am,
                    active: ai,
                    payloads: av,
                },
                Symbol::Union {
                    members: bm,
                    active: bi,
                    payloads: bv,
                },
            ) if am == bm => {
                let members = am.clone();
                let active = self.fresh_union_tag(members.len())?;
                let mut left = equal(&active, ai)?;
                let mut right = equal(&active, bi)?;
                let mut payloads = Vec::with_capacity(members.len());
                for index in 0..members.len() {
                    match (&av[index], &bv[index]) {
                        (Some(a), Some(b)) => {
                            let (joined, a_relation, b_relation) = self.join_value(a, b, views)?;
                            left = left.and(
                                equal(ai, &Linear::number(index as i128))?
                                    .not()
                                    .or(a_relation),
                            );
                            right = right.and(
                                equal(bi, &Linear::number(index as i128))?
                                    .not()
                                    .or(b_relation),
                            );
                            payloads.push(Some(joined));
                        }
                        (Some(value), None) | (None, Some(value)) => {
                            payloads.push(Some(value.clone()))
                        }
                        (None, None) => payloads.push(None),
                    }
                }
                Ok((
                    Symbol::Union {
                        members,
                        active,
                        payloads,
                    },
                    left,
                    right,
                ))
            }
            (Symbol::Shape(a), Symbol::Shape(b)) if a == b => {
                Ok((Symbol::Shape(a.clone()), Formula::True, Formula::True))
            }
            (Symbol::Number(at, _), Symbol::Number(bt, _)) if at == bt => {
                let value = self.arbitrary(at)?;
                Ok((
                    value.clone(),
                    self.symbol_equal(&value, a)?,
                    self.symbol_equal(&value, b)?,
                ))
            }
            (Symbol::Bool(_), Symbol::Bool(_)) => {
                let value = self.arbitrary(&Ty::Bool)?;
                Ok((
                    value.clone(),
                    self.symbol_equal(&value, a)?,
                    self.symbol_equal(&value, b)?,
                ))
            }
            (Symbol::Ref(at, ar, ap), Symbol::Ref(bt, br, bp))
                if at == bt
                    && ar == br
                    && ap.len() == bp.len()
                    && !ap.is_empty()
                    && self.history_element(at) =>
            {
                let offset = ap
                    .iter()
                    .zip(bp)
                    .position(|(a, b)| a != b)
                    .ok_or("conditional reference paths unexpectedly coincide")?;
                let (Projection::Index(a), Projection::Index(b)) = (&ap[offset], &bp[offset])
                else {
                    return Err(
                        "conditional references require one differing array index and matching field paths"
                            .into(),
                    );
                };
                if ap[offset + 1..] != bp[offset + 1..]
                    || ap[offset + 1..]
                        .iter()
                        .any(|step| !matches!(step, Projection::Field(_)))
                {
                    return Err("conditional references require one differing array index and matching field paths".into());
                }
                let index = self.arbitrary(&Ty::Nat)?.number()?;
                let mut path = ap.clone();
                path[offset] = Projection::Index(index.clone());
                let value = Symbol::Ref(at.clone(), *ar, path);
                views.push(value.clone());
                Ok((value, equal(&index, a)?, equal(&index, b)?))
            }
            (Symbol::Record(an, a), Symbol::Record(bn, b)) if an == bn && a.len() == b.len() => {
                let mut fields = BTreeMap::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for (name, value) in a {
                    let (value, l, r) =
                        self.join_value(value, b.get(name).ok_or("branch fields differ")?, views)?;
                    fields.insert(name.clone(), value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((Symbol::Record(an.clone(), fields), left, right))
            }
            (
                Symbol::Array {
                    element,
                    len,
                    items: Some(a),
                    ..
                },
                Symbol::Array {
                    element: be,
                    len: bl,
                    items: Some(b),
                    ..
                },
            ) if element == be
                && len == bl
                && a.len() == b.len()
                && !self.history_element(element) =>
            {
                let mut values = Vec::new();
                let mut left = Formula::True;
                let mut right = Formula::True;
                for (a, b) in a.iter().zip(b) {
                    let (value, l, r) = self.join_value(a, b, views)?;
                    values.push(value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((
                    Symbol::Array {
                        element: element.clone(),
                        len: len.clone(),
                        items: Some(values),
                        cells: BTreeMap::new(),
                        identity: self.fresh_name(),
                    },
                    left,
                    right,
                ))
            }
            (
                Symbol::Array {
                    element,
                    len,
                    items: a_items,
                    cells: a_cells,
                    identity: a_id,
                },
                Symbol::Array {
                    element: b_element,
                    len: b_len,
                    items: b_items,
                    cells: b_cells,
                    identity: b_id,
                },
            ) if element == b_element && len == b_len && self.history_element(element) => {
                if a_id == b_id {
                    let mut cells = a_cells.clone();
                    for (index, value) in b_cells {
                        if cells.get(index).is_some_and(|existing| existing != value) {
                            return Err(
                                "inconsistent materialization of one array contents identity"
                                    .into(),
                            );
                        }
                        cells.insert(index.clone(), value.clone());
                    }
                    return Ok((
                        Symbol::Array {
                            element: element.clone(),
                            len: len.clone(),
                            items: a_items.clone(),
                            cells,
                            identity: a_id.clone(),
                        },
                        Formula::True,
                        Formula::True,
                    ));
                }
                let indices = a_cells
                    .keys()
                    .chain(b_cells.keys())
                    .cloned()
                    .chain(
                        (0..a_items.as_ref().map_or(0, Vec::len))
                            .map(|i| Linear::number(i as i128)),
                    )
                    .chain(
                        (0..b_items.as_ref().map_or(0, Vec::len))
                            .map(|i| Linear::number(i as i128)),
                    )
                    .collect::<BTreeSet<_>>();
                let condition = self.arbitrary(&Ty::Bool)?.proposition()?;
                let identity = self.fresh_name();
                self.arrays.history.insert(
                    identity.clone(),
                    ArrayHistory::Choice {
                        condition: condition.clone(),
                        left: a_id.clone(),
                        right: b_id.clone(),
                    },
                );
                let mut cells = BTreeMap::new();
                let mut left = condition.clone();
                let mut right = condition.not();
                for index in indices {
                    let a = a_items
                        .as_ref()
                        .and_then(|items| constant_index(&index).and_then(|i| items.get(i)))
                        .or_else(|| a_cells.get(&index));
                    let b = b_items
                        .as_ref()
                        .and_then(|items| constant_index(&index).and_then(|i| items.get(i)))
                        .or_else(|| b_cells.get(&index));
                    // Missing predecessor cells are read lazily under their
                    // history guard, never assumed outside their birth branch.
                    let (value, l, r) = match (a, b) {
                        (Some(a), Some(b)) => self.join_value(a, b, views)?,
                        (a, b) => {
                            let value = self.arbitrary(element)?;
                            let l = match a {
                                Some(a) => self.symbol_equal(&value, a)?,
                                None => Formula::True,
                            };
                            let r = match b {
                                Some(b) => self.symbol_equal(&value, b)?,
                                None => Formula::True,
                            };
                            (value, l, r)
                        }
                    };
                    cells.insert(index, value);
                    left = left.and(l);
                    right = right.and(r);
                }
                Ok((
                    Symbol::Array {
                        element: element.clone(),
                        len: len.clone(),
                        items: None,
                        cells,
                        identity,
                    },
                    left,
                    right,
                ))
            }
            _ => Err(
                "conditional storage joins require matching layouts and stable references".into(),
            ),
        }
    }

    pub(super) fn symbol_equal(&self, a: &Symbol, b: &Symbol) -> Result<Formula> {
        if a == b {
            return Ok(Formula::True);
        }
        match (a, b) {
            (Symbol::Shape(a), Symbol::Shape(b)) => unions::type_equal(a, b),
            (Symbol::Type { .. }, Symbol::Type { .. }) => unions::observations_equal(a, b),
            (Symbol::Union { members: am, active: ai, payloads: av }, Symbol::Union { members: bm, active: bi, payloads: bv }) if am == bm => {
                let mut relation = equal(ai, bi)?;
                for (index, (a, b)) in av.iter().zip(bv).enumerate() {
                    if let (Some(a), Some(b)) = (a, b) { relation = relation.and(equal(ai, &Linear::number(index as i128))?.not().or(self.symbol_equal(a, b)?)); }
                }
                Ok(relation)
            }
            (Symbol::Number(_, a), Symbol::Number(_, b)) => equal(a, b),
            (Symbol::Bool(a), Symbol::Bool(b)) => Ok(a
                .clone()
                .and(b.clone())
                .or(a.clone().not().and(b.clone().not()))),
            (Symbol::Unit, Symbol::Unit) => Ok(Formula::True),
            (Symbol::Record(an, a), Symbol::Record(bn, b)) if an == bn && a.len() == b.len() => {
                let mut relation = Formula::True;
                for (field, value) in a {
                    let other = b.get(field).ok_or("conditional record fields differ")?;
                    relation = relation.and(self.symbol_equal(value, other)?);
                }
                Ok(relation)
            }
            _ => Err("conditional values need matching scalar or record fields; array and reference joins are not supported yet".into()),
        }
    }
}
