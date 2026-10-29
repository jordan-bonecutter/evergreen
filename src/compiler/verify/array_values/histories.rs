//! Equality definitions follow immutable stores and joins. Captured indices,
//! values, and guards remain explicit predicate arguments, including under forall.

use super::*;

impl Context<'_> {
    pub(in crate::compiler::verify) fn remember_scalar_literal(
        &mut self,
        array: &Symbol,
    ) -> Result<()> {
        let Symbol::Array {
            element,
            identity,
            items: Some(items),
            ..
        } = array
        else {
            return Ok(());
        };
        if !self.history_element(element)
            || self.arrays.value_literals.contains_key(identity)
            || self.arrays.history.contains_key(identity)
        {
            return Ok(());
        }
        self.charge_value_work(values_weight(items.iter())?)?;
        self.arrays
            .value_literals
            .insert(identity.clone(), items.clone());
        Ok(())
    }

    pub(super) fn value_equality(
        &mut self,
        key: &Key,
        left: &Linear,
        right: &Linear,
        depth: usize,
    ) -> Result<Formula> {
        // Equality is symmetric. Keep one definition for both operand orders,
        // including record projections elaborated by same_value.
        if key.0 > key.1 {
            return self.value_equality(&(key.1.clone(), key.0.clone()), right, left, depth);
        }
        self.charge_value_work(1)?;
        if depth >= 64 {
            return Err("array value equality history depth limit reached".into());
        }
        if key.0.is_none() && key.1.is_none() {
            return equal(left, right);
        }
        if !self.arrays.value_equalities.contains_key(key) {
            // Identical contents retain constant-size congruence, independent
            // of the number of writes preceding this observation.
            let recipe = if key.0 == key.1 {
                self.declare_value_equality(key)?
            } else {
                let a = self.fresh_name();
                let b = self.fresh_name();
                match self.value_equality_body(
                    key,
                    &Linear::variable(&a),
                    &Linear::variable(&b),
                    depth,
                )? {
                    Some(body) => {
                        self.charge_value_work(body.storage_weight()?)?;
                        let captures = body
                            .free_variables()?
                            .into_iter()
                            .filter(|name| name != &a && name != &b)
                            .collect::<Vec<_>>();
                        let parameters =
                            [a, b].into_iter().chain(captures.iter().cloned()).collect();
                        let symbol = self.fresh_name();
                        let definition = self.proof.evidence.define_predicate(
                            symbol.clone(),
                            parameters,
                            body,
                        )?;
                        self.arrays
                            .predicate_definitions
                            .insert(symbol.clone(), definition);
                        Equality { symbol, captures }
                    }
                    None => self.declare_value_equality(key)?,
                }
            };
            self.arrays
                .value_equality_origins
                .insert(recipe.symbol.clone(), key.clone());
            for contents in [&key.0, &key.1].into_iter().flatten() {
                self.arrays
                    .value_predicates
                    .entry(contents.identity.clone())
                    .or_default()
                    .insert(recipe.symbol.clone());
            }
            self.arrays.value_equalities.insert(key.clone(), recipe);
        }
        let recipe = &self.arrays.value_equalities[key];
        Ok(Formula::Predicate {
            symbol: recipe.symbol.clone(),
            arguments: [left.clone(), right.clone()]
                .into_iter()
                .chain(recipe.captures.iter().map(Linear::variable))
                .collect(),
        })
    }

    fn value_equality_body(
        &mut self,
        key: &Key,
        left: &Linear,
        right: &Linear,
        depth: usize,
    ) -> Result<Option<Formula>> {
        if key.0.as_ref().is_some_and(|value| value.whole)
            || key.1.as_ref().is_some_and(|value| value.whole)
        {
            return self.whole_value_equality_body(key, left, right, depth);
        }
        for (side, contents) in [&key.0, &key.1].into_iter().enumerate() {
            let Some(contents) = contents else { continue };
            let identity = &contents.identity;
            let history = self.arrays.history.get(identity);
            if let Some(history) = history {
                let cost = match history {
                    ArrayHistory::Fill(value) | ArrayHistory::Uninitialized(value) => {
                        symbol_weight(value)?
                    }
                    ArrayHistory::Store { index, value, .. } => {
                        symbol_weight(value)?.saturating_add(index.terms.len() + 1)
                    }
                    ArrayHistory::Choice { condition, .. } => condition.storage_weight()?,
                };
                self.charge_value_work(cost)?;
            }
            let history = self.arrays.history.get(identity).cloned();
            let selected = if side == 0 { left } else { right };
            let compare = |ctx: &mut Self, contents: Option<Contents>, value: &Linear| {
                if side == 0 {
                    ctx.value_equality(&(contents, key.1.clone()), value, right, depth + 1)
                } else {
                    ctx.value_equality(&(key.0.clone(), contents), left, value, depth + 1)
                }
            };
            let compare_scalar = |ctx: &mut Self, value: &Symbol| {
                let argument = ctx.scalar_argument(contents.project(value)?)?;
                ctx.scalar_argument_cases(&argument, |ctx, word| compare(ctx, None, word))
            };
            let body = match history {
                Some(ArrayHistory::Fill(value)) => compare_scalar(self, &value)?,
                Some(ArrayHistory::Store { base, index, value }) => {
                    let same = equal(selected, &index)?;
                    let stored = compare_scalar(self, &value)?;
                    let previous = compare(self, Some(contents.with_identity(base)), selected)?;
                    same.clone().and(stored).or(same.not().and(previous))
                }
                Some(ArrayHistory::Choice {
                    condition,
                    left,
                    right,
                }) => {
                    let a = compare(self, Some(contents.with_identity(left)), selected)?;
                    let b = compare(self, Some(contents.with_identity(right)), selected)?;
                    condition.clone().and(a).or(condition.not().and(b))
                }
                Some(ArrayHistory::Uninitialized(_)) => {
                    return Err("scalar payload equality cannot read uninitialized storage".into())
                }
                None => {
                    let Some(values) = self.arrays.value_literals.get(identity) else {
                        continue;
                    };
                    let weight = values_weight(values.iter())?;
                    self.charge_value_work(weight)?;
                    let values = self.arrays.value_literals[identity].clone();
                    let mut alternatives = Vec::with_capacity(values.len());
                    for (index, value) in values.iter().enumerate() {
                        let body = compare_scalar(self, value)?;
                        alternatives
                            .push(equal(selected, &Linear::number(index as i128))?.and(body));
                    }
                    array_predicates::combine(alternatives, false)
                }
            };
            return Ok(Some(body));
        }
        Ok(None)
    }
    // A write changes exactly one logical element. At that index, leave the
    // equality uninterpreted until a checked value-transfer recipe supplies it.
    // Elsewhere, recurse into the immutable prior contents without reading cells.
    fn whole_value_equality_body(
        &mut self,
        key: &Key,
        left: &Linear,
        right: &Linear,
        depth: usize,
    ) -> Result<Option<Formula>> {
        let mut sides = [0, 1];
        if let (Some(a), Some(b)) = (&key.0, &key.1) {
            if !self.arrays.value_transfers.contains_key(&a.identity)
                && self.arrays.value_transfers.contains_key(&b.identity)
            {
                sides = [1, 0];
            }
            let mut ancestor = b.identity.clone();
            for _ in 0..64 {
                self.charge_value_work(1)?;
                if ancestor == a.identity {
                    sides = [1, 0];
                    break;
                }
                let Some((parent, _)) = self.whole_store(&ancestor) else {
                    break;
                };
                ancestor = parent;
            }
        }
        // A loop frame can relate an abstract entry version to an older
        // concrete array. Prefer unfolding toward that already-described
        // relation instead of expanding the concrete array's earlier stores.
        for side in sides {
            self.charge_value_work(1)?;
            let Some(contents) = (if side == 0 { &key.0 } else { &key.1 }) else {
                continue;
            };
            let Some((base, _)) = self.whole_store(&contents.identity) else {
                continue;
            };
            let mut previous = if side == 0 {
                (Some(contents.with_identity(base)), key.1.clone())
            } else {
                (key.0.clone(), Some(contents.with_identity(base)))
            };
            if previous.0 > previous.1 {
                previous = (previous.1, previous.0);
            }
            if self.arrays.value_equalities.contains_key(&previous) {
                sides = [side, 1 - side];
                break;
            }
        }
        for side in sides {
            let Some(contents) = (if side == 0 { &key.0 } else { &key.1 }) else {
                continue;
            };
            let Some((base, index)) = self.whole_store(&contents.identity) else {
                continue;
            };
            self.charge_value_work(1 + index.terms.len())?;
            let selected = if side == 0 { left } else { right };
            let same = equal(selected, &index)?;
            let changed = if let Some((source, at)) =
                self.arrays.value_transfers.get(&contents.identity).cloned()
            {
                self.charge_value_work(1 + at.terms.len())?;
                if side == 0 {
                    self.value_equality(
                        &(Some(contents.with_identity(source)), key.1.clone()),
                        &at,
                        right,
                        depth + 1,
                    )?
                } else {
                    self.value_equality(
                        &(key.0.clone(), Some(contents.with_identity(source))),
                        left,
                        &at,
                        depth + 1,
                    )?
                }
            } else {
                let recipe = self.declare_value_equality(key)?;
                Formula::Predicate {
                    symbol: recipe.symbol,
                    arguments: vec![left.clone(), right.clone()],
                }
            };
            let previous_key = if side == 0 {
                (Some(contents.with_identity(base)), key.1.clone())
            } else {
                (key.0.clone(), Some(contents.with_identity(base)))
            };
            let previous = self.value_equality(&previous_key, left, right, depth + 1)?;
            return Ok(Some(same.clone().and(changed).or(same.not().and(previous))));
        }
        Ok(None)
    }
    fn whole_store(&self, identity: &str) -> Option<(String, Linear)> {
        match self.arrays.history.get(identity) {
            Some(ArrayHistory::Store { base, index, .. }) => Some((base.clone(), index.clone())),
            _ => self.arrays.whole_stores.get(identity).cloned(),
        }
    }
}
