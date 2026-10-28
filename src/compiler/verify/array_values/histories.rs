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
}
