//! Closed selector definitions follow immutable contents versions. A store
//! changes one index and refers to the prior selector everywhere else.

use super::*;

impl Context<'_> {
    pub(super) fn ensure_type_selector(
        &mut self,
        array: &Symbol,
        target: &Ty,
        depth: usize,
    ) -> Result<()> {
        self.charge_value_work(symbol_weight(array)?)?;
        if depth >= 64 {
            return Err("array selector history depth limit reached".into());
        }
        let Symbol::Array {
            element,
            len,
            items,
            cells,
            identity,
        } = array
        else {
            return Err("array selector requires array storage".into());
        };
        let key = (identity.clone(), target.clone());
        if !self.arrays.type_predicates.contains_key(&key)
            && self.arrays.inputs.contains(identity)
            && matches!(element.as_ref(), Ty::Union(_))
            && items.is_none()
        {
            // An input array has no uniform default. Give its immutable
            // version an uninterpreted selector, never an invented type fact.
            // Sparse observations cannot define its unobserved remainder.
            let symbol = self.fresh_name();
            self.proof
                .evidence
                .declare_predicate(symbol.clone(), vec!["index".into()])?;
            self.arrays.type_predicates.insert(
                key.clone(),
                Selector {
                    symbol,
                    captures: Vec::new(),
                },
            );
        }
        if !self.arrays.type_predicates.contains_key(&key)
            && matches!(element.as_ref(), Ty::Union(_))
        {
            if let Some(ArrayHistory::Store { index, value, .. }) =
                self.arrays.history.get(identity)
            {
                self.charge_value_work(symbol_weight(value)?.saturating_add(index.terms.len()))?;
                let Some(ArrayHistory::Store { base, index, value }) =
                    self.arrays.history.get(identity).cloned()
                else {
                    return Err("missing array selector store recipe".into());
                };
                let parent = Symbol::Array {
                    element: element.clone(),
                    len: len.clone(),
                    items: None,
                    cells: BTreeMap::new(),
                    identity: base.clone(),
                };
                self.ensure_type_selector(&parent, target, depth + 1)?;
                let variable = "evg_selector_index";
                let input = Linear::variable(variable);
                let previous = self
                    .arrays
                    .type_predicates
                    .get(&(base, target.clone()))
                    .ok_or("missing checked parent array selector")?;
                let previous = Formula::Predicate {
                    symbol: previous.symbol.clone(),
                    arguments: std::iter::once(input.clone())
                        .chain(previous.captures.iter().map(Linear::variable))
                        .collect(),
                };
                let same = equal(&input, &index)?;
                let body = Formula::Ge(input.clone())
                    .and(Formula::Ge(len.sub(&input)?.add(&Linear::number(-1))?))
                    .and(
                        same.clone()
                            .and(member(&value, target)?)
                            .or(same.not().and(previous)),
                    );
                self.define_type_selector(identity, target, variable, body)?;
                return Ok(());
            }
        }
        if !self.arrays.type_predicates.contains_key(&key) {
            let initial = match self.arrays.history.get(identity) {
                Some(ArrayHistory::Uninitialized(value) | ArrayHistory::Fill(value)) => {
                    Some(member(value, target)?)
                }
                _ if !matches!(element.as_ref(), Ty::Union(_)) => {
                    Some(unions::type_equal(element, target)?)
                }
                _ => None,
            };
            let variable = "evg_selector_index";
            let input = Linear::variable(variable);
            let mut exclusions = Vec::new();
            let mut alternatives = Vec::new();
            let mut visit = |at: &Linear, value: &Symbol| -> Result<()> {
                let matches = member(value, target)?;
                // Read observations matching the uniform default add no exception.
                if initial.as_ref() == Some(&matches) {
                    return Ok(());
                }
                let same = equal(&input, at)?;
                exclusions.push(same.clone().not());
                alternatives.push(same.and(matches));
                Ok(())
            };
            if let Some(items) = items {
                // Literal elements are already explicit data; no capacity is enumerated.
                for (i, value) in items.iter().enumerate() {
                    visit(&Linear::number(i as i128), value)?;
                }
            }
            for (at, value) in cells {
                visit(at, value)?;
            }
            let default = match initial {
                Some(initial) => initial,
                None if items.is_some() => Formula::False,
                None => return Err("indexed union predicates need an input, a known default, literal elements, or a recorded store; join summaries remain unfinished".into()),
            };
            alternatives.push(default.and(combine(exclusions, true)));
            let body = Formula::Ge(input.clone())
                .and(Formula::Ge(len.sub(&input)?.add(&Linear::number(-1))?))
                .and(combine(alternatives, false));
            self.define_type_selector(identity, target, variable, body)?;
        }
        Ok(())
    }

    fn define_type_selector(
        &mut self,
        identity: &str,
        target: &Ty,
        variable: &str,
        body: Formula,
    ) -> Result<()> {
        self.charge_value_work(body.storage_weight()?)?;
        let captures = body
            .free_variables()?
            .into_iter()
            .filter(|name| name != variable)
            .collect::<Vec<_>>();
        let parameters = std::iter::once(variable.to_owned())
            .chain(captures.iter().cloned())
            .collect();
        let symbol = self.fresh_name();
        let definition = self
            .proof
            .evidence
            .define_predicate(symbol.clone(), parameters, body)?;
        self.arrays
            .predicate_definitions
            .insert(symbol.clone(), definition);
        self.arrays.type_predicates.insert(
            (identity.to_owned(), target.clone()),
            Selector { symbol, captures },
        );
        Ok(())
    }
}
