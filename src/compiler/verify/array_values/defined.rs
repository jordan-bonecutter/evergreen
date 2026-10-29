//! Reduce only immutable array definitions. Observed cells, branch assumptions,
//! admissions, and arithmetic guesses cannot supply defaults for other elements.

use super::*;

#[cfg(test)]
mod tests;

impl Context<'_> {
    pub(in crate::compiler::verify) fn defined_array_read(
        &mut self,
        identity: &str,
        index: &Linear,
    ) -> Result<Option<Symbol>> {
        let contents = Contents {
            whole: false,
            identity: identity.into(),
            fields: Vec::new(),
        };
        self.defined_array_value(&contents, Some(index), 0)
    }

    // No index asks for a value shared by the entire range. With an index,
    // definite stores and explicit literals can supply their captured value.
    // Unknown aliases or branch choices reduce only if both values are identical.
    pub(super) fn defined_array_value(
        &mut self,
        contents: &Contents,
        index: Option<&Linear>,
        depth: usize,
    ) -> Result<Option<Symbol>> {
        self.charge_value_work(1)?;
        if depth >= 64 {
            return Err("array history read depth limit reached (64)".into());
        }
        let captured = match self.arrays.history.get(&contents.identity) {
            Some(ArrayHistory::Fill(value) | ArrayHistory::Store { value, .. }) => {
                Some(contents.project(value)?)
            }
            _ => None,
        };
        if let Some(value) = captured {
            self.charge_value_work(symbol_weight(value)?)?;
        }
        match self.arrays.history.get(&contents.identity) {
            Some(ArrayHistory::Fill(value)) => Ok(Some(contents.project(value)?.clone())),
            Some(ArrayHistory::Store {
                base,
                index: written,
                value,
            }) => {
                let same = index.is_some_and(|index| index == written);
                let different = index.is_some_and(|index| {
                    index.terms == written.terms && index.constant != written.constant
                });
                let base = contents.with_identity(base.clone());
                let value = contents.project(value)?.clone();
                if same {
                    return Ok(Some(value));
                }
                let previous = self.defined_array_value(&base, index, depth + 1)?;
                Ok(if different {
                    previous
                } else {
                    previous.filter(|previous| previous == &value)
                })
            }
            Some(ArrayHistory::Choice { left, right, .. }) => {
                let left = contents.with_identity(left.clone());
                let right = contents.with_identity(right.clone());
                let Some(left) = self.defined_array_value(&left, index, depth + 1)? else {
                    return Ok(None);
                };
                Ok(self
                    .defined_array_value(&right, index, depth + 1)?
                    .filter(|right| right == &left))
            }
            Some(ArrayHistory::Uninitialized(_)) => Ok(None),
            None => {
                let Some(values) = self.arrays.value_literals.get(&contents.identity) else {
                    return Ok(None);
                };
                if let Some(index) = index.filter(|index| index.terms.is_empty()) {
                    let Some(index) = constant_index(index) else {
                        return Ok(None);
                    };
                    let value = values
                        .get(index)
                        .map(|value| contents.project(value))
                        .transpose()?;
                    let weight = value.map(symbol_weight).transpose()?.unwrap_or(0);
                    self.charge_value_work(weight)?;
                    return self.arrays.value_literals[&contents.identity]
                        .get(index)
                        .map(|value| contents.project(value).cloned())
                        .transpose();
                }
                let weight = values_weight(values.iter())?;
                self.charge_value_work(weight)?;
                let values = &self.arrays.value_literals[&contents.identity];
                let Some(first) = values.first() else {
                    return Ok(None);
                };
                let first = contents.project(first)?;
                for value in values {
                    if contents.project(value)? != first {
                        return Ok(None);
                    };
                }
                Ok(Some(first.clone()))
            }
        }
    }
}
