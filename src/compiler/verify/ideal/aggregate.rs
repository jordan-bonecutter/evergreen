//! Borrow immutable aggregate contents for the duration of a reduction. A read
//! follows only the demanded slot and exact history edges; it neither enumerates
//! capacity nor imports branch-local read-cache assumptions.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(super) enum Array<'a> {
    Stored(&'a Symbol),
    Bytes(&'a [u8]),
}

impl Array<'_> {
    pub(super) fn ty(&self) -> Ty {
        match self {
            Self::Stored(value) => value.ty(),
            Self::Bytes(bytes) => {
                Ty::Array(Box::new(byte_type()), Linear::number(bytes.len() as i128))
            }
        }
    }
}

fn byte_type() -> Ty {
    Ty::Machine(MachineInt::parse("u8").expect("u8 type"))
}

pub(super) fn select<'a>(
    context: &'a Context<'_>,
    budget: &mut Budget,
    array: Array<'a>,
    index: usize,
) -> Result<Option<Value<'a>>> {
    budget.tick()?;
    let source = match array {
        Array::Stored(source) => source,
        Array::Bytes(bytes) => {
            let byte = bytes
                .get(index)
                .ok_or("ideal definition evaluation indexed out of bounds")?;
            return Value::checked_number(byte_type(), i128::from(*byte)).map(Some);
        }
    };
    let Symbol::Array {
        len,
        items,
        cells,
        identity,
        ..
    } = source
    else {
        return Err("ideal array view requires array storage".into());
    };
    // A symbolic bound still needs a proof-aware selection term. This evaluator
    // does not use caller assumptions, including for bounds or alias decisions.
    if !len.terms.is_empty() {
        return Ok(None);
    }
    if index as i128 >= len.constant {
        return Err("ideal definition evaluation indexed out of bounds".into());
    }
    let key = Linear::number(index as i128);
    let value = items
        .as_ref()
        .and_then(|items| items.get(index))
        .or_else(|| cells.get(&key));
    let source = match value {
        Some(value) => Some(value),
        None => history_value(context, budget, identity, &key)?,
    };
    source
        .map(|source| Importer::new(context, budget).value(source, 0))
        .transpose()
        .map(Option::flatten)
}

fn history_value<'a>(
    context: &'a Context<'_>,
    budget: &mut Budget,
    mut identity: &'a str,
    index: &Linear,
) -> Result<Option<&'a Symbol>> {
    // Source construction makes histories acyclic. The work budget also bounds
    // traversal defensively, without recursive calls on the host stack.
    loop {
        budget.tick()?;
        match context.arrays.history.get(identity) {
            Some(ArrayHistory::Fill(value)) => return Ok(Some(value)),
            Some(ArrayHistory::Store {
                base,
                index: written,
                value,
            }) => {
                if written == index {
                    return Ok(Some(value));
                }
                if written.terms != index.terms {
                    return Ok(None);
                }
                identity = base;
            }
            Some(ArrayHistory::Choice {
                condition,
                left,
                right,
            }) => {
                budget.spend(condition.storage_weight()?)?;
                identity = match values::closed_boolean(condition) {
                    Some(true) => left,
                    Some(false) => right,
                    None => return Ok(None),
                };
            }
            // Empty slots have no data to read. Unknown inputs and cached
            // selections need checked observations, not invented default values.
            Some(ArrayHistory::Uninitialized(_)) | None => return Ok(None),
        }
    }
}
