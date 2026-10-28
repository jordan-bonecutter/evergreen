//! A checked universal instance can describe an ordinary numeric read. This
//! frontend interpretation uses exact contents identities and observed indices;
//! it neither enumerates a range nor invents values for unobserved cells.

use super::*;

fn atom(formula: &Formula) -> Option<(&str, &[Linear], bool)> {
    match formula {
        Formula::Predicate { symbol, arguments } => Some((symbol, arguments, false)),
        Formula::Not(body) => match body.as_ref() {
            Formula::Predicate { symbol, arguments } => Some((symbol, arguments, true)),
            _ => None,
        },
        _ => None,
    }
}

impl Equality {
    fn matches_observation(&self, symbol: &str, arguments: &[Linear]) -> bool {
        self.symbol == symbol
            && arguments.len() == 2 + self.captures.len()
            && arguments[2..]
                .iter()
                .zip(&self.captures)
                .all(|(argument, capture)| *argument == Linear::variable(capture))
    }
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn observe_array_values(
        &mut self,
        identity: &str,
        index: &Linear,
        value: &Symbol,
    ) -> Result<()> {
        let Symbol::Number(_, observed) = value else {
            return Ok(());
        };
        if self.arrays.value_equality_origins.is_empty() {
            return Ok(());
        }
        let candidates = self
            .proof
            .claims
            .iter()
            .copied()
            .chain(self.proof.witnesses.values().copied())
            .collect::<BTreeSet<_>>();
        self.charge_value_work(candidates.len())?;
        for theorem in candidates {
            self.charge_value_work(self.proof.evidence.claim(theorem)?.storage_weight()?)?;
            let Formula::Forall { variable, body, .. } =
                self.proof.evidence.claim(theorem)?.clone()
            else {
                continue;
            };
            let mut pending = vec![(&*body, Vec::new())];
            while let Some((part, path)) = pending.pop() {
                self.charge_value_work(1 + path.len())?;
                if let Formula::And(left, right) = part {
                    let mut a = path.clone();
                    a.push(false);
                    let mut b = path;
                    b.push(true);
                    pending.push((left, a));
                    pending.push((right, b));
                    continue;
                }
                let Some((symbol, arguments, _)) = atom(part) else {
                    continue;
                };
                let Some(key) = self.arrays.value_equality_origins.get(symbol).cloned() else {
                    continue;
                };
                for (side, contents) in [&key.0, &key.1].into_iter().enumerate() {
                    if contents.as_deref() != Some(identity) {
                        continue;
                    };
                    let Some(term) =
                        array_predicates::specialization_index(&arguments[side], index, &variable)?
                    else {
                        continue;
                    };
                    self.charge_value_work(part.storage_weight()?)?;
                    let claim = part.substitute(&variable, &term)?;
                    let Some(interpretation) =
                        self.observed_numeric_equality(&claim, &key, side, index, observed)?
                    else {
                        continue;
                    };
                    if self.checked_entails(&interpretation)? {
                        continue;
                    };
                    self.charge_value_work(body.storage_weight()?)?;
                    let instance = body.substitute(&variable, &term)?;
                    let Some(premise) =
                        self.checked_array_specialization(theorem, &term, &instance)?
                    else {
                        continue;
                    };
                    self.import_numeric_observation(claim, interpretation, premise, &path)?;
                }
            }
        }
        Ok(())
    }

    fn import_numeric_observation(
        &mut self,
        claim: Formula,
        interpretation: Formula,
        mut premise: evidence::NodeId,
        path: &[bool],
    ) -> Result<()> {
        for &right in path {
            let Formula::And(a, b) = self.proof.evidence.claim(premise)?.clone() else {
                return Err("numeric observation lost its conjunction path".into());
            };
            premise = self.proof.evidence.derive(
                if right { *b } else { *a },
                if right {
                    evidence::Rule::AndRight(premise)
                } else {
                    evidence::Rule::AndLeft(premise)
                },
            )?;
        }
        // This is the same trusted frontend boundary as ordinary
        // array reads: interpreting the exact version's payload.
        // The implication provides no fact without its premise.
        let relation = self.proof.evidence.contract(
            Formula::Implies(Box::new(claim), Box::new(interpretation.clone())),
            Vec::new(),
        )?;
        let fact = self.proof.evidence.derive(
            interpretation.clone(),
            evidence::Rule::ImpElim {
                theorem: relation,
                argument: premise,
            },
        )?;
        self.assume_from(&interpretation, paths::Origin::Evidence(fact))
    }

    fn observed_numeric_equality(
        &mut self,
        claim: &Formula,
        key: &Key,
        side: usize,
        index: &Linear,
        observed: &Linear,
    ) -> Result<Option<Formula>> {
        let Some((symbol, arguments, negated)) = atom(claim) else {
            return Ok(None);
        };
        let recipe = &self.arrays.value_equalities[key];
        // Definitions can be instantiated mathematically with different
        // captures. Only the original captures describe this storage version.
        if !recipe.matches_observation(symbol, arguments) {
            return Ok(None);
        }
        if arguments.len() < 2 || &arguments[side] != index {
            return Err("numeric observation does not match its array index".into());
        }
        let other = 1 - side;
        let contents = if other == 0 { &key.0 } else { &key.1 };
        let other_value = match contents {
            None => arguments[other].clone(),
            Some(contents) => {
                let Some(value) = self.captured_numeric_value(contents, &arguments[other])? else {
                    return Ok(None);
                };
                value
            }
        };
        let equality = equal(observed, &other_value)?;
        self.charge_value_work(equality.storage_weight()?)?;
        Ok(Some(if negated { equality.not() } else { equality }))
    }

    fn captured_numeric_value(&mut self, identity: &str, index: &Linear) -> Result<Option<Linear>> {
        let mut identity = identity.to_owned();
        loop {
            self.charge_value_work(
                identity
                    .len()
                    .saturating_add(index.terms.len())
                    .saturating_add(1),
            )?;
            let known = self
                .arrays
                .reads
                .get(&(identity.clone(), index.clone()))
                .and_then(|value| match value {
                    Symbol::Number(_, value) => Some(value),
                    _ => None,
                })
                .or_else(|| {
                    constant_index(index)
                        .and_then(|index| self.arrays.value_literals.get(&identity)?.get(index))
                });
            if let Some(value) = known {
                let value = value.clone();
                self.charge_value_work(value.terms.len() + 1)?;
                return Ok(Some(value));
            }
            match self.arrays.history.get(&identity) {
                Some(ArrayHistory::Fill(Symbol::Number(_, value))) => {
                    let value = value.clone();
                    self.charge_value_work(value.terms.len() + 1)?;
                    return Ok(Some(value));
                }
                Some(ArrayHistory::Store {
                    base,
                    index: written,
                    value,
                }) => {
                    if written == index {
                        let value = value.number()?;
                        self.charge_value_work(value.terms.len() + 1)?;
                        return Ok(Some(value));
                    }
                    // Different affine constants with identical terms cannot
                    // alias. Other relationships need a checked case proof.
                    if written.terms != index.terms {
                        return Ok(None);
                    };
                    identity = base.clone();
                }
                _ => return Ok(None),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rewritten_recipe_captures_do_not_describe_the_original_storage() {
        let recipe = Equality {
            symbol: "contents_equality".into(),
            captures: vec!["stored_value".into(), "store_index".into()],
        };
        let original = vec![
            Linear::number(3),
            Linear::number(42),
            Linear::variable("stored_value"),
            Linear::variable("store_index"),
        ];
        assert!(recipe.matches_observation("contents_equality", &original));
        for position in [2, 3] {
            let mut changed = original.clone();
            changed[position] = Linear::number(0);
            assert!(!recipe.matches_observation("contents_equality", &changed));
        }
        assert!(!recipe.matches_observation("another_equality", &original));
        assert!(!recipe.matches_observation("contents_equality", &original[..3]));
    }
}
