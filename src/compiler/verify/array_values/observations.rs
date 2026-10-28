//! A checked universal instance can describe an ordinary scalar read. This
//! frontend interpretation uses exact contents identities and observed indices;
//! it never enumerates a range. Intermediate scalar leaves are queried lazily.

use super::*;

mod compound;
mod historical;

#[derive(Clone, Copy)]
struct Source {
    theorem: evidence::NodeId,
    world: Option<state::WorldId>,
}

struct Observation<'a> {
    identity: &'a str,
    index: &'a Linear,
    value: &'a Symbol,
    fields: &'a [String],
}

impl Observation<'_> {
    fn project<'v>(&'v self, contents: &Contents) -> Result<Option<&'v Symbol>> {
        if contents.identity != self.identity || !contents.fields.starts_with(self.fields) {
            return Ok(None);
        }
        let suffix = Contents {
            identity: contents.identity.clone(),
            fields: contents.fields[self.fields.len()..].to_vec(),
        };
        suffix.project(self.value).map(Some)
    }
}

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
        if self.arrays.value_equality_origins.is_empty() {
            return Ok(());
        }
        let observed = Observation {
            identity,
            index,
            value,
            fields: &[],
        };
        self.observe_values(&observed, None)
    }

    fn observe_values(
        &mut self,
        observed: &Observation<'_>,
        world: Option<state::WorldId>,
    ) -> Result<()> {
        let candidates = if let Some(world) = world {
            let (candidates, work) = self.proof.subjects.historical_candidates(world)?;
            self.charge_value_work(work)?;
            candidates
                .intersection(&self.proof.claims)
                .copied()
                .collect()
        } else {
            self.proof
                .claims
                .iter()
                .copied()
                .chain(self.proof.witnesses.values().copied())
                .collect::<BTreeSet<_>>()
        };
        self.charge_value_work(candidates.len())?;
        for theorem in candidates {
            self.charge_value_work(self.proof.evidence.claim(theorem)?.storage_weight()?)?;
            let Formula::Forall { variable, body, .. } =
                self.proof.evidence.claim(theorem)?.clone()
            else {
                continue;
            };
            self.observe_compound_values(theorem, &variable, &body, observed, world)?;
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
                    let Some(contents) = contents.as_ref() else {
                        continue;
                    };
                    self.charge_value_work(contents.fields.len() + 1)?;
                    let Some(value) = observed.project(contents)? else {
                        continue;
                    };
                    if !scalar(&value.ty()) {
                        continue;
                    }
                    let Some(term) = array_predicates::specialization_index(
                        &arguments[side],
                        observed.index,
                        &variable,
                    )?
                    else {
                        continue;
                    };
                    self.charge_value_work(part.storage_weight()?)?;
                    let claim = part.substitute(&variable, &term)?;
                    self.charge_value_work(body.storage_weight()?)?;
                    let instance = body.substitute(&variable, &term)?;
                    // Validate the source before following any of its old-state
                    // dependencies. A stale or admitted range grants no lookup.
                    let Some(premise) =
                        self.checked_array_specialization_in(theorem, &term, &instance, world)?
                    else {
                        continue;
                    };
                    let Some(interpretation) = self.observed_scalar_equality(
                        &claim,
                        &key,
                        side,
                        observed.index,
                        value,
                        Source { theorem, world },
                    )?
                    else {
                        continue;
                    };
                    if self.checked_entails(&interpretation)? {
                        continue;
                    }
                    self.import_scalar_observation(claim, interpretation, premise, &path)?;
                }
            }
        }
        Ok(())
    }

    fn import_scalar_observation(
        &mut self,
        claim: Formula,
        interpretation: Formula,
        mut premise: evidence::NodeId,
        path: &[bool],
    ) -> Result<()> {
        for &right in path {
            let Formula::And(a, b) = self.proof.evidence.claim(premise)?.clone() else {
                return Err("scalar observation lost its conjunction path".into());
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

    fn observed_scalar_equality(
        &mut self,
        claim: &Formula,
        key: &Key,
        side: usize,
        index: &Linear,
        observed: &Symbol,
        source: Source,
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
            return Err("scalar observation does not match its array index".into());
        }
        let other = 1 - side;
        let contents = if other == 0 { &key.0 } else { &key.1 };
        let equality = match contents {
            None => self.scalar_word_equality(observed, &arguments[other])?,
            Some(contents) => {
                let Some(value) = self.captured_scalar_value(
                    contents,
                    &arguments[other],
                    &observed.ty(),
                    source,
                )?
                else {
                    return Ok(None);
                };
                self.symbol_equal(observed, &value)?
            }
        };
        self.charge_value_work(equality.storage_weight()?)?;
        Ok(Some(if negated { equality.not() } else { equality }))
    }

    fn captured_scalar_value(
        &mut self,
        contents: &Contents,
        index: &Linear,
        ty: &Ty,
        source: Source,
    ) -> Result<Option<Symbol>> {
        let mut identity = contents.identity.clone();
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
                .or_else(|| {
                    constant_index(index)
                        .and_then(|index| self.arrays.value_literals.get(&identity)?.get(index))
                });
            if let Some(value) = known {
                let value = contents.project(value)?.clone();
                self.charge_value_work(symbol_weight(&value)?)?;
                return Ok(Some(value));
            }
            match self.arrays.history.get(&identity) {
                Some(ArrayHistory::Fill(value)) => {
                    let value = contents.project(value)?.clone();
                    self.charge_value_work(symbol_weight(&value)?)?;
                    return Ok(Some(value));
                }
                Some(ArrayHistory::Store {
                    base,
                    index: written,
                    value,
                }) => {
                    if written == index {
                        let value = contents.project(value)?.clone();
                        self.charge_value_work(symbol_weight(&value)?)?;
                        return Ok(Some(value));
                    }
                    // Different affine constants with identical terms cannot
                    // alias. Other relationships need a checked case proof.
                    if written.terms != index.terms {
                        return Ok(None);
                    };
                    identity = base.clone();
                }
                None if !self.arrays.value_literals.contains_key(&identity) => {
                    return self
                        .historical_scalar_value(
                            &contents.with_identity(identity),
                            index,
                            ty,
                            source,
                        )
                        .map(Some);
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
