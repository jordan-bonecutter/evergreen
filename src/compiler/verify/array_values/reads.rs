//! Demand-driven equations for ordinary reads of an opaque scalar input.
//! Only fresh read scalars are named; literals and stores retain their existing
//! definitions. One observed index never supplies a default for other cells.

use super::*;

#[derive(Clone)]
pub(in crate::compiler::verify) struct ReadBinding {
    value: Linear,
    definition: evidence::BindingId,
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn bind_scalar_array_read(
        &mut self,
        identity: &str,
        index: &Linear,
        value: &Symbol,
    ) -> Result<()> {
        if self.arrays.history.contains_key(identity)
            || self.arrays.value_literals.contains_key(identity)
        {
            return Ok(());
        }
        if !scalar(&value.ty()) {
            return Ok(());
        }
        let scalars::Argument::Word(value) = self.scalar_argument(value)? else {
            return Err("new scalar array reads require a registered word".into());
        };
        let Some((name, 1)) = value.terms.iter().next() else {
            return Ok(());
        };
        if value.constant != 0 || value.terms.len() != 1 {
            return Err("scalar array read must allocate a fresh scalar".into());
        }
        let mut terms = Terms::new()?;
        let mut work = Work::new(MAX_VALUE_WORK.saturating_sub(self.work.value_work));
        let mut argument = terms.number(index.constant, &mut work)?;
        for (name, coefficient) in &index.terms {
            let variable = terms.variable(name, &mut work)?;
            let scaled = terms.scale(variable, *coefficient, &mut work)?;
            argument = terms.add(argument, scaled, &mut work)?;
        }
        let read = terms.application(
            &format!("array_contents:{identity}"),
            &[argument],
            &mut work,
        )?;
        self.charge_value_work(work.spent())?;
        let definition = self
            .proof
            .evidence
            .define_scalar_binding(name.clone(), terms, read)?;
        self.arrays
            .scalar_bindings
            .entry(identity.to_owned())
            .or_default()
            .insert(
                index.clone(),
                ReadBinding {
                    value: value.clone(),
                    definition,
                },
            );
        Ok(())
    }

    pub(super) fn prove_scalar_read_binding(
        &mut self,
        goal: &Formula,
        key: &Key,
    ) -> Result<Option<evidence::NodeId>> {
        let (identity, side) = match key {
            (Some(identity), None) => (identity, 0),
            (None, Some(identity)) => (identity, 1),
            _ => return Ok(None),
        };
        let Formula::Predicate { symbol, arguments } = goal else {
            return Ok(None);
        };
        // History definitions are handled by checked unfolding, never by an
        // equation for a different version or a rewritten set of captures.
        if arguments.len() != 2 || self.arrays.predicate_definitions.contains_key(symbol) {
            return Ok(None);
        }
        let Some(bindings) = self.arrays.scalar_bindings.get(identity) else {
            return Ok(None);
        };
        let weight = bindings.iter().fold(0usize, |cost, (index, binding)| {
            cost.saturating_add(index.terms.len() + binding.value.terms.len() + 2)
        });
        self.charge_value_work(weight)?;
        let bindings = self.arrays.scalar_bindings[identity].clone();
        for (index, binding) in bindings {
            let mut actual = vec![index, binding.value];
            if side == 1 {
                actual.swap(0, 1);
            }
            let mut equalities = Vec::new();
            for (from, to) in actual.iter().zip(arguments) {
                let Some(proof) = self.reduce_selector_formula(&equal(from, to)?, 0)? else {
                    break;
                };
                equalities.push(proof);
            }
            if equalities.len() != 2 {
                continue;
            }
            let premise = self.proof.evidence.derive(
                Formula::Predicate {
                    symbol: symbol.clone(),
                    arguments: actual,
                },
                evidence::Rule::ScalarBinding(binding.definition),
            )?;
            return self
                .proof
                .evidence
                .derive(
                    goal.clone(),
                    evidence::Rule::PredicateCongruence {
                        source: premise,
                        equalities,
                    },
                )
                .map(Some);
        }
        Ok(None)
    }
}
