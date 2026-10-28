//! Scalar equalities are scoped predicates whose fixed term recipes expose all
//! free integers as parameters. Registration supplies a meaning, never evidence.

use super::*;
use crate::compiler::kernel::terms::{Id, Terms, Work};
use std::sync::Arc;

#[cfg(test)]
mod tests;

#[derive(Debug)]
struct Equality {
    terms: Arc<Terms>,
    parameters: Vec<String>,
    left: Id,
    right: Id,
}

#[derive(Debug, Default)]
pub(super) struct Definitions {
    equalities: BTreeMap<String, Equality>,
}

impl Evidence {
    // Source indexed-payload elaboration will register these recipes.
    #[allow(dead_code)]
    pub(super) fn define_scalar_equality(
        &mut self,
        symbol: String,
        parameters: Vec<String>,
        terms: Arc<Terms>,
        left: Id,
        right: Id,
    ) -> Result<DefinitionId> {
        let declaration_weight = parameters.iter().fold(symbol.len(), |cost, name| {
            cost.saturating_add(1 + name.len())
        });
        if declaration_weight > MAX_VALUE_WORK.saturating_sub(self.storage_weight) {
            return Err("scalar definition storage limit reached".into());
        }
        let names = parameters
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        let mut work = Work::new(MAX_VALUE_WORK - self.storage_weight - declaration_weight);
        let mut variables = terms.free_variables(left, &mut work)?;
        variables.extend(terms.free_variables(right, &mut work)?);
        if variables.iter().any(|name| !names.contains(name.as_str())) {
            return Err("scalar equalities must name every free variable as a parameter".into());
        }
        let id = self.declare_predicate(symbol.clone(), parameters.clone())?;
        self.storage_weight += work.spent();
        self.scalars.equalities.insert(
            symbol,
            Equality {
                terms,
                parameters,
                left,
                right,
            },
        );
        Ok(id)
    }

    fn scalar_sides(
        &self,
        claim: &Formula,
        scratch: &mut Terms,
        work: &mut Work,
    ) -> Result<Option<(Id, Id)>> {
        let Formula::Predicate { symbol, arguments } = claim else {
            return Ok(None);
        };
        let Some(definition) = self.scalars.equalities.get(symbol) else {
            return Ok(None);
        };
        if arguments.len() != definition.parameters.len() {
            return Err("scalar equality instance has the wrong arity".into());
        }
        work.charge(
            definition
                .parameters
                .iter()
                .fold(0usize, |cost, name| cost.saturating_add(1 + name.len())),
        )?;
        let roots = scratch.import(
            &definition.terms,
            &[definition.left, definition.right],
            work,
        )?;
        let mut bindings = BTreeMap::new();
        for (name, argument) in definition.parameters.iter().zip(arguments) {
            bindings.insert(name.clone(), import_linear(scratch, argument, work)?);
        }
        Ok(Some((
            scratch.substitute(roots[0], &bindings, work)?,
            scratch.substitute(roots[1], &bindings, work)?,
        )))
    }

    pub(super) fn scalar_reflexivity(
        &self,
        goal: &Formula,
        work: &mut usize,
        limit: usize,
    ) -> Result<bool> {
        let mut budget = Work::new(limit.saturating_sub(*work));
        let result = self
            .scalar_sides(goal, &mut Terms::new()?, &mut budget)
            .map(|sides| sides.is_some_and(|(left, right)| left == right));
        *work = work.saturating_add(budget.spent());
        result
    }

    pub(super) fn scalar_congruence(
        &self,
        goal: &Formula,
        equalities: &[NodeId],
        work: &mut usize,
        limit: usize,
    ) -> Result<bool> {
        let mut budget = Work::new(limit.saturating_sub(*work));
        let result = self.check_scalar_congruence(goal, equalities, &mut budget);
        *work = work.saturating_add(budget.spent());
        result
    }

    fn check_scalar_congruence(
        &self,
        goal: &Formula,
        equalities: &[NodeId],
        work: &mut Work,
    ) -> Result<bool> {
        let mut scratch = Terms::new()?;
        let Some((left, right)) = self.scalar_sides(goal, &mut scratch, work)? else {
            return Ok(false);
        };
        let left = scratch.application_parts(left, work)?;
        let right = scratch.application_parts(right, work)?;
        let (Some((a, aa)), Some((b, ba))) = (left, right) else {
            return Ok(false);
        };
        if a != b || aa.len() != ba.len() || aa.len() != equalities.len() {
            return Ok(false);
        }
        // Release the read view before importing parent equations into scratch.
        let pairs = aa
            .iter()
            .copied()
            .zip(ba.iter().copied())
            .collect::<Vec<_>>();
        for ((a, b), &parent) in pairs.into_iter().zip(equalities) {
            let claim = self.claim(parent)?;
            if let Some((from, to)) = self.scalar_sides(claim, &mut scratch, work)? {
                if (a, b) != (from, to) {
                    return Ok(false);
                }
            } else {
                let (Some(a), Some(b)) = (scratch.linear(a, work)?, scratch.linear(b, work)?)
                else {
                    return Ok(false);
                };
                if !claim.normalized().alpha_equal(&equal(&a, &b)?.normalized()) {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
}

fn import_linear(terms: &mut Terms, row: &Linear, work: &mut Work) -> Result<Id> {
    let mut result = terms.number(row.constant, work)?;
    for (name, coefficient) in &row.terms {
        let variable = terms.variable(name, work)?;
        let scaled = terms.scale(variable, *coefficient, work)?;
        result = terms.add(result, scaled, work)?;
    }
    Ok(result)
}
