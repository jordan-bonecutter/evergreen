//! Acyclic definitional extensions of the logical language. Every free integer
//! must be an explicit parameter; definitions cannot assert propositions as axioms.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug)]
pub(in crate::compiler::verify) struct DefinitionId(usize);

#[derive(Debug)]
struct Definition {
    symbol: String,
    parameters: Vec<String>,
    body: Formula,
}

#[derive(Debug, Default)]
pub(super) struct Definitions {
    entries: Vec<Definition>,
    symbols: BTreeMap<String, DefinitionId>,
}

impl Evidence {
    pub(in crate::compiler::verify) fn define_predicate(
        &mut self,
        symbol: String,
        parameters: Vec<String>,
        body: Formula,
    ) -> Result<DefinitionId> {
        let weight = parameters.iter().fold(
            body.storage_weight()?.saturating_add(symbol.len()),
            |weight, name| weight.saturating_add(1 + name.len()),
        );
        if symbol.is_empty() || self.definitions.symbols.contains_key(&symbol) {
            return Err("predicate definitions require a fresh nonempty symbol".into());
        }
        if weight > MAX_VALUE_WORK.saturating_sub(self.storage_weight) {
            return Err("predicate definition storage limit reached".into());
        }
        let names = parameters
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        if names.len() != parameters.len()
            || names.iter().any(|name| name.is_empty() || name.len() > 256)
        {
            return Err("predicate parameters must have distinct valid names".into());
        }
        if body
            .free_variables()?
            .iter()
            .any(|name| !names.contains(name.as_str()))
        {
            return Err(
                "predicate definitions must name every free variable as a parameter".into(),
            );
        }
        let mut pending = vec![&body];
        while let Some(part) = pending.pop() {
            match part {
                Formula::Predicate { symbol, arguments } => {
                    let prior = self
                        .definitions
                        .symbols
                        .get(symbol)
                        .and_then(|id| self.definitions.entries.get(id.0))
                        .ok_or("predicate definitions may only reference earlier definitions")?;
                    if arguments.len() != prior.parameters.len() {
                        return Err("predicate definition dependency has the wrong arity".into());
                    }
                }
                Formula::Not(p) => pending.push(p),
                Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) => {
                    pending.push(a);
                    pending.push(b);
                }
                Formula::Forall { domain, body, .. } => {
                    pending.push(domain);
                    pending.push(body);
                }
                _ => {}
            }
        }
        let id = DefinitionId(self.definitions.entries.len());
        self.definitions.symbols.insert(symbol.clone(), id);
        self.definitions.entries.push(Definition {
            symbol,
            parameters,
            body,
        });
        self.storage_weight += weight;
        Ok(id)
    }

    pub(in crate::compiler::verify) fn predicate_definition(
        &self,
        id: DefinitionId,
        atom: &Formula,
        work: &mut usize,
        limit: usize,
    ) -> Result<Formula> {
        let definition = self
            .definitions
            .entries
            .get(id.0)
            .ok_or("missing predicate definition")?;
        let Formula::Predicate { symbol, arguments } = atom else {
            return Err("definition unfolding requires a predicate atom".into());
        };
        if symbol != &definition.symbol || arguments.len() != definition.parameters.len() {
            return Err("predicate definition symbol or arity does not match".into());
        }
        *work = work
            .saturating_add(definition.parameters.len())
            .saturating_add(atom.storage_weight()?);
        if *work > limit {
            return Err("predicate unfolding work limit reached".into());
        }
        let bindings = definition
            .parameters
            .iter()
            .zip(arguments)
            .map(|(name, value)| (name.as_str(), value))
            .collect();
        definition.body.substitute_counted(&bindings, work, limit)
    }
}
