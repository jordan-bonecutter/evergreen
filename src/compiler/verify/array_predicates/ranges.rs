//! A full-range type proof can describe unobserved slots without enumerating
//! them. Storage transitions require closed evidence without admissions.

use super::*;

impl Context<'_> {
    pub(in crate::compiler::verify) fn checked_array_member_range(
        &mut self,
        array: &Symbol,
        target: &Ty,
    ) -> Result<bool> {
        let Symbol::Array { len, identity, .. } = array else {
            return Err("array member range requires array storage".into());
        };
        self.ensure_type_selector(array, target, 0)?;
        let variable = self.fresh_name();
        let index = Linear::variable(&variable);
        let selector = &self.arrays.type_predicates[&(identity.clone(), target.clone())];
        let body = Formula::Predicate {
            symbol: selector.symbol.clone(),
            arguments: std::iter::once(index.clone())
                .chain(selector.captures.iter().map(Linear::variable))
                .collect(),
        };
        let goal = Formula::Forall {
            variable,
            domain: Box::new(
                Formula::Ge(index.clone())
                    .and(Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?)),
            ),
            body: Box::new(body),
        };
        let Some(proof) = self.reduce_selector_formula(&goal, 0)? else {
            return Ok(false);
        };
        if !self.unadmitted_evidence(proof)? || self.proof.evidence.check_closed(proof).is_err() {
            return Ok(false);
        }
        self.proof.uses.push(proof);
        Ok(true)
    }
}
