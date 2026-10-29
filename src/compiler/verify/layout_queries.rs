//! Layout observations inspect a type in the specification phase. Dependent
//! bounds may be checked there, but cannot execute runtime effects.

use super::*;

impl Context<'_> {
    pub(super) fn layout_query(&mut self, name: &str, arguments: &[Expr]) -> Result<Symbol> {
        let [argument] = arguments else {
            return Err(format!("{name} requires one type argument"));
        };
        let ty = argument
            .literal_type_for(self.declarations.target.word_bits())
            .ok_or("layout queries require a type")?;
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let checked = self.resolve(&ty);
        self.execution.phase = phase;
        checked?;
        let value = crate::compiler::layout::query::value_for(
            self.declarations.target,
            name,
            arguments,
            self.declarations.structs,
        )?;
        Ok(Symbol::Number(
            Ty::Machine(self.declarations.target.integer("usize").unwrap()),
            Linear::number(value as i128),
        ))
    }
}
