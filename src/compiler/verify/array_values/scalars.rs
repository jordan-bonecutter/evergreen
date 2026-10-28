//! Numeric words and Boolean truth values share equality histories. Boolean
//! inputs have a registered zero-or-one word; compound propositions retain
//! their formula and are split into true/false cases without a guessed value.

use super::*;

pub(super) enum Argument {
    Word(Linear),
    Boolean(Formula),
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn boolean_word(&self, predicate: &Formula) -> Option<Linear> {
        match predicate {
            Formula::True => Some(Linear::number(1)),
            Formula::False => Some(Linear::number(0)),
            _ => self.arrays.boolean_words.get(predicate).cloned(),
        }
    }

    pub(in crate::compiler::verify) fn boolean_value_equality(
        &self,
        a: &Formula,
        b: &Formula,
    ) -> Result<Formula> {
        if let (Some(a), Some(b)) = (self.boolean_word(a), self.boolean_word(b)) {
            return equal(&a, &b);
        }
        Ok(a.clone()
            .and(b.clone())
            .or(a.clone().not().and(b.clone().not())))
    }
    pub(super) fn scalar_argument(&self, value: &Symbol) -> Result<Argument> {
        match value {
            Symbol::Number(_, value) => Ok(Argument::Word(value.clone())),
            Symbol::Bool(Formula::True) => Ok(Argument::Word(Linear::number(1))),
            Symbol::Bool(Formula::False) => Ok(Argument::Word(Linear::number(0))),
            Symbol::Bool(predicate) => Ok(match self.arrays.boolean_words.get(predicate) {
                Some(word) => Argument::Word(word.clone()),
                None => Argument::Boolean(predicate.clone()),
            }),
            _ => Err("array payload equality requires a numeric or Boolean scalar".into()),
        }
    }

    pub(super) fn scalar_argument_cases(
        &mut self,
        value: &Argument,
        mut compare: impl FnMut(&mut Self, &Linear) -> Result<Formula>,
    ) -> Result<Formula> {
        match value {
            Argument::Word(word) => {
                self.charge_value_work(word.terms.len() + 1)?;
                compare(self, word)
            }
            Argument::Boolean(predicate) => {
                self.charge_value_work(predicate.storage_weight()?)?;
                let when_true = compare(self, &Linear::number(1))?;
                let when_false = compare(self, &Linear::number(0))?;
                Ok(predicate
                    .clone()
                    .and(when_true)
                    .or(predicate.clone().not().and(when_false)))
            }
        }
    }

    pub(super) fn scalar_word_equality(&self, value: &Symbol, word: &Linear) -> Result<Formula> {
        match value {
            Symbol::Number(_, value) => equal(value, word),
            Symbol::Bool(predicate) => {
                if let Some(value) = self.boolean_word(predicate) {
                    return equal(&value, word);
                }
                // A rewritten predicate argument need not be zero or one.
                // In that case both branches are false, rather than treating
                // every non-one argument as Boolean false.
                Ok(predicate
                    .clone()
                    .and(equal(word, &Linear::number(1))?)
                    .or(predicate
                        .clone()
                        .not()
                        .and(equal(word, &Linear::number(0))?)))
            }
            _ => Err("scalar observation requires a numeric or Boolean value".into()),
        }
    }
}
