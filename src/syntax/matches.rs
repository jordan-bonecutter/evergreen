//! Exhaustive Boolean matching lowers to the ordinary checked conditional.
//! The scrutinee is evaluated once; type/ownership/effect rules stay shared.

use super::*;

impl Parser {
    pub(super) fn boolean_match(&mut self, line: usize) -> Result<Expr, String> {
        let condition = self.expr(0)?;
        self.expect("{")?;
        let mut yes = None;
        let mut no = None;
        let mut wildcard = false;
        while !self.eat("}") {
            if wildcard {
                return Err(self.err("unreachable match arm after _"));
            }
            let pattern = if self.eat("true") {
                Some(true)
            } else if self.eat("false") {
                Some(false)
            } else if self.eat("_") {
                None
            } else {
                return Err(self.err("match currently supports true, false, and _ patterns"));
            };
            if matches!(pattern, Some(true)) && yes.is_some()
                || matches!(pattern, Some(false)) && no.is_some()
            {
                return Err(self.err("duplicate Boolean match arm"));
            }
            if pattern.is_none() && yes.is_some() && no.is_some() {
                return Err(self.err("unreachable _ arm: true and false are already covered"));
            }
            self.expect("=>")?;
            let arm = if self.eat("{") {
                if self.eat("}") {
                    Expr {
                        kind: Kind::Unit,
                        line: self.line(),
                    }
                } else {
                    let value = self.expr(0)?;
                    if self.peek() == ";" {
                        return Err(self.err("match arm blocks currently take a single value expression; statement blocks need scope/cleanup support"));
                    }
                    self.expect("}")?;
                    value
                }
            } else {
                self.expr(0)?
            };
            match pattern {
                Some(true) => yes = Some(arm),
                Some(false) => no = Some(arm),
                None => {
                    wildcard = true;
                    if yes.is_none() {
                        yes = Some(arm.clone());
                    }
                    if no.is_none() {
                        no = Some(arm);
                    }
                }
            }
            if self.eat("}") {
                break;
            }
            self.expect(",")?;
        }
        let (Some(yes), Some(no)) = (yes, no) else {
            return Err(self.err("non-exhaustive Boolean match: cover true and false, or use _"));
        };
        Ok(Expr {
            kind: Kind::If(Box::new(condition), Box::new(yes), Box::new(no)),
            line,
        })
    }
}
