//! Matching lowers to ordinary checked conditionals and complete destructuring.
//! The scrutinee is evaluated once; type/ownership/effect rules stay shared.

use super::*;

impl Parser {
    pub(super) fn match_expression(&mut self, line: usize) -> Result<Expr, String> {
        // Source names cannot use the evg_ prefix; token positions keep nested
        // lowered matches distinct without exposing a new runtime construct.
        let temporary = format!("evg_match_{}", self.pos);
        let condition = self.expr(0)?;
        self.expect("{")?;
        if matches!(self.peek(), "true" | "false" | "_") {
            self.boolean_match(condition, line)
        } else if self.peek().starts_with(|ch: char| ch.is_ascii_alphabetic()) {
            self.record_match(condition, line)
        } else {
            self.integer_match(condition, temporary, line)
        }
    }

    // Shared with let patterns and Drop receivers. Call after the opening brace.
    pub(super) fn pattern_fields(&mut self) -> Result<Vec<(String, String)>, String> {
        let mut fields = Vec::new();
        while !self.eat("}") {
            let field = self.name()?;
            let binding = if self.eat(":") {
                self.name()?
            } else {
                field.clone()
            };
            fields.push((field, binding));
            if self.eat("}") {
                break;
            }
            self.expect(",")?;
        }
        Ok(fields)
    }

    fn record_match(&mut self, value: Expr, line: usize) -> Result<Expr, String> {
        let mut record = self.name()?;
        let mut arguments = Vec::new();
        while self.eat("::") {
            if self.peek() == "<" {
                arguments = self.generic_arguments()?;
                break;
            }
            record.push_str("::");
            record.push_str(&self.name()?);
        }
        self.expect("{")?;
        let fields = self.pattern_fields()?;
        self.expect("=>")?;
        let arm = if self.peek() == "{" {
            self.block_expression()?
        } else {
            self.expr(0)?
        };
        self.eat(",");
        if !self.eat("}") {
            return Err(self.err(
                "a complete record pattern covers the input; additional arms are unreachable",
            ));
        }
        Ok(Expr {
            kind: Kind::Block(
                vec![Statement::Destructure {
                    record,
                    arguments,
                    fields,
                    value,
                }],
                Box::new(arm),
            ),
            line,
        })
    }

    fn boolean_match(&mut self, condition: Expr, line: usize) -> Result<Expr, String> {
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
            let arm = if self.peek() == "{" {
                self.block_expression()?
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

    fn integer_match(
        &mut self,
        value: Expr,
        temporary: String,
        line: usize,
    ) -> Result<Expr, String> {
        let mut arms = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        let mut fallback = None;
        while !self.eat("}") {
            if fallback.is_some() {
                return Err(self.err("unreachable match arm after _"));
            }
            let arm_line = self.line();
            let pattern = if self.eat("_") {
                None
            } else {
                let negative = self.eat("-");
                let digits = self.peek();
                if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
                    return Err(self.err("expected an integer literal or _ match pattern"));
                }
                let text = format!("{}{digits}", if negative { "-" } else { "" });
                let number: i128 = text
                    .parse()
                    .map_err(|_| self.err("integer literal exceeds bootstrap limit"))?;
                self.pos += 1;
                if !seen.insert(number) {
                    return Err(self.err("duplicate integer match arm"));
                }
                Some(number)
            };
            self.expect("=>")?;
            let arm = if self.peek() == "{" {
                self.block_expression()?
            } else {
                self.expr(0)?
            };
            match pattern {
                Some(number) => arms.push((number, arm_line, arm)),
                None => fallback = Some(arm),
            }
            if self.eat("}") {
                break;
            }
            self.expect(",")?;
        }
        let Some(mut tail) = fallback else {
            return Err(self.err("integer match requires a final _ arm"));
        };
        for (number, arm_line, arm) in arms.into_iter().rev() {
            let condition = Expr {
                kind: Kind::Binary(
                    "==".into(),
                    Box::new(Expr {
                        kind: Kind::Name(temporary.clone()),
                        line: arm_line,
                    }),
                    Box::new(Expr {
                        kind: Kind::Number(number),
                        line: arm_line,
                    }),
                ),
                line: arm_line,
            };
            tail = Expr {
                kind: Kind::If(Box::new(condition), Box::new(arm), Box::new(tail)),
                line: arm_line,
            };
            if !tail.bounded_depth(128) {
                return Err(self.err("expression tree depth limit reached (128)"));
            }
        }
        Ok(Expr {
            kind: Kind::Block(
                vec![Statement::Let {
                    name: temporary,
                    ty: None,
                    value,
                }],
                Box::new(tail),
            ),
            line,
        })
    }
}
