//! Statement parsing, tail expressions, and the restricted update grammar.

use super::*;

enum BindingKind {
    Let,
    Fact,
}

impl Parser {
    pub(super) fn function_body(&mut self) -> Result<(Vec<Statement>, Expr), String> {
        self.block(true)
    }

    fn block(&mut self, returns: bool) -> Result<(Vec<Statement>, Expr), String> {
        self.expect("{")?;
        let mut body = Vec::new();
        let result = loop {
            if self.peek() == "}" {
                break Expr {
                    kind: Kind::Unit,
                    line: self.line(),
                };
            }
            if let Some(statement) = self.body_statement()? {
                body.push(statement);
                continue;
            }
            if self.eat("return") {
                if !returns {
                    return Err(
                        self.err("return inside a loop needs an exit invariant; unsupported")
                    );
                }
                let value = self.expr(0)?;
                self.eat(";");
                break value;
            }
            let value = self.expr(0)?;
            if self.eat("=") {
                body.push(self.assignment(value)?);
                continue;
            }
            if self.eat(";") {
                body.push(Statement::Effect(value));
                continue;
            }
            break value;
        };
        self.expect("}")?;
        Ok((body, result))
    }

    fn body_statement(&mut self) -> Result<Option<Statement>, String> {
        let statement = if self.eat("ideal") {
            self.ideal_statement()?
        } else if self.eat("update") {
            self.update_statement()?
        } else if self.eat("while") {
            self.while_statement()?
        } else if self.eat("proof") {
            self.proof_statement()?
        } else if self.eat("let") {
            self.binding(BindingKind::Let)?
        } else if self.eat("fact") {
            self.binding(BindingKind::Fact)?
        } else {
            return Ok(None);
        };
        Ok(Some(statement))
    }

    fn assignment(&mut self, target: Expr) -> Result<Statement, String> {
        let value = self.expr(0)?;
        self.expect(";")?;
        Ok(Statement::Assign { target, value })
    }

    fn while_statement(&mut self) -> Result<Statement, String> {
        let line = self.line();
        if self.depth >= 128 {
            return Err(self.err("statement nesting limit reached (128)"));
        }
        self.depth += 1;
        let condition = self.expr(0)?;
        self.expect("invariant")?;
        let invariant = self.expr(0)?;
        let modifies = if self.eat("modifies") {
            self.nonempty_expressions()?
        } else {
            Vec::new()
        };
        let (mut body, tail) = self.block(false)?;
        if tail.kind != Kind::Unit {
            body.push(Statement::Effect(tail));
        }
        self.depth -= 1;
        Ok(Statement::While {
            condition,
            invariant,
            modifies,
            body,
            line,
        })
    }

    fn update_statement(&mut self) -> Result<Statement, String> {
        let line = self.line();
        let places = self.nonempty_expressions()?;
        self.expect("lifts")?;
        let mut lifts = Vec::new();
        loop {
            lifts.push(self.lifted_selector()?);
            if !self.eat(",") {
                break;
            }
        }
        self.expect("{")?;
        let mut body = Vec::new();
        while !self.eat("}") {
            body.push(self.update_item()?);
        }
        Ok(Statement::Update {
            places,
            lifts,
            body,
            line,
        })
    }

    fn lifted_selector(&mut self) -> Result<String, String> {
        // Selectors can include module::Type::fact; ordinary names have at
        // most one module qualifier, so their parser is intentionally separate.
        let mut selector = self.name()?;
        while self.eat("::") {
            selector.push_str("::");
            selector.push_str(&self.name()?);
        }
        Ok(selector)
    }

    fn update_item(&mut self) -> Result<Statement, String> {
        if self.eat("ideal") {
            return self.ideal_statement();
        }
        if self.eat("let") {
            let name = self.name()?;
            let ty = if self.eat(":") {
                Some(self.ty()?)
            } else {
                None
            };
            self.expect("=")?;
            let value = self.expr(0)?;
            self.expect(";")?;
            return Ok(Statement::Let { name, ty, value });
        }
        if self.eat("proof") {
            return self.proof_statement();
        }
        if self.eat("fact") {
            return self.binding(BindingKind::Fact);
        }
        let target = self.expr(0)?;
        if self.eat("=") {
            return self.assignment(target);
        }
        self.expect(";")?;
        Ok(Statement::Effect(target))
    }

    fn ideal_statement(&mut self) -> Result<Statement, String> {
        let statement = if self.eat("let") {
            self.binding(BindingKind::Let)?
        } else {
            let target = self.expr(0)?;
            self.expect("=")?;
            self.assignment(target)?
        };
        Ok(Statement::Ideal(Box::new(statement)))
    }

    fn binding(&mut self, kind: BindingKind) -> Result<Statement, String> {
        let fact = matches!(kind, BindingKind::Fact);
        let mut name = self.name()?;
        if !fact && self.eat("::") {
            name.push_str("::");
            name.push_str(&self.name()?);
            if self.peek() != "{" {
                return Err(self.err("qualified let names require a record pattern"));
            }
        }
        if !fact && self.eat("{") {
            let mut fields = Vec::new();
            if !self.eat("}") {
                loop {
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
                    if self.eat("}") {
                        break;
                    }
                }
            }
            self.expect("=")?;
            let value = self.expr(0)?;
            self.expect(";")?;
            return Ok(Statement::Destructure {
                record: name,
                fields,
                value,
            });
        }
        let ty = if !fact && self.eat(":") {
            Some(self.ty()?)
        } else {
            None
        };
        self.expect("=")?;
        let value = self.expr(0)?;
        self.expect(";")?;
        Ok(if fact {
            Statement::Fact { name, value }
        } else {
            Statement::Let { name, ty, value }
        })
    }

    fn proof_statement(&mut self) -> Result<Statement, String> {
        let name = if self.eat("_") {
            self.expect(":")?;
            "_".into()
        } else if self
            .tokens
            .get(self.pos + 1)
            .is_some_and(|token| token.text == ":")
        {
            let name = self.name()?;
            self.expect(":")?;
            name
        } else {
            "_".into()
        };
        let proposition = self.expr(0)?;
        let steps = if self.eat("by") {
            self.proof()?
        } else {
            vec!["omega".into()]
        };
        self.expect(";")?;
        Ok(Statement::Proof {
            name,
            proposition,
            steps,
        })
    }
}
