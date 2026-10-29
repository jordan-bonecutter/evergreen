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

    pub(super) fn block_expression(&mut self) -> Result<Expr, String> {
        let line = self.line();
        let (body, tail) = self.block(false)?;
        Ok(if body.is_empty() {
            tail
        } else {
            Expr {
                kind: Kind::Block(body, Box::new(tail)),
                line,
            }
        })
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
                    return Err(self.err(
                        "return from a nested block needs checked exit/cleanup paths; unsupported",
                    ));
                }
                let value = self.expr(0)?;
                self.eat(";");
                break value;
            }
            let block_like = matches!(self.peek(), "match" | "if" | "{");
            let value = self.expr(0)?;
            if self.eat("=") {
                body.push(self.assignment(value)?);
                continue;
            }
            if self.eat(";") {
                body.push(Statement::Effect(value));
                continue;
            }
            if block_like && self.peek() != "}" {
                body.push(Statement::Effect(value));
                continue;
            }
            break value;
        };
        self.expect("}")?;
        Ok((body, result))
    }

    fn body_statement(&mut self) -> Result<Option<Statement>, String> {
        // Dispatch before constructing a statement, keeping recursive parsing
        // from reserving a large result temporary for every keyword branch.
        let parse: fn(&mut Self) -> Result<Statement, String> = match self.peek() {
            "ideal" => Self::ideal_statement,
            "update" => Self::update_statement,
            "starts_owner" => Self::owner_start_statement,
            "while" => Self::while_statement,
            "proof" => Self::proof_statement,
            "let" => |parser| parser.binding(BindingKind::Let),
            "fact" => |parser| parser.binding(BindingKind::Fact),
            _ => return Ok(None),
        };
        self.pos += 1;
        parse(self).map(Some)
    }

    fn assignment(&mut self, target: Expr) -> Result<Statement, String> {
        let value = self.expr(0)?;
        if self.peek() == "starts_owner" {
            return Err(self.err("use starts_owner(pointer) { target = value; }"));
        }
        self.expect(";")?;
        Ok(Statement::Assign {
            target,
            value,
            starts: Vec::new(),
        })
    }

    fn owner_start_statement(&mut self) -> Result<Statement, String> {
        let starts = self.nonempty_expressions()?;
        if let Some(hints) = &mut self.format_hints {
            hints.bodies.insert(self.pos);
        }
        self.expect("{")?;
        // This scope marks one write event, not a transaction over an arbitrary
        // sequence. Lower it to the existing checked assignment transition.
        let target = self.expr(0)?;
        if !self.eat("=") {
            return Err(self.err("starts_owner requires exactly one assignment"));
        }
        let mut statement = self.assignment(target)?;
        if !self.eat("}") {
            return Err(self.err("starts_owner requires exactly one assignment"));
        }
        if let Statement::Assign { starts: owners, .. } = &mut statement {
            *owners = starts;
        }
        Ok(statement)
    }

    fn while_statement(&mut self) -> Result<Statement, String> {
        let line = self.line();
        if self.depth >= 128 {
            return Err(self.err("statement nesting limit reached (128)"));
        }
        self.depth += 1;
        let condition = self.expr(0)?;
        let start = self.pos;
        self.expect("invariant")?;
        let invariant = self.expr(0)?;
        self.note_format_clause(start);
        let start = self.pos;
        let modifies = if self.eat("modifies") {
            self.nonempty_expressions()?
        } else {
            Vec::new()
        };
        self.note_format_clause(start);
        let start = self.pos;
        let decreases = if self.eat("decreases") {
            Some(self.expr(0)?)
        } else {
            None
        };
        self.note_format_clause(start);
        if let Some(hints) = &mut self.format_hints {
            hints.bodies.insert(self.pos);
        }
        let (mut body, tail) = self.block(false)?;
        if tail.kind != Kind::Unit {
            body.push(Statement::Effect(tail));
        }
        self.depth -= 1;
        Ok(Statement::While {
            condition,
            invariant,
            modifies,
            decreases,
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
        let mut arguments = Vec::new();
        while !fact && self.eat("::") {
            if self.peek() == "<" {
                arguments = self.generic_arguments()?;
                break;
            }
            name.push_str("::");
            name.push_str(&self.name()?);
        }
        if (name.contains("::") || !arguments.is_empty()) && self.peek() != "{" {
            return Err(self.err("qualified let names require a record pattern"));
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
                arguments,
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
        let header = self.pos - 1;
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
        let start = self.pos;
        let proposition = self.expr(0)?;
        let steps = if self.eat("by") {
            self.proof()?
        } else {
            vec!["omega".into()]
        };
        self.expect(";")?;
        if let Some(hints) = &mut self.format_hints {
            hints.proofs.insert(start, self.pos);
            hints.proof_headers.insert(header);
        }
        Ok(Statement::Proof {
            name,
            proposition,
            steps,
        })
    }
}
