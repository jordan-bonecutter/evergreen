//! Function signatures, contracts, and return-borrow paths.

use super::*;

struct Parameters {
    values: Vec<(String, Type)>,
    ideal: Vec<String>,
    receiver_pattern: Option<Vec<(String, String)>>,
}

fn return_path(expression: &Expr, out: &mut Vec<ReturnProjection>) -> Result<(), String> {
    match &expression.kind {
        Kind::Name(name) if name == "result" => {}
        Kind::Name(name) => out.push(ReturnProjection::Field(name.clone())),
        Kind::Field(base, name) => {
            return_path(base, out)?;
            out.push(ReturnProjection::Field(name.clone()));
        }
        Kind::Index(base, index) => {
            return_path(base, out)?;
            let Kind::Number(index) = index.kind else {
                return Err("return alias indices must be integer literals".into());
            };
            out.push(ReturnProjection::Index(
                usize::try_from(index).map_err(|_| "return alias index is out of range")?,
            ));
        }
        _ => return Err("borrow targets require return field or literal index paths".into()),
    }
    Ok(())
}

impl Parser {
    pub(super) fn function(
        &mut self,
        receiver: Option<&str>,
        ideal: bool,
    ) -> Result<(Vec<GenericParameter>, Function), String> {
        let saved_consts = self.generic_consts.clone();
        let saved_names = self.generic_names.clone();
        let line = self.line();
        let external = if self.eat("extern") {
            if self.eat("console_write") {
                Some(External::ConsoleWrite)
            } else if self.eat("compare_exchange64") {
                Some(External::CompareExchange64)
            } else {
                self.expect("syscall")?;
                self.expect("(")?;
                let number = self
                    .peek()
                    .parse::<u32>()
                    .map_err(|_| self.err("syscall number must be a u32 integer literal"))?;
                self.pos += 1;
                self.expect(")")?;
                Some(External::Syscall(number))
            }
        } else {
            None
        };
        let method = self.eat("method");
        let by_reference = method && self.eat("&");
        if !method {
            self.expect("fn")?;
        }
        if method && (receiver.is_none() || external.is_some()) {
            return Err(self.err("methods require an impl scope and a checked body"));
        }
        let name = self.name()?;
        let generics = self.generic_parameters()?;
        let mut parameters = self.function_parameters(receiver)?;
        if parameters.receiver_pattern.is_some() && (method || name != "drop") {
            return Err(
                self.err("a bare receiver pattern currently requires fn drop inside impl Drop")
            );
        }
        if method {
            if parameters.values.iter().any(|(name, _)| name == "self") {
                return Err(self.err("method self is implicit; omit it from the parameter list"));
            }
            let mut ty = Type::Named(receiver.expect("method receiver scope").to_owned());
            if by_reference {
                ty = Type::Ref(Box::new(ty));
            }
            parameters.values.insert(0, ("self".into(), ty));
        }
        let ret = if self.eat("->") {
            self.ty()?
        } else {
            Type::Unit
        };
        let pre = self.optional_clause("where")?;
        let start = self.pos;
        let modifies = if self.eat("modifies") {
            self.nonempty_expressions()?
        } else {
            Vec::new()
        };
        self.note_format_clause(start);
        let start = self.pos;
        let borrows = self.return_borrows()?;
        self.note_format_clause(start);
        let post = self.optional_clause("ensures")?;
        let decreases = self.optional_clause("decreases")?;
        if let Some(hints) = &mut self.format_hints {
            hints.bodies.insert(self.pos);
        }
        let (mut body, result) = if external.is_some() {
            self.expect(";")?;
            (
                Vec::new(),
                Expr {
                    kind: Kind::Unit,
                    line,
                },
            )
        } else {
            self.function_body()?
        };
        if let Some(fields) = parameters.receiver_pattern.take() {
            body.insert(
                0,
                Statement::Destructure {
                    record: receiver
                        .ok_or_else(|| self.err("receiver patterns require an impl scope"))?
                        .to_owned(),
                    arguments: Vec::new(),
                    fields,
                    value: Expr {
                        kind: Kind::Name("self".into()),
                        line,
                    },
                },
            );
        }
        let proof = if self.eat("proof") {
            Some(self.proof()?)
        } else {
            None
        };
        self.generic_consts = saved_consts;
        self.generic_names = saved_names;
        Ok((
            generics,
            Function {
                source: crate::shared::diagnostics::SourceOrigin::Input(0),
                impl_target: None,
                receiver: if method {
                    Some(if by_reference {
                        MethodReceiver::Reference
                    } else {
                        MethodReceiver::Value
                    })
                } else {
                    None
                },
                name,
                external,
                params: parameters.values,
                ret,
                pre,
                post,
                decreases,
                borrows,
                body,
                result,
                proof,
                line,
                drop_target: receiver.map(str::to_owned),
                ideal,
                modifies,
                ideal_params: parameters.ideal,
                module: None,
                partial: false,
                unspecified_arithmetic: false,
                entry_memory: false,
                entry_pointees: Vec::new(),
            },
        ))
    }

    fn function_parameters(&mut self, receiver: Option<&str>) -> Result<Parameters, String> {
        self.expect("(")?;
        let mut values = Vec::new();
        let mut ideal = Vec::new();
        if self.eat("{") {
            let target =
                receiver.ok_or_else(|| self.err("receiver patterns require an impl scope"))?;
            let fields = self.pattern_fields()?;
            self.expect(")")?;
            return Ok(Parameters {
                values: vec![("self".into(), Type::Named(target.to_owned()))],
                ideal,
                receiver_pattern: Some(fields),
            });
        }
        if !self.eat(")") {
            loop {
                let erased = self.eat("ideal");
                let name = self.name()?;
                if erased {
                    ideal.push(name.clone());
                }
                let ty = match receiver {
                    Some(target) if name == "self" && self.peek() != ":" => {
                        Type::Named(target.into())
                    }
                    _ => {
                        self.expect(":")?;
                        self.ty()?
                    }
                };
                values.push((name, ty));
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        Ok(Parameters {
            values,
            ideal,
            receiver_pattern: None,
        })
    }

    fn optional_clause(&mut self, keyword: &str) -> Result<Option<Expr>, String> {
        let start = self.pos;
        if !self.eat(keyword) {
            return Ok(None);
        }
        let expression = self.expr(0)?;
        self.note_format_clause(start);
        Ok(Some(expression))
    }

    fn return_borrows(&mut self) -> Result<Vec<ReturnBorrow>, String> {
        let mut borrows = Vec::new();
        if self.eat("borrows") {
            self.expect("(")?;
            loop {
                let expression = self.expr(0)?;
                if self.eat(":") {
                    let mut path = Vec::new();
                    return_path(&expression, &mut path)?;
                    borrows.push(ReturnBorrow {
                        path,
                        reference: self.expr(0)?,
                    });
                } else {
                    if !borrows.is_empty() {
                        return Err(self.err("structured borrows entries require path: reference"));
                    }
                    borrows.push(ReturnBorrow {
                        path: Vec::new(),
                        reference: expression,
                    });
                    self.expect(")")?;
                    break;
                }
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        if self.eat("when") {
            if borrows.is_empty() {
                return Err(self.err("when requires a preceding borrows contract"));
            }
            if self.depth >= 128 {
                return Err(self.err("conditional borrow nesting limit reached"));
            }
            self.depth += 1;
            let condition = self.expr(0)?;
            self.expect("else")?;
            let alternatives = self.return_borrows()?;
            self.depth -= 1;
            if alternatives.len() != borrows.len()
                || borrows.iter().any(|alias| {
                    alternatives
                        .iter()
                        .filter(|other| other.path == alias.path)
                        .count()
                        != 1
                })
            {
                return Err(self.err(
                    "conditional borrows must name the same return paths in every alternative",
                ));
            }
            for alias in &mut borrows {
                let other = alternatives
                    .iter()
                    .find(|other| other.path == alias.path)
                    .ok_or_else(|| self.err("missing conditional return path"))?;
                alias.reference = Expr {
                    line: condition.line,
                    kind: Kind::If(
                        Box::new(condition.clone()),
                        Box::new(alias.reference.clone()),
                        Box::new(other.reference.clone()),
                    ),
                };
            }
        }
        Ok(borrows)
    }
}

impl Function {
    /// Calls may provide every parameter, or omit all erased parameters for inference.
    pub(crate) fn supplied_parameters(&self, count: usize) -> Result<Vec<&(String, Type)>, String> {
        if count == self.params.len() {
            return Ok(self.params.iter().collect());
        }
        let runtime = self
            .params
            .iter()
            .filter(|(name, _)| !self.ideal_params.contains(name))
            .collect::<Vec<_>>();
        if count == runtime.len() && !self.ideal_params.is_empty() {
            return Ok(runtime);
        }
        Err(if self.ideal_params.is_empty() {
            format!("{} expects {} arguments", self.name, self.params.len())
        } else {
            format!(
                "{} expects {} runtime arguments, or {} arguments including explicit ideal values",
                self.name,
                runtime.len(),
                self.params.len()
            )
        })
    }
}
