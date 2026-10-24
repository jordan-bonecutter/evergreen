//! Function signatures, contracts, and return-borrow paths.
use super::*;

struct Parameters {
    values: Vec<(String, Type)>,
    ideal: Vec<String>,
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
    ) -> Result<Function, String> {
        let line = self.line();
        self.expect("fn")?;
        let name = self.name()?;
        let parameters = self.function_parameters(receiver)?;
        let ret = if self.eat("->") {
            self.ty()?
        } else {
            Type::Unit
        };
        let pre = self.optional_clause("where")?;
        let modifies = if self.eat("modifies") {
            self.nonempty_expressions()?
        } else {
            Vec::new()
        };
        let borrows = self.return_borrows()?;
        let post = self.optional_clause("ensures")?;
        let decreases = self.optional_clause("decreases")?;
        let (body, result) = self.function_body()?;
        let proof = if self.eat("proof") {
            Some(self.proof()?)
        } else {
            None
        };
        Ok(Function {
            name,
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
            entry_memory: false,
        })
    }

    fn function_parameters(&mut self, receiver: Option<&str>) -> Result<Parameters, String> {
        self.expect("(")?;
        let mut values = Vec::new();
        let mut ideal = Vec::new();
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
        Ok(Parameters { values, ideal })
    }

    fn optional_clause(&mut self, keyword: &str) -> Result<Option<Expr>, String> {
        if !self.eat(keyword) {
            return Ok(None);
        }
        self.expect("(")?;
        let expression = self.expr(0)?;
        self.expect(")")?;
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
        Ok(borrows)
    }
}
