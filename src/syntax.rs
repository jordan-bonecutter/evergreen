//! Shared, source-located syntax for the internal compiler pipeline.
use crate::{lex, Token};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Int,
    Nat,
    Bool,
    Array(Box<Type>, Box<Expr>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: Kind,
    pub line: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Number(i128),
    Bool(bool),
    Name(String),
    Unary(String, Box<Expr>),
    Binary(String, Box<Expr>, Box<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Array(Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}
#[derive(Clone, Debug)]
pub struct Statement {
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr,
    pub proof: Option<Vec<String>>,
    pub fact: bool,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub pre: Option<Expr>,
    pub post: Option<Expr>,
    pub body: Vec<Statement>,
    pub result: Expr,
    pub proof: Vec<String>,
    pub line: usize,
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    depth: usize,
}
impl Parser {
    fn peek(&self) -> &str {
        &self.tokens[self.pos].text
    }
    fn line(&self) -> usize {
        self.tokens[self.pos].line
    }
    fn err(&self, s: &str) -> String {
        format!("line {}: {s}", self.line())
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.peek() == s {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, s: &str) -> Result<(), String> {
        if self.eat(s) {
            Ok(())
        } else {
            Err(self.err(&format!("expected {s:?}, found {:?}", self.peek())))
        }
    }
    fn name(&mut self) -> Result<String, String> {
        let s = self.peek().to_string();
        if !s.starts_with(|c: char| c.is_ascii_alphabetic())
            || s.starts_with("evg_")
            || matches!(
                s.as_str(),
                "fn" | "let"
                    | "fact"
                    | "return"
                    | "result"
                    | "proof"
                    | "where"
                    | "ensures"
                    | "if"
                    | "else"
                    | "true"
                    | "false"
                    | "by"
                    | "sorry"
                    | "axiom"
                    | "unsafe"
                    | "partial"
            )
        {
            return Err(self.err("expected a non-reserved identifier"));
        }
        self.pos += 1;
        Ok(s)
    }
    fn ty(&mut self) -> Result<Type, String> {
        if self.depth >= 128 {
            return Err(self.err("syntax nesting limit reached"));
        }
        self.depth += 1;
        let result = if self.eat("[") {
            let t = self.ty()?;
            self.expect(";")?;
            let n = self.expr(0)?;
            self.expect("]")?;
            Ok(Type::Array(Box::new(t), Box::new(n)))
        } else {
            match self.peek() {
                "isize" => {
                    self.pos += 1;
                    Ok(Type::Int)
                }
                "usize" => {
                    self.pos += 1;
                    Ok(Type::Nat)
                }
                "bool" => {
                    self.pos += 1;
                    Ok(Type::Bool)
                }
                _ => Err(self.err("expected isize, usize, bool, or [T; n]")),
            }
        };
        self.depth -= 1;
        result
    }
    fn expr(&mut self, min: u8) -> Result<Expr, String> {
        if self.depth >= 128 {
            return Err(self.err("syntax nesting limit reached"));
        }
        self.depth += 1;
        let line = self.line();
        let mut lhs = if self.eat("(") {
            let e = self.expr(0)?;
            self.expect(")")?;
            e
        } else if self.peek() == "-" || self.peek() == "!" {
            let op = self.peek().to_owned();
            self.pos += 1;
            Expr {
                kind: Kind::Unary(op, Box::new(self.expr(7)?)),
                line,
            }
        } else if self.eat("if") {
            let cond = self.expr(0)?;
            self.expect("{")?;
            let yes = self.expr(0)?;
            self.expect("}")?;
            self.expect("else")?;
            self.expect("{")?;
            let no = self.expr(0)?;
            self.expect("}")?;
            Expr {
                kind: Kind::If(Box::new(cond), Box::new(yes), Box::new(no)),
                line,
            }
        } else if self.eat("[") {
            let mut items = Vec::new();
            if !self.eat("]") {
                loop {
                    items.push(self.expr(0)?);
                    if self.eat("]") {
                        break;
                    }
                    self.expect(",")?;
                }
            }
            Expr {
                kind: Kind::Array(items),
                line,
            }
        } else {
            let s = self.peek().to_owned();
            let kind = if s.chars().all(|c| c.is_ascii_digit()) && !s.is_empty() {
                self.pos += 1;
                Kind::Number(
                    s.parse()
                        .map_err(|_| self.err("integer literal exceeds bootstrap limit"))?,
                )
            } else if self.eat("true") {
                Kind::Bool(true)
            } else if self.eat("false") {
                Kind::Bool(false)
            } else if self.eat("result") {
                Kind::Name("result".into())
            } else {
                let n = self.name()?;
                if self.eat("(") {
                    let mut args = Vec::new();
                    if !self.eat(")") {
                        loop {
                            args.push(self.expr(0)?);
                            if self.eat(")") {
                                break;
                            }
                            self.expect(",")?;
                        }
                    }
                    Kind::Call(n, args)
                } else {
                    Kind::Name(n)
                }
            };
            Expr { kind, line }
        };
        loop {
            if self.peek() == "[" && min <= 8 {
                self.pos += 1;
                let idx = self.expr(0)?;
                self.expect("]")?;
                lhs = Expr {
                    kind: Kind::Index(Box::new(lhs), Box::new(idx)),
                    line,
                };
                continue;
            }
            let prec = match self.peek() {
                "||" => 1,
                "&&" => 2,
                "==" | "!=" => 3,
                "<" | "<=" | ">" | ">=" => 4,
                "+" | "-" => 5,
                "*" => 6,
                "/" | "%" => return Err(self.err("division and remainder are not supported yet")),
                _ => break,
            };
            if prec < min {
                break;
            }
            let op = self.peek().to_owned();
            self.pos += 1;
            let rhs = self.expr(prec + 1)?;
            lhs = Expr {
                kind: Kind::Binary(op, Box::new(lhs), Box::new(rhs)),
                line,
            };
        }
        self.depth -= 1;
        Ok(lhs)
    }
    fn proof(&mut self) -> Result<Vec<String>, String> {
        self.expect("{")?;
        let mut steps = Vec::new();
        loop {
            if self.peek() == "<eof>" {
                return Err(self.err("unterminated proof block"));
            }
            let s = self.peek().to_owned();
            self.pos += 1;
            let step = match s.as_str() {
                "omega" | "rfl" | "simp_all" | "decide" | "assumption" => s,
                "exact" => format!("exact {}", self.name()?),
                _ => return Err(self.err("unsupported proof step; unproven axioms are forbidden")),
            };
            steps.push(step);
            if self.eat("}") {
                break;
            }
            self.expect(";")?;
            if self.eat("}") {
                break;
            }
        }
        Ok(steps)
    }
    fn function(&mut self) -> Result<Function, String> {
        let line = self.line();
        self.expect("fn")?;
        let name = self.name()?;
        self.expect("(")?;
        let mut params = Vec::new();
        if !self.eat(")") {
            loop {
                let n = self.name()?;
                self.expect(":")?;
                params.push((n, self.ty()?));
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        self.expect("->")?;
        let ret = self.ty()?;
        let pre = if self.eat("where") {
            self.expect("(")?;
            let p = self.expr(0)?;
            self.expect(")")?;
            Some(p)
        } else {
            None
        };
        let post = if self.eat("ensures") {
            self.expect("(")?;
            let p = self.expr(0)?;
            self.expect(")")?;
            Some(p)
        } else {
            None
        };
        self.expect("{")?;
        let mut body = Vec::new();
        while self.peek() == "let" || self.peek() == "fact" {
            let fact = self.eat("fact");
            if !fact {
                self.expect("let")?;
            }
            let name = self.name()?;
            let ty = if !fact && self.eat(":") {
                Some(self.ty()?)
            } else {
                None
            };
            self.expect("=")?;
            let value = self.expr(0)?;
            let proof = if self.eat("by") {
                if !fact {
                    return Err(self.err("only facts accept by blocks"));
                }
                Some(self.proof()?)
            } else {
                None
            };
            self.expect(";")?;
            body.push(Statement {
                name,
                ty,
                value,
                proof,
                fact,
            });
        }
        self.eat("return");
        let result = self.expr(0)?;
        self.eat(";");
        self.expect("}")?;
        let proof = if self.eat("proof") {
            self.proof()?
        } else {
            vec!["omega".into()]
        };
        Ok(Function {
            name,
            params,
            ret,
            pre,
            post,
            body,
            result,
            proof,
            line,
        })
    }
}

pub fn parse(source: &str) -> Result<Vec<Function>, String> {
    if source.len() > 1_000_000 {
        return Err("source exceeds 1 MB bootstrap limit".into());
    }
    let mut p = Parser {
        tokens: lex(source)?,
        pos: 0,
        depth: 0,
    };
    let mut functions = Vec::new();
    while p.peek() != "<eof>" {
        functions.push(p.function()?);
    }
    if functions.is_empty() {
        return Err("expected at least one function".into());
    }
    Ok(functions)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parses_calls_branches_and_arrays() {
        let f = parse(
            "fn main() -> usize { let a: [usize; 2] = [1, 2]; if true { f(a[0]) } else { 3 } }",
        )
        .unwrap();
        assert!(matches!(f[0].result.kind, Kind::If(..)));
    }
    #[test]
    fn rejects_truncated_proofs_and_deep_syntax() {
        assert!(parse("fn f() -> usize { 1 } proof {").is_err());
        let s = format!(
            "fn f() -> usize {{ {}1{} }}",
            "(".repeat(200),
            ")".repeat(200)
        );
        assert!(parse(&s).is_err());
    }
}
