//! Shared, source-located syntax for the internal compiler pipeline.
use crate::{lex, Token};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineInt {
    pub signed: bool,
    pub bits: u8,
}
impl MachineInt {
    pub fn parse(s: &str) -> Option<Self> {
        if s == "usize" {
            return Some(Self {
                signed: false,
                bits: 64,
            });
        }
        if s == "isize" {
            return Some(Self {
                signed: true,
                bits: 64,
            });
        }
        let signed = match s.as_bytes().first()? {
            b'i' => true,
            b'u' => false,
            _ => return None,
        };
        let bits = s.get(1..)?.parse().ok()?;
        if !matches!(bits, 8 | 16 | 32 | 64) {
            return None;
        }
        Some(Self { signed, bits })
    }
    pub fn bounds(self) -> (i128, i128) {
        if self.signed {
            let half = 1_i128 << (self.bits - 1);
            (-half, half - 1)
        } else {
            (0, (1_i128 << self.bits) - 1)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Int,
    Nat,
    Bool,
    Unit,
    Ref(Box<Type>),
    Machine(MachineInt),
    Named(String),
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
    Constant(MachineInt, i128),
    Bool(bool),
    Unit,
    Name(String),
    Unary(String, Box<Expr>),
    Binary(String, Box<Expr>, Box<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Array(Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Record(String, Vec<(String, Expr)>),
    Field(Box<Expr>, String),
}
#[derive(Clone, Debug)]
pub enum Statement {
    Let {
        name: String,
        ty: Option<Type>,
        value: Expr,
    },
    Fact {
        name: String,
        value: Expr,
        proof: Option<Vec<String>>,
    },
    Assign {
        target: Expr,
        value: Expr,
    },
    Effect(Expr),
    Update {
        places: Vec<String>,
        body: Vec<Statement>,
        line: usize,
    },
}
#[derive(Clone, Debug)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<(String, Type)>,
    pub invariant: Option<Expr>,
    pub line: usize,
}
#[derive(Clone, Debug)]
pub struct Program {
    pub structs: Vec<Struct>,
    pub functions: Vec<Function>,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub pre: Option<Expr>,
    pub post: Option<Expr>,
    pub decreases: Option<Expr>,
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
        let result = if self.eat("&") {
            Ok(Type::Ref(Box::new(self.ty()?)))
        } else if self.eat("(") {
            self.expect(")")?;
            Ok(Type::Unit)
        } else if self.eat("[") {
            let t = self.ty()?;
            self.expect(";")?;
            let n = self.expr(0)?;
            self.expect("]")?;
            Ok(Type::Array(Box::new(t), Box::new(n)))
        } else {
            match self.peek() {
                s if MachineInt::parse(s).is_some() => {
                    let t = MachineInt::parse(s).expect("validated machine type");
                    self.pos += 1;
                    Ok(Type::Machine(t))
                }
                "int" => {
                    self.pos += 1;
                    Ok(Type::Int)
                }
                "nat" => {
                    self.pos += 1;
                    Ok(Type::Nat)
                }
                "bool" => {
                    self.pos += 1;
                    Ok(Type::Bool)
                }
                _ if self.peek().starts_with(|c: char| c.is_ascii_uppercase()) => {
                    Ok(Type::Named(self.name()?))
                }
                _ => Err(self.err("expected isize, usize, bool, [T; n], or a struct name")),
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
            if self.eat(")") {
                Expr {
                    kind: Kind::Unit,
                    line,
                }
            } else {
                let e = self.expr(0)?;
                self.expect(")")?;
                e
            }
        } else if matches!(self.peek(), "-" | "!" | "&" | "*") {
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
                if self.eat("::") {
                    let ty = MachineInt::parse(&n)
                        .ok_or_else(|| self.err("qualified constants require an integer type"))?;
                    let (lo, hi) = ty.bounds();
                    let bound = self.name()?;
                    Kind::Constant(
                        ty,
                        match bound.as_str() {
                            "MAX" | "max" => hi,
                            "MIN" | "min" => lo,
                            _ => return Err(self.err("expected MAX or MIN")),
                        },
                    )
                } else if n.starts_with(|c: char| c.is_ascii_uppercase()) && self.eat("{") {
                    let mut fields = Vec::new();
                    if !self.eat("}") {
                        loop {
                            let field = self.name()?;
                            self.expect(":")?;
                            let value = self.expr(0)?;
                            fields.push((field, value));
                            if self.eat("}") {
                                break;
                            }
                            self.expect(",")?;
                            if self.eat("}") {
                                break;
                            }
                        }
                    }
                    Kind::Record(n, fields)
                } else if self.eat("(") {
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
            if min <= 8 && self.eat(".") {
                let field = self.name()?;
                lhs = Expr {
                    kind: Kind::Field(Box::new(lhs), field),
                    line,
                };
                continue;
            }
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
        let decreases = if self.eat("decreases") {
            self.expect("(")?;
            let m = self.expr(0)?;
            self.expect(")")?;
            Some(m)
        } else {
            None
        };
        self.expect("{")?;
        let mut body = Vec::new();
        let result = loop {
            if self.eat("update") {
                let line = self.line();
                self.expect("(")?;
                let mut places = Vec::new();
                loop {
                    places.push(self.name()?);
                    if self.eat(")") {
                        break;
                    }
                    self.expect(",")?;
                }
                self.expect("{")?;
                let mut updates = Vec::new();
                while !self.eat("}") {
                    if self.eat("fact") {
                        let name = self.name()?;
                        self.expect("=")?;
                        let value = self.expr(0)?;
                        let proof = if self.eat("by") {
                            Some(self.proof()?)
                        } else {
                            None
                        };
                        self.expect(";")?;
                        updates.push(Statement::Fact { name, value, proof });
                    } else {
                        let target = self.expr(0)?;
                        self.expect("=")?;
                        let value = self.expr(0)?;
                        self.expect(";")?;
                        updates.push(Statement::Assign { target, value });
                    }
                }
                body.push(Statement::Update {
                    places,
                    body: updates,
                    line,
                });
                continue;
            }
            if self.eat("return") {
                let value = self.expr(0)?;
                self.eat(";");
                break value;
            }
            if self.peek() != "let" && self.peek() != "fact" {
                let value = self.expr(0)?;
                if self.eat("=") {
                    let rhs = self.expr(0)?;
                    self.expect(";")?;
                    body.push(Statement::Assign {
                        target: value,
                        value: rhs,
                    });
                    continue;
                }
                if self.eat(";") && self.peek() != "}" {
                    body.push(Statement::Effect(value));
                    continue;
                }
                break value;
            }
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
            body.push(if fact {
                Statement::Fact { name, value, proof }
            } else {
                Statement::Let { name, ty, value }
            });
        };
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
            decreases,
            body,
            result,
            proof,
            line,
        })
    }

    fn structure(&mut self) -> Result<Struct, String> {
        let line = self.line();
        self.expect("type")?;
        let name = self.name()?;
        if !name.starts_with(|c: char| c.is_ascii_uppercase()) {
            return Err(self.err("struct names must start with an uppercase letter"));
        }
        self.expect("struct")?;
        self.expect("{")?;
        let mut fields = Vec::new();
        if !self.eat("}") {
            loop {
                let n = self.name()?;
                self.expect(":")?;
                fields.push((n, self.ty()?));
                if self.eat("}") {
                    break;
                }
                self.expect(",")?;
                if self.eat("}") {
                    break;
                }
            }
        }
        let invariant = if self.eat("where") {
            self.expect("(")?;
            let p = self.expr(0)?;
            self.expect(")")?;
            Some(p)
        } else {
            None
        };
        self.eat(";");
        Ok(Struct {
            name,
            fields,
            invariant,
            line,
        })
    }
}

pub fn parse(source: &str) -> Result<Program, String> {
    if source.len() > 1_000_000 {
        return Err("source exceeds 1 MB bootstrap limit".into());
    }
    let mut p = Parser {
        tokens: lex(source)?,
        pos: 0,
        depth: 0,
    };
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    while p.peek() != "<eof>" {
        if p.peek() == "type" {
            structs.push(p.structure()?);
        } else {
            functions.push(p.function()?);
        }
    }
    if functions.is_empty() {
        return Err("expected at least one function".into());
    }
    Ok(Program { structs, functions })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parses_calls_branches_and_arrays() {
        let f =
            parse("fn main() -> nat { let a: [nat; 2] = [1, 2]; if true { f(a[0]) } else { 3 } }")
                .unwrap();
        assert!(matches!(f.functions[0].result.kind, Kind::If(..)));
    }
    #[test]
    fn rejects_truncated_proofs_and_deep_syntax() {
        assert!(parse("fn f() -> nat { 1 } proof {").is_err());
        let s = format!(
            "fn f() -> nat {{ {}1{} }}",
            "(".repeat(200),
            ")".repeat(200)
        );
        assert!(parse(&s).is_err());
    }
}
