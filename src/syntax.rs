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
impl Expr {
    // Check actual tree depth as well as parser recursion: a flat sequence of
    // left-associative operators or projections otherwise builds an unbounded
    // tree, including recursively dropped boxes on a parse error.
    fn bounded_depth(&self, remaining: usize) -> bool {
        if remaining == 0 {
            return false;
        }
        let child = |e: &Expr| e.bounded_depth(remaining - 1);
        match &self.kind {
            Kind::Unary(_, e) | Kind::Field(e, _) | Kind::FactAt(e, _) => child(e),
            Kind::Binary(_, a, b) | Kind::Index(a, b) => child(a) && child(b),
            Kind::If(c, a, b) => child(c) && child(a) && child(b),
            Kind::Array(es) | Kind::Call(_, es) => es.iter().all(child),
            Kind::Record(_, fields) => fields.iter().all(|(_, e)| child(e)),
            _ => true,
        }
    }
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
    FactAt(Box<Expr>, String),
}
#[derive(Clone, Debug)]
pub enum Statement {
    Destructure {
        record: String,
        fields: Vec<(String, String)>,
        value: Expr,
    },
    Let {
        name: String,
        ty: Option<Type>,
        value: Expr,
    },
    Fact {
        name: String,
        value: Expr,
    },
    Proof {
        name: String,
        proposition: Expr,
        steps: Vec<String>,
    },
    Assign {
        target: Expr,
        value: Expr,
    },
    Effect(Expr),
    Update {
        places: Vec<String>,
        lifts: Vec<String>,
        body: Vec<Statement>,
        line: usize,
    },
}
impl Statement {
    pub fn bindings(&self) -> Vec<&str> {
        match self {
            Self::Let { name, .. } => vec![name],
            Self::Destructure { fields, .. } => {
                fields.iter().map(|(_, name)| name.as_str()).collect()
            }
            _ => Vec::new(),
        }
    }
}
#[derive(Clone, Debug)]
pub struct Struct {
    pub name: String,
    pub fields: Vec<(String, Type)>,
    pub invariant: Option<Expr>,
    pub line: usize,
    pub ideal: bool,
    pub affine: bool,
    pub opaque: bool,
    pub module: Option<String>,
    pub facts: Vec<(String, Expr)>,
}
#[derive(Clone, Debug)]
pub struct Program {
    pub structs: Vec<Struct>,
    pub functions: Vec<Function>,
    pub destructors: Vec<(String, Function)>,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub pre: Option<Expr>,
    pub post: Option<Expr>,
    pub decreases: Option<Expr>,
    pub borrows: Option<Expr>,
    pub body: Vec<Statement>,
    pub result: Expr,
    pub proof: Option<Vec<String>>,
    pub line: usize,
    pub drop_target: Option<String>,
    pub ideal: bool,
    pub modifies: Vec<String>,
    pub ideal_params: Vec<String>,
    pub module: Option<String>,
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
        if s.len() > 256 {
            return Err(self.err("identifier exceeds 256-byte bootstrap limit"));
        }
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
                    | "borrows"
                    | "module"
                    | "opaque"
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
    fn path_name(&mut self) -> Result<String, String> {
        let mut name = self.name()?;
        if self.eat("::") {
            name.push_str("::");
            name.push_str(&self.name()?);
        }
        Ok(name)
    }
    fn arguments(&mut self) -> Result<Vec<Expr>, String> {
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
        Ok(args)
    }
    fn record_fields(&mut self) -> Result<Vec<(String, Expr)>, String> {
        let mut fields = Vec::new();
        if !self.eat("}") {
            loop {
                let field = self.name()?;
                self.expect(":")?;
                fields.push((field, self.expr(0)?));
                if self.eat("}") {
                    break;
                }
                self.expect(",")?;
                if self.eat("}") {
                    break;
                }
            }
        }
        Ok(fields)
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
                _ if self.peek().starts_with(|c: char| c.is_ascii_alphabetic()) => {
                    Ok(Type::Named(self.path_name()?))
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
                    let member = self.name()?;
                    if let Some(ty) = MachineInt::parse(&n) {
                        let (lo, hi) = ty.bounds();
                        Kind::Constant(
                            ty,
                            match member.as_str() {
                                "MAX" | "max" => hi,
                                "MIN" | "min" => lo,
                                _ => return Err(self.err("expected MAX or MIN")),
                            },
                        )
                    } else if self.eat("(") {
                        Kind::Call(format!("{n}::{member}"), self.arguments()?)
                    } else if member.starts_with(|c: char| c.is_ascii_uppercase()) && self.eat("{")
                    {
                        Kind::Record(format!("{n}::{member}"), self.record_fields()?)
                    } else {
                        Kind::FactAt(
                            Box::new(Expr {
                                kind: Kind::Name(n),
                                line,
                            }),
                            member,
                        )
                    }
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
            if !lhs.bounded_depth(128) {
                return Err(self.err("expression tree depth limit reached (128)"));
            }
            if min <= 8 && self.eat("::") {
                let name = self.name()?;
                lhs = Expr {
                    kind: Kind::FactAt(Box::new(lhs), name),
                    line,
                };
                continue;
            }
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
                "=>" => 0,
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
            let rhs = self.expr(if op == "=>" { prec } else { prec + 1 })?;
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
                "omega" | "rfl" | "simp_all" | "decide" | "assumption" | "trustme" => s,
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
    fn function(&mut self, receiver: Option<&str>, ideal: bool) -> Result<Function, String> {
        let line = self.line();
        self.expect("fn")?;
        let name = self.name()?;
        self.expect("(")?;
        let mut params = Vec::new();
        let mut ideal_params = Vec::new();
        if !self.eat(")") {
            loop {
                let erased = self.eat("ideal");
                let n = self.name()?;
                if erased {
                    ideal_params.push(n.clone());
                }
                let t = match receiver {
                    Some(target) if n == "self" && self.peek() != ":" => Type::Named(target.into()),
                    _ => {
                        self.expect(":")?;
                        self.ty()?
                    }
                };
                params.push((n, t));
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        let ret = if self.eat("->") {
            self.ty()?
        } else {
            Type::Unit
        };
        let pre = if self.eat("where") {
            self.expect("(")?;
            let p = self.expr(0)?;
            self.expect(")")?;
            Some(p)
        } else {
            None
        };
        let mut modifies = Vec::new();
        if self.eat("modifies") {
            self.expect("(")?;
            loop {
                modifies.push(self.name()?);
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        let borrows = if self.eat("borrows") {
            self.expect("(")?;
            let reference = self.expr(0)?;
            self.expect(")")?;
            Some(reference)
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
            if self.peek() == "}" {
                break Expr {
                    kind: Kind::Unit,
                    line: self.line(),
                };
            }
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
                self.expect("lifts")?;
                let mut lifts = Vec::new();
                loop {
                    let mut name = self.name()?;
                    while self.eat("::") {
                        name.push_str("::");
                        name.push_str(&self.name()?);
                    }
                    lifts.push(name);
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("{")?;
                let mut updates = Vec::new();
                while !self.eat("}") {
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
                        updates.push(Statement::Let { name, ty, value });
                    } else if self.eat("proof") {
                        updates.push(self.proof_statement()?);
                    } else if self.eat("fact") {
                        let name = self.name()?;
                        self.expect("=")?;
                        let value = self.expr(0)?;
                        self.expect(";")?;
                        updates.push(Statement::Fact { name, value });
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
                    lifts,
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
            if self.eat("proof") {
                body.push(self.proof_statement()?);
                continue;
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
                body.push(Statement::Destructure {
                    record: name,
                    fields,
                    value,
                });
                continue;
            }
            let ty = if !fact && self.eat(":") {
                Some(self.ty()?)
            } else {
                None
            };
            self.expect("=")?;
            let value = self.expr(0)?;
            self.expect(";")?;
            body.push(if fact {
                Statement::Fact { name, value }
            } else {
                Statement::Let { name, ty, value }
            });
        };
        self.expect("}")?;
        let proof = if self.eat("proof") {
            Some(self.proof()?)
        } else {
            None
        };
        Ok(Function {
            name,
            params,
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
            ideal_params,
            module: None,
        })
    }

    fn proof_statement(&mut self) -> Result<Statement, String> {
        let name = self.name()?;
        self.expect(":")?;
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

    fn destructor(&mut self) -> Result<(String, Function), String> {
        self.expect("impl")?;
        self.expect("Drop")?;
        self.expect("for")?;
        let target = self.path_name()?;
        self.expect("{")?;
        let mut function = self.function(Some(&target), false)?;
        if function.name != "drop"
            || function.params != vec![("self".into(), Type::Named(target.clone()))]
            || function.ret != Type::Unit
            || function.pre.is_some()
            || function.decreases.is_some()
            || function.borrows.is_some()
            || !function.modifies.is_empty()
            || !function.ideal_params.is_empty()
        {
            return Err(
                self.err("Drop requires fn drop(self) -> () without preconditions or recursion")
            );
        }
        self.expect("}")?;
        function.name = format!("evg_drop_{target}");
        Ok((target, function))
    }

    fn structure(&mut self, ideal: bool, affine: bool) -> Result<Struct, String> {
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
        let mut facts = Vec::new();
        let invariant = if self.eat("where") {
            self.expect("(")?;
            while self.peek() == "fact" || self.peek() == "pub" {
                self.eat("pub");
                self.expect("fact")?;
                let name = self.name()?;
                self.expect("=")?;
                let value = self.expr(0)?;
                self.expect(";")?;
                facts.push((name, value));
            }
            let value = self.expr(0)?;
            self.expect(")")?;
            Some(value)
        } else {
            None
        };
        self.eat(";");
        Ok(Struct {
            name,
            fields,
            invariant,
            line,
            ideal,
            affine,
            facts,
            opaque: false,
            module: None,
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
    let mut destructors = Vec::new();
    let mut module = None;
    let mut modules = std::collections::BTreeSet::new();
    while p.peek() != "<eof>" {
        if p.eat("module") {
            if module.is_some() {
                return Err(p.err("nested modules are not supported yet"));
            }
            let name = p.name()?;
            if MachineInt::parse(&name).is_some() || matches!(name.as_str(), "int" | "nat" | "bool")
            {
                return Err(p.err("module names cannot shadow builtin types"));
            }
            if !modules.insert(name.clone()) {
                return Err(
                    p.err("a module must have one closed definition; reopening is forbidden")
                );
            }
            p.expect("{")?;
            module = Some(name);
            continue;
        }
        if p.eat("}") {
            if module.take().is_none() {
                return Err(p.err("unexpected module closing brace"));
            }
            continue;
        }
        let ideal = p.eat("ideal");
        let opaque = p.eat("opaque");
        let affine = p.eat("affine");
        if p.peek() == "type" {
            let mut structure = p.structure(ideal, affine)?;
            if opaque && module.is_none() {
                return Err(p.err("opaque representations require a defining module"));
            }
            structure.opaque = opaque;
            structure.module = module.clone();
            structs.push(structure);
        } else if p.peek() == "impl" {
            if affine || opaque {
                return Err(p.err("affine and opaque modify type declarations"));
            }
            if ideal {
                return Err(p.err("ideal data has no runtime destructor"));
            }
            let (target, mut function) = p.destructor()?;
            function.module = module.clone();
            destructors.push((target, function));
        } else {
            if affine || opaque {
                return Err(p.err("affine and opaque modify type declarations"));
            }
            let mut function = p.function(None, ideal)?;
            function.module = module.clone();
            functions.push(function);
        }
    }
    if module.is_some() {
        return Err(p.err("unterminated module"));
    }
    if functions.is_empty() && destructors.is_empty() {
        return Err("expected at least one function".into());
    }
    let mut program = Program {
        structs,
        functions,
        destructors,
    };
    crate::modules::qualify(&mut program);
    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn module_scopes_are_closed_and_names_are_qualified_once() {
        let program = parse("module a {opaque type Item struct {n: usize} fn get() -> Item {Item {n: 42}}} fn main() -> usize {let item: a::Item = a::get(); 42}").unwrap();
        assert_eq!(program.structs[0].name, "a::Item");
        assert!(program.structs[0].opaque);
        assert_eq!(program.functions[0].name, "a::get");
        assert!(
            matches!(&program.functions[0].result.kind, Kind::Record(name, _) if name == "a::Item")
        );
        for source in [
            "module a {module b {fn f() -> usize {0}}}",
            "module a {fn f() -> usize {0}} module a {fn g() -> usize {0}}",
            "module a {fn f() -> usize {0}",
            "opaque type Item struct {} fn main() -> usize {0}",
            "module usize {fn f() -> usize {0}}",
        ] {
            assert!(parse(source).is_err(), "{source}");
        }
        assert!(parse(&format!("fn {}() -> usize {{0}}", "x".repeat(257))).is_err());
    }
    #[test]
    fn parses_calls_branches_and_arrays() {
        let f =
            parse("fn main() -> nat { let a: [nat; 2] = [1, 2]; if true { f(a[0]) } else { 3 } }")
                .unwrap();
        assert!(matches!(f.functions[0].result.kind, Kind::If(..)));
    }
    #[test]
    fn rejects_flat_chains_before_the_expression_tree_can_overflow() {
        for expression in [
            std::iter::repeat_n("1", 300)
                .collect::<Vec<_>>()
                .join(" + "),
            format!("x{}", ".field".repeat(300)),
            format!("x{}", "[0]".repeat(300)),
            format!("x{}", "::known".repeat(300)),
        ] {
            let error = parse(&format!("fn main() -> usize {{{expression}}}")).unwrap_err();
            assert!(error.contains("expression tree depth limit"), "{error}");
        }
        assert!(parse(&format!(
            "fn main() -> usize {{{}}}",
            std::iter::repeat_n("1", 32).collect::<Vec<_>>().join(" + ")
        ))
        .is_ok());
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
