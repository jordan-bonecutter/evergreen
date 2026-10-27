//! Shared, source-located syntax for the internal compiler pipeline.

use lexer::{lex, Token};

mod lexer;
mod modules;
mod representation;
mod strings;
pub use representation::{Endianness, IntegralEncoding, Representation, ScalarDefinition};

mod functions;
mod statements;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    Plane(Box<Type>),
    Machine(MachineInt),
    Named(String),
    Array(Box<Type>, Box<Expr>),
    Union(Vec<Type>),
    Shape(Box<Type>),
}

impl Type {
    pub(crate) fn bytes(length: usize, line: usize) -> Self {
        Self::Array(
            Box::new(Self::Machine(MachineInt {
                signed: false,
                bits: 8,
            })),
            Box::new(Expr {
                kind: Kind::Number(length as i128),
                line,
            }),
        )
    }
    /// A pointer-shaped union is unambiguous only with one pointer member.
    /// This selects a type for elaboration; the checker must prove it active.
    pub(crate) fn pointer_member(&self) -> Option<&Type> {
        match self {
            Self::Ref(_) | Self::Plane(_) => Some(self),
            Self::Union(members) => {
                let mut pointers = members
                    .iter()
                    .filter(|ty| matches!(ty, Self::Ref(_) | Self::Plane(_)));
                let pointer = pointers.next()?;
                pointers.next().is_none().then_some(pointer)
            }
            _ => None,
        }
    }

    pub(crate) fn literal_numeric_member(&self) -> Option<&Type> {
        let Self::Union(members) = self else {
            return Some(self);
        };
        let mut numeric = members
            .iter()
            .filter(|ty| matches!(ty, Type::Machine(_) | Type::Int | Type::Nat));
        let first = numeric.next()?;
        numeric.next().is_none().then_some(first)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: Kind,
    pub line: usize,
}

impl Expr {
    pub(crate) fn byte_array(bytes: &[u8], line: usize) -> Self {
        let element = MachineInt {
            signed: false,
            bits: 8,
        };
        Self {
            kind: Kind::Array(
                bytes
                    .iter()
                    .map(|&byte| Self {
                        kind: Kind::Constant(element, i128::from(byte)),
                        line,
                    })
                    .collect(),
            ),
            line,
        }
    }

    /// The syntax of a type used as an ideal value. Resolving names and proving
    /// dependent extents remain the verifier's responsibility.
    pub(crate) fn literal_type(&self) -> Option<Type> {
        match &self.kind {
            Kind::Unit => Some(Type::Unit),
            Kind::Name(name) => Some(MachineInt::parse(name).map(Type::Machine).unwrap_or_else(
                || match name.as_str() {
                    "bool" => Type::Bool,
                    "unit" => Type::Unit,
                    "integer" => Type::Int,
                    "nat" => Type::Nat,
                    _ => Type::Named(name.clone()),
                },
            )),
            Kind::Unary(op, inner) if op == "&" => {
                inner.literal_type().map(|ty| Type::Ref(Box::new(ty)))
            }
            Kind::Call(name, args) if name == "shape" && args.len() == 1 => {
                args[0].literal_type().map(|ty| Type::Shape(Box::new(ty)))
            }
            Kind::Call(name, args) if name == "plane" && args.len() == 1 => {
                args[0].literal_type().map(|ty| Type::Plane(Box::new(ty)))
            }
            _ => None,
        }
    }
    pub(crate) fn indirect_place(&self) -> bool {
        match &self.kind {
            Kind::Index(..) => true,
            Kind::Unary(op, _) if op == "*" => true,
            Kind::Field(base, _) => base.indirect_place(),
            _ => false,
        }
    }

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
    Bytes(Vec<u8>),
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
    Ideal(Box<Statement>),
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
        places: Vec<Expr>,
        lifts: Vec<String>,
        body: Vec<Statement>,
        line: usize,
    },
    While {
        condition: Expr,
        invariant: Expr,
        modifies: Vec<Expr>,
        decreases: Option<Expr>,
        body: Vec<Statement>,
        line: usize,
    },
}

impl Statement {
    pub fn bindings(&self) -> Vec<&str> {
        match self {
            Self::Ideal(binding) => binding.bindings(),
            Self::Let { name, .. } => vec![name],
            Self::Destructure { fields, .. } => {
                fields.iter().map(|(_, name)| name.as_str()).collect()
            }
            _ => Vec::new(),
        }
    }

    pub fn runtime_bindings(
        &self,
        structs: &std::collections::BTreeMap<String, Struct>,
    ) -> Vec<&str> {
        match self {
            Self::Ideal(_) => Vec::new(),
            Self::Destructure { record, fields, .. } => fields
                .iter()
                .filter(|(field, _)| !structs[record].ideal_fields.contains(field))
                .map(|(_, name)| name.as_str())
                .collect(),
            _ => self.bindings(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Struct {
    pub copy: bool,
    pub name: String,
    pub fields: Vec<(String, Type)>,
    pub ideal_fields: std::collections::BTreeSet<String>,
    pub invariant: Option<Expr>,
    pub line: usize,
    pub ideal: bool,
    pub opaque: bool,
    pub module: Option<String>,
    pub facts: Vec<(String, Expr)>,
}

impl Struct {
    pub fn runtime_fields(&self) -> impl Iterator<Item = &(String, Type)> {
        self.fields
            .iter()
            .filter(|(name, _)| !self.ideal_fields.contains(name))
    }
}

#[derive(Clone, Debug)]
pub struct CopyImplementation {
    pub target: String,
    pub module: Option<String>,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Program {
    pub copy_impls: Vec<CopyImplementation>,
    pub imports: std::collections::BTreeSet<String>,
    pub scalar_types: Vec<ScalarDefinition>,
    pub modules: std::collections::BTreeSet<String>,
    pub structs: Vec<Struct>,
    pub functions: Vec<Function>,
    pub destructors: Vec<(String, Function)>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ReturnProjection {
    Field(String),
    Index(usize),
}

#[derive(Clone, Debug)]
pub struct ReturnBorrow {
    /// Empty for a direct reference return; otherwise a path in the returned value.
    pub path: Vec<ReturnProjection>,
    pub reference: Expr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum External {
    Syscall(u32),
    CompareExchange64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MethodReceiver {
    Value,
    Reference,
}

#[derive(Clone, Debug)]
pub struct Function {
    pub impl_target: Option<String>,
    pub receiver: Option<MethodReceiver>,
    pub name: String,
    /// Explicit trusted target operation; no Evergreen body.
    pub external: Option<External>,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub pre: Option<Expr>,
    pub post: Option<Expr>,
    pub decreases: Option<Expr>,
    pub borrows: Vec<ReturnBorrow>,
    pub body: Vec<Statement>,
    pub result: Expr,
    pub proof: Option<Vec<String>>,
    pub line: usize,
    pub drop_target: Option<String>,
    pub ideal: bool,
    pub modifies: Vec<Expr>,
    pub ideal_params: Vec<String>,
    pub module: Option<String>,
    /// Derived by verification: contracts hold on return, but totality is unproved.
    pub partial: bool,
    /// Derived once during verification; compound old(...) needs an entry store.
    pub(crate) entry_memory: bool,
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
                    | "import"
                    | "method"
                    | "opaque"
                    | "ideal"
                    | "if"
                    | "else"
                    | "while"
                    | "invariant"
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
        while self.eat("::") {
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

    // Unlike call arguments, effect and update lists require at least one item.
    fn nonempty_expressions(&mut self) -> Result<Vec<Expr>, String> {
        self.expect("(")?;
        let mut expressions = Vec::new();
        loop {
            expressions.push(self.expr(0)?);
            if self.eat(")") {
                break;
            }
            self.expect(",")?;
        }
        Ok(expressions)
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

    fn array_arguments(&mut self) -> Result<(Type, Expr), String> {
        self.expect("(")?;
        let element = self.ty()?;
        self.expect(",")?;
        let count = self.expr(0)?;
        self.expect(")")?;
        Ok((element, count))
    }

    fn ty(&mut self) -> Result<Type, String> {
        let first = self.type_atom()?;
        if !self.eat("|") {
            return Ok(first);
        }
        let mut members = Vec::new();
        fn append(members: &mut Vec<Type>, ty: Type) {
            match ty {
                Type::Union(nested) => members.extend(nested),
                ty => members.push(ty),
            }
        }
        append(&mut members, first);
        loop {
            append(&mut members, self.type_atom()?);
            if members.len() > 16 {
                return Err(self.err("raw union member limit reached (16)"));
            }
            if !self.eat("|") {
                break;
            }
        }
        Ok(Type::Union(members))
    }

    fn type_atom(&mut self) -> Result<Type, String> {
        if self.depth >= 128 {
            return Err(self.err("syntax nesting limit reached"));
        }
        self.depth += 1;
        let result = if self.eat("&&") {
            // The lexer also uses && for logical conjunction. In a type it is
            // two reference constructors, with both counted toward depth.
            if self.depth >= 128 {
                Err(self.err("syntax nesting limit reached"))
            } else {
                self.depth += 1;
                let nested = self.type_atom();
                self.depth -= 1;
                nested.map(|ty| Type::Ref(Box::new(Type::Ref(Box::new(ty)))))
            }
        } else if self.eat("&") {
            Ok(Type::Ref(Box::new(self.type_atom()?)))
        } else if self.eat("shape") {
            self.expect("(")?;
            let inner = self.ty()?;
            self.expect(")")?;
            if matches!(inner, Type::Shape(_)) {
                return Err(self.err("shape(shape(T)) is not a distinct storage state"));
            }
            Ok(Type::Shape(Box::new(inner)))
        } else if self.eat("array") {
            let (element, count) = self.array_arguments()?;
            if !constant_extent(&count) {
                return Err(self.err("array(T, N) requires a compile-time extent; use linear_plane(T, n) for a runtime-bound pointer"));
            }
            Ok(Type::Array(Box::new(element), Box::new(count)))
        } else if self.eat("linear_plane") {
            let (element, count) = self.array_arguments()?;
            Ok(Type::Ref(Box::new(Type::Array(
                Box::new(element),
                Box::new(count),
            ))))
        } else if self.eat("plane") {
            self.expect("(")?;
            let mut inner = self.ty()?;
            if self.eat(",") {
                let count = self.expr(0)?;
                inner = Type::Array(Box::new(inner), Box::new(count));
            }
            self.expect(")")?;
            Ok(Type::Plane(Box::new(inner)))
        } else if self.eat("(") {
            if self.eat(")") {
                Ok(Type::Unit)
            } else {
                let inner = self.ty()?;
                self.expect(")")?;
                Ok(inner)
            }
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
                "integer" => {
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

    fn named_expression(&mut self, line: usize) -> Result<Kind, String> {
        let mut parts = vec![self.name()?];
        while self.eat("::") {
            if parts.len() >= 128 {
                return Err(self.err("expression tree depth limit reached (128 path segments)"));
            }
            parts.push(self.name()?);
        }
        let name = parts.join("::");
        if self.eat("(") {
            return Ok(Kind::Call(name, self.arguments()?));
        }
        if parts.len() == 2 {
            if let Some(integer) = MachineInt::parse(&parts[0]) {
                let (low, high) = integer.bounds();
                let value = match parts[1].as_str() {
                    "MAX" | "max" => high,
                    "MIN" | "min" => low,
                    _ => return Err(self.err("expected MAX or MIN")),
                };
                return Ok(Kind::Constant(integer, value));
            }
        }
        if parts
            .last()
            .is_some_and(|part| part.starts_with(|c: char| c.is_ascii_uppercase()))
            && self.eat("{")
        {
            return Ok(Kind::Record(name, self.record_fields()?));
        }
        if parts.len() > 1 {
            let field = parts.pop().expect("qualified name");
            return Ok(Kind::FactAt(
                Box::new(Expr {
                    line,
                    kind: Kind::Name(parts.join("::")),
                }),
                field,
            ));
        }
        Ok(Kind::Name(name))
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
        } else if let Some(bytes) = self.tokens[self.pos].bytes.clone() {
            self.pos += 1;
            Expr {
                kind: Kind::Bytes(bytes),
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
                self.named_expression(line)?
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
                let kind = if self.eat("(") {
                    let mut args = vec![lhs];
                    args.extend(self.arguments()?);
                    Kind::Call(format!("evg_method_{field}"), args)
                } else {
                    Kind::Field(Box::new(lhs), field)
                };
                lhs = Expr { kind, line };
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
                "omega" | "rfl" | "simp_all" | "decide" | "assumption" | "trustme"
                | "constructor" | "left" | "right" => s,
                "exact" | "intro" | "apply" => format!("{s} {}", self.name()?),
                "cases" => {
                    let proof = self.name()?;
                    if self.eat("with") {
                        let first = self.name()?;
                        let separator = if self.eat("|") {
                            "|"
                        } else {
                            self.expect(",")?;
                            ","
                        };
                        let second = self.name()?;
                        format!("cases {proof} with {first} {separator} {second}")
                    } else {
                        format!("cases {proof}")
                    }
                }
                _ => return Err(self.err("unsupported proof step; unproven axioms are forbidden")),
            };
            steps.push(step);
            if steps.len() > 1024 {
                return Err(self.err("proof script limit reached (1024 steps)"));
            }
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
            || !function.borrows.is_empty()
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

    fn structure(&mut self, ideal: bool) -> Result<Struct, String> {
        let line = self.line();
        self.expect("type")?;
        let name = self.name()?;
        if !name.starts_with(|c: char| c.is_ascii_uppercase()) {
            return Err(self.err("struct names must start with an uppercase letter"));
        }
        self.expect("struct")?;
        self.expect("{")?;
        let mut fields = Vec::new();
        let mut ideal_fields = std::collections::BTreeSet::new();
        if !self.eat("}") {
            loop {
                let erased = self.eat("ideal");
                let n = self.name()?;
                if erased {
                    ideal_fields.insert(n.clone());
                }
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
            let parenthesized = self.eat("(");
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
            if parenthesized {
                self.expect(")")?;
            }
            Some(value)
        } else {
            None
        };
        self.eat(";");
        Ok(Struct {
            copy: false,
            name,
            fields,
            ideal_fields,
            invariant,
            line,
            ideal,
            facts,
            opaque: false,
            module: None,
        })
    }
}

fn constant_extent(expression: &Expr) -> bool {
    match &expression.kind {
        Kind::Number(_) | Kind::Constant(..) => true,
        Kind::Unary(op, value) if op == "-" => constant_extent(value),
        Kind::Binary(op, left, right) if matches!(op.as_str(), "+" | "-" | "*") => {
            constant_extent(left) && constant_extent(right)
        }
        _ => false,
    }
}

fn parse_unit(source: &str) -> Result<Program, String> {
    if source.len() > 1_000_000 {
        return Err("source exceeds 1 MB bootstrap limit".into());
    }
    let mut p = Parser {
        tokens: lex(source)?,
        pos: 0,
        depth: 0,
    };
    let mut copy_impls = Vec::new();
    let mut imports = std::collections::BTreeSet::new();
    let mut scalar_types = Vec::new();
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    let mut destructors = Vec::new();
    let mut module = None;
    let mut file_module = false;
    let mut modules = std::collections::BTreeSet::new();
    while p.peek() != "<eof>" {
        if p.eat("module") {
            if module.is_some() {
                return Err(p.err("nested modules are not supported yet"));
            }
            let name = p.name()?;
            if MachineInt::parse(&name).is_some()
                || matches!(name.as_str(), "integer" | "nat" | "bool")
            {
                return Err(p.err("module names cannot shadow builtin types"));
            }
            if !modules.insert(name.clone()) {
                return Err(
                    p.err("a module must have one closed definition; reopening is forbidden")
                );
            }
            if p.eat(";") {
                if !functions.is_empty()
                    || !structs.is_empty()
                    || !destructors.is_empty()
                    || !scalar_types.is_empty()
                    || !imports.is_empty()
                    || !copy_impls.is_empty()
                    || modules.len() != 1
                {
                    return Err(p.err("a file module declaration must precede all declarations"));
                }
                file_module = true;
            } else {
                p.expect("{")?;
            }
            module = Some(name);
            continue;
        }
        if p.eat("}") {
            if file_module {
                return Err(p.err("file modules have no closing brace"));
            }
            if module.take().is_none() {
                return Err(p.err("unexpected module closing brace"));
            }
            continue;
        }
        if p.eat("import") {
            if !functions.is_empty()
                || !structs.is_empty()
                || !destructors.is_empty()
                || !scalar_types.is_empty()
                || !copy_impls.is_empty()
            {
                return Err(p.err("imports must precede declarations"));
            }
            let name = p.name()?;
            p.expect(";")?;
            if !imports.insert(name) {
                return Err(p.err("duplicate import"));
            }
            continue;
        }
        let ideal = p.eat("ideal");
        let opaque = p.eat("opaque");
        if p.peek() == "affine" {
            return Err(p.err("the affine modifier is not supported; values move by default unless they implement Copy"));
        }
        if p.peek() == "type"
            && p.tokens
                .get(p.pos + 2)
                .is_some_and(|token| token.text == "=")
        {
            if ideal || opaque {
                return Err(p.err("make_type declarations do not accept ideal or opaque modifiers"));
            }
            let mut definition = p.scalar_definition()?;
            definition.module = module.clone();
            scalar_types.push(definition);
        } else if p.peek() == "type" {
            let mut structure = p.structure(ideal)?;
            if opaque && module.is_none() {
                return Err(p.err("opaque representations require a defining module"));
            }
            structure.opaque = opaque;
            structure.module = module.clone();
            structs.push(structure);
        } else if p.peek() == "impl" {
            if opaque {
                return Err(p.err("opaque modifies type declarations"));
            }
            if ideal {
                return Err(p.err("ideal data has no runtime destructor"));
            }
            if p.tokens
                .get(p.pos + 1)
                .is_some_and(|token| token.text == "Copy")
            {
                let line = p.line();
                p.expect("impl")?;
                p.expect("Copy")?;
                p.expect("for")?;
                let target = p.path_name()?;
                p.expect("{")?;
                p.expect("}")?;
                copy_impls.push(CopyImplementation {
                    target,
                    module: module.clone(),
                    line,
                });
                continue;
            }
            if p.tokens
                .get(p.pos + 1)
                .is_none_or(|token| token.text != "Drop")
            {
                p.expect("impl")?;
                let target = p.path_name()?;
                p.expect("{")?;
                while !p.eat("}") {
                    let ideal = p.eat("ideal");
                    let mut function = p.function(Some(&target), ideal)?;
                    if function.receiver.is_none()
                        && function.params.iter().any(|(name, _)| name == "self")
                    {
                        return Err(p.err("use method or method& for an implicit self receiver"));
                    }
                    function.drop_target = None;
                    function.impl_target = Some(target.clone());
                    function.module = module.clone();
                    functions.push(function);
                }
                continue;
            }
            let (target, mut function) = p.destructor()?;
            function.module = module.clone();
            destructors.push((target, function));
        } else {
            if opaque {
                return Err(p.err("opaque modifies type declarations"));
            }
            let mut function = p.function(None, ideal)?;
            function.module = module.clone();
            functions.push(function);
        }
    }
    if module.is_some() && !file_module {
        return Err(p.err("unterminated module"));
    }
    if functions.is_empty()
        && destructors.is_empty()
        && structs.is_empty()
        && scalar_types.is_empty()
    {
        return Err("expected at least one declaration".into());
    }
    Ok(Program {
        copy_impls,
        imports,
        scalar_types,
        modules,
        structs,
        functions,
        destructors,
    })
}

// An internal framing character, forbidden inside individual source files.
// Keeping unit boundaries preserves file-module scope without rewriting code.
const UNIT_SEPARATOR: char = '\u{1e}';

pub fn join_source_units(sources: &[String]) -> Result<String, String> {
    if sources.iter().any(|source| source.contains(UNIT_SEPARATOR)) {
        return Err("source contains a reserved source-unit separator".into());
    }
    let source = sources.join(&UNIT_SEPARATOR.to_string());
    if source.len() > 1_000_000 {
        return Err("source exceeds 1 MB bootstrap limit".into());
    }
    Ok(source)
}

pub fn parse(source: &str) -> Result<Program, String> {
    if source.len() > 1_000_000 {
        return Err("source exceeds 1 MB bootstrap limit".into());
    }
    let mut units = source
        .split(UNIT_SEPARATOR)
        .filter(|unit| !unit.trim().is_empty());
    let mut program = parse_unit(units.next().unwrap_or_default())?;
    for unit in units {
        let unit = parse_unit(unit)?;
        program.copy_impls.extend(unit.copy_impls);
        program.imports.extend(unit.imports);
        program.scalar_types.extend(unit.scalar_types);
        program.modules.extend(unit.modules);
        program.structs.extend(unit.structs);
        program.functions.extend(unit.functions);
        program.destructors.extend(unit.destructors);
    }
    modules::qualify(&mut program);
    Ok(program)
}

#[cfg(test)]
mod tests;
