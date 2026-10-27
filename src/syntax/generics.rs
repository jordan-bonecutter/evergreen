//! Generic declaration syntax. Templates remain separate from concrete
//! declarations until specialization; the proof checker sees concrete code.

use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GenericArgument {
    Type(Type),
    Const(Expr),
}

#[derive(Clone, Debug)]
pub enum GenericParameter {
    Type {
        name: String,
        default: Option<Type>,
    },
    Const {
        name: String,
        ty: Type,
        default: Option<Expr>,
    },
}

impl GenericParameter {
    pub fn name(&self) -> &str {
        match self {
            Self::Type { name, .. } | Self::Const { name, .. } => name,
        }
    }
}

#[derive(Clone, Debug)]
pub enum GenericDeclaration {
    Record {
        parameters: Vec<GenericParameter>,
        definition: Box<Struct>,
    },
    Function {
        parameters: Vec<GenericParameter>,
        definition: Box<Function>,
    },
}

impl Parser {
    pub(super) fn generic_extent(&self, expression: &Expr) -> bool {
        match &expression.kind {
            Kind::Name(name) => self.generic_consts.contains(name),
            Kind::Number(_) | Kind::Constant(..) => true,
            Kind::Unary(op, value) if op == "-" => self.generic_extent(value),
            Kind::Binary(op, a, b) if matches!(op.as_str(), "+" | "-" | "*") => {
                self.generic_extent(a) && self.generic_extent(b)
            }
            _ => false,
        }
    }
    pub(super) fn generic_parameters(&mut self) -> Result<Vec<GenericParameter>, String> {
        if !self.eat("<") {
            return Ok(Vec::new());
        }
        let mut parameters = Vec::new();
        let mut names = std::collections::BTreeSet::new();
        let mut default_seen = false;
        loop {
            if parameters.len() >= 128 {
                return Err(self.err("generic parameter limit reached"));
            }
            let constant = self.eat("const");
            let name = self.name()?;
            if name == "Self" || name == "self" || !names.insert(name.clone()) {
                return Err(
                    self.err("generic parameter names must be distinct and cannot shadow self")
                );
            }
            self.generic_names.insert(name.clone());
            let (parameter, has_default) = if constant {
                self.expect(":")?;
                let ty = self.ty()?;
                let default = if self.eat("=") {
                    Some(self.generic_constant()?)
                } else {
                    None
                };
                let has_default = default.is_some();
                self.generic_consts.insert(name.clone());
                (GenericParameter::Const { name, ty, default }, has_default)
            } else {
                if !name.starts_with(|c: char| c.is_ascii_uppercase()) {
                    return Err(
                        self.err("generic type parameters must start with an uppercase letter")
                    );
                }
                if self.peek() == ":" {
                    return Err(self.err("generic trait bounds are not implemented yet"));
                }
                let default = if self.eat("=") {
                    Some(self.ty()?)
                } else {
                    None
                };
                let has_default = default.is_some();
                (GenericParameter::Type { name, default }, has_default)
            };
            if default_seen && !has_default {
                return Err(self.err("generic defaults must be trailing parameters"));
            }
            default_seen |= has_default;
            parameters.push(parameter);
            if self.eat(">") {
                break;
            }
            self.expect(",")?;
            if self.eat(">") {
                break;
            }
        }
        Ok(parameters)
    }

    fn generic_constant(&mut self) -> Result<Expr, String> {
        if self.eat("{") {
            let value = self.expr(0)?;
            self.expect("}")?;
            Ok(value)
        } else {
            // Greater-than terminates an angle argument, so compound constant
            // expressions use braces rather than the ordinary comparison parser.
            self.expr(7)
        }
    }

    pub(super) fn generic_arguments(&mut self) -> Result<Vec<GenericArgument>, String> {
        self.expect("<")?;
        let mut arguments = Vec::new();
        loop {
            if arguments.len() >= 128 {
                return Err(self.err("generic argument limit reached"));
            }
            let constant = self.peek() == "{"
                || self.generic_consts.contains(self.peek())
                || self.peek() == "-"
                || self.peek().parse::<i128>().is_ok()
                || matches!(self.peek(), "true" | "false")
                || MachineInt::parse(self.peek()).is_some()
                    && self
                        .tokens
                        .get(self.pos + 1)
                        .is_some_and(|token| token.text == "::");
            arguments.push(if constant {
                GenericArgument::Const(self.generic_constant()?)
            } else {
                GenericArgument::Type(self.ty()?)
            });
            if self.eat(">") {
                break;
            }
            self.expect(",")?;
            if self.eat(">") {
                break;
            }
        }
        Ok(arguments)
    }
}
