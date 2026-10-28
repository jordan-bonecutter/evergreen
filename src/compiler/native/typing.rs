//! Representation checks and expression hints after source verification.

use super::*;

impl Emitter<'_> {
    pub(super) fn compatible(a: &Type, b: &Type) -> Result<bool> {
        if a == b {
            return Ok(true);
        }
        match (a, b) {
            (Type::Shape(a), Type::Shape(b)) => Self::compatible(a, b),
            (Type::Union(a), Type::Union(b)) if a.len() == b.len() => {
                a.iter().try_fold(true, |same, a| {
                    Ok(same
                        && b.iter().try_fold(false, |found, b| {
                            Ok::<_, String>(found || Self::compatible(a, b)?)
                        })?)
                })
            }
            // Source verification already checked pointee compatibility. The
            // native reference ABI is one address even for dependent pointees.
            (Type::Ref(_), Type::Ref(_))
            | (Type::Unique(_), Type::Unique(_))
            | (Type::Shared(_), Type::Shared(_)) => Ok(true),
            (Type::Array(a, al), Type::Array(b, bl)) => {
                Ok(Self::compatible(a, b)?
                    && layout::array_length(al)? == layout::array_length(bl)?)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn hint(&self, e: &Expr) -> Option<Type> {
        match &e.kind {
            Kind::Bytes(bytes) => Some(Type::bytes(bytes.len(), e.line)),
            Kind::Name(n) => self.slots.get(n).map(|local| local.ty.clone()),
            Kind::Record(name, _) => Some(Type::Named(name.clone())),
            Kind::Field(base, name) => self.field(&self.hint(base)?, name).ok().map(|f| f.ty),
            Kind::Index(base, _) => match self.hint(base)? {
                Type::Array(element, _) => Some(*element),
                _ => None,
            },
            Kind::Bool(_) => Some(Type::Bool),
            Kind::Constant(t, _) => Some(Type::Machine(*t)),
            Kind::Unary(op, _) if op == "!" => Some(Type::Bool),
            Kind::Unary(op, x) if op == "&" => self.hint(x).map(|t| Type::Ref(Box::new(t))),
            Kind::Unary(op, x) if op == "*" => match self.hint(x)?.pointer_member()? {
                Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) => {
                    Some(*inner.clone())
                }
                _ => None,
            },
            Kind::Unary(_, x) => self.hint(x),
            Kind::Binary(op, _, _)
                if matches!(
                    op.as_str(),
                    "==" | "!=" | "<" | ">" | "<=" | ">=" | "&&" | "||" | "=>"
                ) =>
            {
                Some(Type::Bool)
            }
            Kind::Binary(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::Call(n, _) if MachineInt::parse(n).is_some() => {
                MachineInt::parse(n).map(Type::Machine)
            }
            Kind::Call(name, _) if matches!(name.as_str(), "size_of" | "align_of") => {
                Some(Type::Machine(MachineInt::parse("usize").unwrap()))
            }
            Kind::Call(name, args) if name == "shape" && args.len() == 1 => {
                args[0].literal_type().map(|ty| Type::Shape(Box::new(ty)))
            }
            Kind::Call(n, args) if n == "alloc" && args.len() == 1 => {
                self.hint(&args[0]).map(|t| Type::Unique(Box::new(t)))
            }
            Kind::Call(n, _) => self.functions.get(n).map(|f| f.ret.clone()),
            Kind::If(_, a, b) => self.hint(a).or_else(|| self.hint(b)),
            Kind::Block(_, tail) => self.hint(tail),
            _ => None,
        }
    }
}
