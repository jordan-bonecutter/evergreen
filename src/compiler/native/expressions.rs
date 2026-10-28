//! Expression dispatch and result representation checks after specialized lowering.

use super::*;

impl Emitter<'_> {
    pub(super) fn expr(&mut self, e: &Expr, expected: Option<&Type>) -> Result<Type> {
        let ty = match &e.kind {
            Kind::Bytes(bytes) => self.expr(
                &Expr::byte_array(bytes, e.line),
                Some(&Type::bytes(bytes.len(), e.line)),
            )?,
            Kind::Number(n) => {
                self.immediate(*n as u64);
                expected
                    .and_then(Type::literal_numeric_member)
                    .cloned()
                    .unwrap_or_else(machine)
            }
            Kind::Constant(t, n) => {
                self.immediate(*n as u64);
                Type::Machine(*t)
            }
            Kind::Bool(b) => {
                self.immediate(u64::from(*b));
                Type::Bool
            }
            Kind::Unit => {
                self.immediate(0);
                Type::Unit
            }
            Kind::Name(n) => {
                let ty = self.load(n)?;
                if crate::shared::ownership::is_move_only(&ty, self.structs, self.drops) {
                    self.mark_moved(n);
                }
                ty
            }
            Kind::Record(name, entries) => self.record_literal(name, entries)?,
            Kind::Field(..) => self.storage_value(e)?,
            Kind::Array(items) => self.array_literal(items, expected, e.line)?,
            Kind::Index(base, index) => {
                let borrowed = base.stored_place();
                let ty = self.index_address(
                    base,
                    index,
                    if borrowed {
                        ReadMode::Place
                    } else {
                        ReadMode::Value
                    },
                )?;
                if layout::aggregate(&ty) && borrowed {
                    self.snapshot(&ty)?;
                } else if !layout::aggregate(&ty) {
                    self.load_scalar(&ty)?;
                }
                ty
            }
            Kind::Unary(op, x) if op == "&" => Type::Ref(Box::new(self.address(x)?)),
            Kind::Unary(op, x) if op == "*" => {
                let inner = match self.pointer_operand(x)? {
                    Type::Ref(inner) | Type::Unique(inner) | Type::Shared(inner) => inner,
                    _ => {
                        return Err("native dereference requires a reference or owned plane".into())
                    }
                };
                self.snapshot(&inner)?;
                *inner
            }
            Kind::Unary(op, x) if op == "!" => self.logical_not(x)?,
            Kind::Unary(op, x) if op == "-" => self.negate(x, expected)?,
            Kind::Binary(op, a, b) => self.binary(op, a, b, expected)?,
            Kind::If(condition, yes, no) => self.conditional_value(condition, yes, no, expected)?,
            Kind::Block(body, tail) => self.block_value(body, tail, expected)?,
            Kind::Call(name, args) => self.call_expression(name, args, expected)?,
            _ => {
                return Err(format!(
                    "line {}: this expression is not supported by the scalar native backend",
                    e.line
                ))
            }
        };
        let ty = self.union_value(ty, expected)?;
        layout::of(&ty, self.structs)?;
        if let Some(expected) = expected {
            if !Self::compatible(expected, &ty)? {
                return Err(format!("line {}: native type mismatch", e.line));
            }
        }
        if self.code.len() > MAX_CODE {
            return Err("native code exceeds 8 MiB limit".into());
        }
        Ok(ty)
    }
}
