//! Explicit applications keep their chosen arguments. Implicit free calls use
//! argument shapes; observing a return header does not certify its body.

use super::*;

impl Engine {
    pub(super) fn explicit_arguments(&mut self, expression: &mut Expr) -> Result<()> {
        if let Kind::Generic {
            arguments,
            member,
            value,
        } = &mut expression.kind
        {
            for argument in arguments.iter_mut() {
                self.argument(argument)?;
            }
            match &mut value.kind {
                Kind::Call(name, _) => {
                    *name = if let Some(member) = member.take() {
                        let target = self.specialize(name, std::mem::take(arguments), true)?;
                        format!("{target}::{member}")
                    } else {
                        self.specialize(name, std::mem::take(arguments), false)?
                    };
                }
                Kind::Record(name, _) => {
                    *name = self.specialize(name, std::mem::take(arguments), true)?
                }
                Kind::Name(name) => {
                    value.kind = Kind::Type(Type::Named(self.specialize(
                        name,
                        std::mem::take(arguments),
                        true,
                    )?));
                }
                _ => return Err("invalid generic expression".into()),
            }
            *expression = std::mem::replace(
                value.as_mut(),
                Expr {
                    kind: Kind::Unit,
                    line: expression.line,
                },
            );
        }
        Ok(())
    }

    pub(super) fn infer_call(
        &mut self,
        name: &mut String,
        args: &mut [Expr],
        line: usize,
    ) -> Result<Option<Type>> {
        let mut actual = Vec::new();
        for argument in args.iter_mut() {
            actual.push((None, self.expression(argument)?));
        }
        if self.templates.contains_key(name) {
            let arguments = self.inferred_arguments(name, &actual, line)?;
            *name = self.specialize(name, arguments, false)?;
        } else if let Some((base, member)) = name.rsplit_once("::") {
            if self
                .templates
                .get(base)
                .is_some_and(|t| matches!(t.declaration, GenericDeclaration::Record { .. }))
            {
                *name = format!("{}::{member}", self.specialize(base, Vec::new(), true)?);
            }
        }
        if let Some(machine) = self.target.integer(name) {
            return Ok(Some(Type::Machine(machine)));
        }
        let first = actual.first_mut().and_then(|(_, ty)| ty.take());
        let builtin = match name.as_str() {
            "same_value" | "same_representation" => Some(Type::Bool),
            "transfer_type" => Some(Type::Unit),
            "copy_representation" if args.len() == 3 => Some(Type::Unit),
            "copy_representation" => {
                return Ok(match first {
                    Some(Type::Ref(inner)) => inner
                        .representation_payload()
                        .map(|ty| Type::Shape(Box::new(ty))),
                    _ => None,
                })
            }
            "integer" => Some(Type::Int),
            "nat" | "owner_count" => Some(Type::Nat),
            "size_of" | "align_of" => Some(Type::Machine(self.target.integer("usize").unwrap())),
            "old" | "move" => return Ok(first),
            "alloc" if args.len() == 1 => return Ok(first.map(|t| Type::Unique(Box::new(t)))),
            _ => None,
        };
        if builtin.is_some() {
            return Ok(builtin);
        }
        // Method spelling is lowered later, but a known receiver can
        // already identify its declared return shape.
        let lookup = if let Some(method) = name.strip_prefix("evg_method_") {
            let mut receiver = first;
            while let Some(Type::Ref(t) | Type::Unique(t) | Type::Shared(t)) = receiver {
                receiver = Some(*t);
            }
            match receiver {
                Some(Type::Named(target)) => format!("{target}::{method}"),
                _ => return Ok(None),
            }
        } else {
            name.clone()
        };
        self.read_hint(self.inference.returns.get(&lookup).cloned())
    }
}
