//! Ideal value equality compares record fields and live pointer identities.
//! Indexed operands retain contents identities; no bound cell is materialized.

use super::*;

#[cfg(test)]
mod tests;

enum Value {
    Observed(Symbol),
    Indexed {
        ty: Ty,
        contents: Contents,
        index: Linear,
    },
}

impl Value {
    fn ty(&self) -> Ty {
        match self {
            Self::Observed(value) => value.ty(),
            Self::Indexed { ty, .. } => ty.clone(),
        }
    }

    // This is an ideal observation of pointer identity, not another owner.
    fn reference(&self) -> Result<Symbol> {
        match self {
            Self::Observed(value @ (Symbol::Ref(..) | Symbol::RefCases(..))) => Ok(value.clone()),
            Self::Observed(Symbol::Unique(ty, reference)) => {
                Ok(Symbol::Ref(ty.clone(), *reference, Vec::new()))
            }
            Self::Observed(Symbol::Shared(ty, owner)) => {
                Ok(Symbol::Ref(ty.clone(), owner.reference(), Vec::new()))
            }
            _ => Err("value equality requires an observed live pointer".into()),
        }
    }

    fn field(&self, name: &str, resolve_type: impl FnOnce() -> Result<Ty>) -> Result<Self> {
        match self {
            Self::Observed(Symbol::Record(_, fields)) => Ok(Self::Observed(
                fields
                    .get(name)
                    .ok_or("value equality lost a record field")?
                    .clone(),
            )),
            Self::Indexed {
                contents, index, ..
            } => {
                let mut contents = contents.clone();
                contents.fields.push(name.into());
                Ok(Self::Indexed {
                    ty: resolve_type()?,
                    contents,
                    index: index.clone(),
                })
            }
            _ => Err("value equality projection requires a record".into()),
        }
    }
}

impl Context<'_> {
    pub(in crate::compiler::verify) fn eval_same_value(
        &mut self,
        args: &[Expr],
        line: usize,
    ) -> Result<Symbol> {
        if self.execution.phase == Phase::Runtime {
            return Err(format!("line {line}: same_value is ideal-only"));
        }
        let [a, b] = args else {
            return Err(format!("line {line}: same_value expects two values"));
        };
        // A concrete counterpart supplies the payload type for a union slot.
        // Ordinary evaluation must still prove that this member is active.
        let left = self.hint(a);
        let right = self.hint(b);
        let hint = left
            .as_ref()
            .filter(|ty| !matches!(ty, Ty::Union(_)))
            .or_else(|| right.as_ref().filter(|ty| !matches!(ty, Ty::Union(_))))
            .cloned()
            .or(left)
            .or(right);
        let a = self.structural_operand(a, hint.as_ref())?;
        let b = self.structural_operand(b, Some(&a.ty()))?;
        self.compatible(&a.ty(), &b.ty(), line)?;
        Ok(Symbol::Bool(self.structural_equality(&a, &b, line, 0)?))
    }

    fn structural_operand(&mut self, expression: &Expr, hint: Option<&Ty>) -> Result<Value> {
        if self.locals.quantified_evaluation != 0 {
            if let Some((base, index, fields)) = projections::indexed_parts(expression) {
                let index = self.eval(index, Some(&Ty::Int))?.number()?;
                // A quantified comparison needs the saved contents identity,
                // not live access to the owners formerly stored in that array.
                let array = match &base.kind {
                    Kind::Call(name, arguments) if name == "old" && arguments.len() == 1 => {
                        self.old_expression(&arguments[0], None)?
                    }
                    _ => self.storage(base)?,
                };
                self.charge_value_work(symbol_weight(&array)?)?;
                self.remember_scalar_literal(&array)?;
                let Symbol::Array {
                    element,
                    len,
                    identity,
                    ..
                } = array
                else {
                    return Err("same_value indexed operands require array storage".into());
                };
                let whole = !self.history_element(&element);
                if whole && !fields.is_empty() {
                    return Err(
                        "indexed owning value equality currently compares whole elements".into(),
                    );
                }
                let ty = self.scalar_projection_type(*element, &fields, expression.line)?;
                self.defer_quantified_check(
                    Formula::Ge(index.clone())
                        .and(Formula::Ge(len.sub(&index)?.add(&Linear::number(-1))?)),
                    "quantified array index bounds".into(),
                    expression.line,
                )?;
                return Ok(Value::Indexed {
                    ty,
                    contents: Contents {
                        identity,
                        fields,
                        whole,
                    },
                    index,
                });
            }
        }
        Ok(Value::Observed(self.eval(expression, hint)?))
    }

    fn structural_equality(
        &mut self,
        a: &Value,
        b: &Value,
        line: usize,
        depth: usize,
    ) -> Result<Formula> {
        self.charge_value_work(1)?;
        for value in [a, b] {
            if let Value::Observed(value) = value {
                self.charge_value_work(symbol_weight(value)?)?;
            }
        }
        if depth >= 64 {
            return Err("value equality projection depth limit reached".into());
        }
        if let (
            Value::Indexed {
                contents: left,
                index: a,
                ..
            },
            Value::Indexed {
                contents: right,
                index: b,
                ..
            },
        ) = (a, b)
        {
            if left.whole && right.whole {
                return self.value_equality(&(Some(left.clone()), Some(right.clone())), a, b, 0);
            }
        }
        match a.ty() {
            Ty::Unit => Ok(Formula::True),
            Ty::Record(name) => {
                let fields = self.declarations.structs[&name].fields.clone();
                self.charge_value_work(fields.len())?;
                let mut result = Formula::True;
                for (name, ty) in fields {
                    // Observed fields already carry their instantiated types,
                    // including bounds dependent on sibling record fields.
                    let left = a.field(&name, || self.resolve(&ty))?;
                    let right = b.field(&name, || self.resolve(&ty))?;
                    result =
                        result.and(self.structural_equality(&left, &right, line, depth + 1)?);
                }
                Ok(result)
            }
            Ty::Shape(_) => Ok(Formula::True),
            Ty::Union(_) => self.structural_union_equality(a, b, line, depth),
            Ty::Array(_, _) => self.structural_array_equality(a, b, line, depth),
            Ty::Ref(_) | Ty::Unique(_) | Ty::Shared(_) => {
                self.reference_equality(&a.reference()?, &b.reference()?)
            }
            ty if scalar(&ty) => {
                let a = self.structural_scalar(a)?;
                let b = self.structural_scalar(b)?;
                self.scalar_argument_cases(&a.argument, |ctx, left| {
                    ctx.scalar_argument_cases(&b.argument, |ctx, right| {
                        ctx.value_equality(
                            &(a.contents.clone(), b.contents.clone()),
                            left,
                            right,
                            0,
                        )
                    })
                })
            }
            _ => Err("same_value cannot compare this ideal value kind".into()),
        }
    }

    fn structural_union_equality(
        &mut self,
        a: &Value,
        b: &Value,
        line: usize,
        depth: usize,
    ) -> Result<Formula> {
        let (Value::Observed(left), Value::Observed(right)) = (a, b) else {
            return Err("union value equality requires observed values".into());
        };
        self.validate_argument(left, line)?;
        self.validate_argument(right, line)?;
        if left == right {
            return Ok(Formula::True);
        }
        let (
            Symbol::Union {
                members: a_members,
                active: a_active,
                payloads: a_payloads,
            },
            Symbol::Union {
                members: b_members,
                active: b_active,
                payloads: b_payloads,
            },
        ) = (left, right)
        else {
            return Err("union value equality requires union storage".into());
        };
        if a_members != b_members {
            return Err("union value equality requires matching member types".into());
        }
        let base = self.proof.paths.clone();
        let mut result = Formula::False;
        for (index, (left, right)) in a_payloads.iter().zip(b_payloads).enumerate() {
            self.charge_value_work(1)?;
            let tag = Linear::number(index as i128);
            let guard = equal(a_active, &tag)?.and(equal(b_active, &tag)?);
            self.proof.paths = extend(
                &base,
                &guard,
                false,
                self.session,
                &mut self.work.value_work,
            )?;
            let comparison = (|| {
                let paths = self.proof.paths.clone();
                if self.checked_impossible(&paths, &Formula::True)? {
                    return Ok(Formula::False);
                }
                let (Some(left), Some(right)) = (left, right) else {
                    return Err("union value equality requires an observed active payload".into());
                };
                self.structural_equality(
                    &Value::Observed(left.clone()),
                    &Value::Observed(right.clone()),
                    line,
                    depth + 1,
                )
            })();
            self.proof.paths = base.clone();
            result = result.or(guard.and(comparison?));
        }
        Ok(result)
    }

    fn structural_array_equality(
        &mut self,
        a: &Value,
        b: &Value,
        line: usize,
        depth: usize,
    ) -> Result<Formula> {
        let (
            Value::Observed(
                left @ Symbol::Array {
                    identity: a_id,
                    items: a_items,
                    ..
                },
            ),
            Value::Observed(
                right @ Symbol::Array {
                    identity: b_id,
                    items: b_items,
                    ..
                },
            ),
        ) = (a, b)
        else {
            return Err("whole-array equality requires observed array values".into());
        };
        self.validate_argument(left, line)?;
        self.validate_argument(right, line)?;
        if a_id == b_id {
            return Ok(Formula::True);
        }
        let (Some(a_items), Some(b_items)) = (a_items, b_items) else {
            return Err(
                "sparse array equality requires matching immutable contents identities".into(),
            );
        };
        if a_items.len() != b_items.len() {
            return Ok(Formula::False);
        }
        let mut result = Formula::True;
        for (left, right) in a_items.iter().zip(b_items) {
            result = result.and(self.structural_equality(
                &Value::Observed(left.clone()),
                &Value::Observed(right.clone()),
                line,
                depth + 1,
            )?);
        }
        Ok(result)
    }

    fn structural_scalar(&mut self, value: &Value) -> Result<Operand> {
        let (contents, argument) = match value {
            Value::Observed(value) => {
                self.charge_value_work(symbol_weight(value)?)?;
                (None, self.scalar_argument(value)?)
            }
            Value::Indexed {
                contents, index, ..
            } => {
                if let Some(value) = self.defined_array_value(contents, None, 0)? {
                    (None, self.scalar_argument(&value)?)
                } else {
                    (
                        Some(contents.clone()),
                        scalars::Argument::Word(index.clone()),
                    )
                }
            }
        };
        Ok(Operand {
            ty: value.ty(),
            contents,
            argument,
        })
    }
}
