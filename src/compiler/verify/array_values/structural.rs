//! Ideal value equality lowers record products to their scalar projections.
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

    fn field(&self, name: &str, ty: Ty) -> Result<Self> {
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
                    ty,
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
        let hint = self.hint(a).or_else(|| self.hint(b));
        let a = self.structural_operand(a, hint.as_ref())?;
        let b = self.structural_operand(b, Some(&a.ty()))?;
        self.compatible(&a.ty(), &b.ty(), line)?;
        if !self.history_element(&a.ty()) || !self.history_element(&b.ty()) {
            return Err(format!("line {line}: same_value currently requires scalar values or reference-free records without runtime cleanup"));
        }
        Ok(Symbol::Bool(self.structural_equality(&a, &b, 0)?))
    }

    fn structural_operand(&mut self, expression: &Expr, hint: Option<&Ty>) -> Result<Value> {
        if self.locals.quantified_evaluation != 0 {
            if let Some((base, index, fields)) = projections::indexed_parts(expression) {
                let index = self.eval(index, Some(&Ty::Int))?.number()?;
                let array = self.storage(base)?;
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
                if !self.history_element(&element) {
                    return Err("same_value indexed operands require initialized scalar or reference-free record elements without cleanup".into());
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
                    contents: Contents { identity, fields },
                    index,
                });
            }
        }
        Ok(Value::Observed(self.eval(expression, hint)?))
    }

    fn structural_equality(&mut self, a: &Value, b: &Value, depth: usize) -> Result<Formula> {
        self.charge_value_work(1)?;
        for value in [a, b] {
            if let Value::Observed(value) = value {
                self.charge_value_work(symbol_weight(value)?)?;
            }
        }
        if depth >= 64 {
            return Err("value equality projection depth limit reached".into());
        }
        match a.ty() {
            Ty::Unit => Ok(Formula::True),
            Ty::Record(name) => {
                let fields = self.declarations.structs[&name].fields.clone();
                self.charge_value_work(fields.len())?;
                let mut result = Formula::True;
                for (name, ty) in fields {
                    let ty = self.resolve(&ty)?;
                    let left = a.field(&name, ty.clone())?;
                    let right = b.field(&name, ty)?;
                    result = result.and(self.structural_equality(&left, &right, depth + 1)?);
                }
                Ok(result)
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
            _ => Err("same_value requires initialized scalar fields".into()),
        }
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
