//! An explicit evaluation stack for the read-only scalar/array observation
//! fragment. Unsupported computation falls back to the checked source contract.

use super::*;

struct Frame<'a> {
    function: &'a Function,
    locals: BTreeMap<String, Value<'a>>,
    entry: BTreeMap<String, Value<'a>>,
}

enum Task<'a> {
    Body(usize, usize),
    Expression(&'a Expr, usize, Option<Ty>, bool),
    Bind(&'a str, usize),
    Discard,
    Unary(&'a str),
    Binary(&'a str),
    Convert(Ty),
    Index,
    Field(&'a str),
    Branch(&'a Expr, &'a Expr, usize, Option<Ty>, bool),
    Invoke(&'a Function, Vec<&'a str>),
    Return(usize),
}

pub(super) fn run<'a>(
    context: &'a Context<'_>,
    function: &Function,
    arguments: BTreeMap<String, Value<'a>>,
    budget: &mut Budget,
) -> Result<Option<Value<'a>>> {
    start(context, function, arguments, budget, false)
}

/// Evaluate the declared precondition in the actual argument environment,
/// without installing a callee scope in the verifier or importing any contracts.
pub(super) fn precondition<'a>(
    context: &'a Context<'_>,
    function: &Function,
    arguments: BTreeMap<String, Value<'a>>,
    budget: &mut Budget,
) -> Result<Option<Value<'a>>> {
    start(context, function, arguments, budget, true)
}

fn start<'a>(
    context: &'a Context<'_>,
    function: &Function,
    arguments: BTreeMap<String, Value<'a>>,
    budget: &mut Budget,
    precondition: bool,
) -> Result<Option<Value<'a>>> {
    let function = context
        .declarations
        .functions
        .get(&function.name)
        .ok_or("missing ideal definition")?;
    let entry = if precondition {
        Task::Expression(
            function.pre.as_ref().ok_or("missing ideal precondition")?,
            0,
            Some(Ty::Bool),
            false,
        )
    } else {
        Task::Body(0, 0)
    };
    let mut machine = Machine {
        context,
        budget,
        frames: vec![Frame {
            function,
            entry: arguments.clone(),
            locals: arguments,
        }],
        pending: vec![Task::Return(0), entry],
        values: Vec::new(),
    };
    while let Some(task) = machine.pending.pop() {
        machine.budget.tick()?;
        if !machine.step(task)? {
            return Ok(None);
        }
    }
    if machine.values.len() != 1 {
        return Err("ideal evaluation value stack mismatch".into());
    }
    Ok(machine.values.pop())
}

struct Machine<'a, 'c, 'b> {
    context: &'a Context<'c>,
    budget: &'b mut Budget,
    frames: Vec<Frame<'a>>,
    pending: Vec<Task<'a>>,
    values: Vec<Value<'a>>,
}

impl<'a> Machine<'a, '_, '_> {
    fn step(&mut self, task: Task<'a>) -> Result<bool> {
        match task {
            Task::Return(frame) => {
                if frame + 1 != self.frames.len() {
                    return Err("ideal evaluation frame mismatch".into());
                }
                self.frames.pop();
            }
            Task::Body(frame, index) => return self.body(frame, index),
            Task::Bind(name, frame) => {
                self.frames[frame]
                    .locals
                    .insert(name.into(), pop(&mut self.values)?);
            }
            Task::Discard => {
                pop(&mut self.values)?;
            }
            Task::Branch(yes, no, frame, expected, entry) => {
                let condition = pop(&mut self.values)?;
                // Do not speculate through an unknown branch: its untaken arm
                // may need bounds or recursion facts that do not hold here.
                let Value::Bool(condition) = condition else {
                    return Ok(false);
                };
                let branch = if condition { yes } else { no };
                self.pending
                    .push(Task::Expression(branch, frame, expected, entry));
            }
            Task::Unary(op) => {
                let value = pop(&mut self.values)?;
                if symbolic::is_symbolic(&value) {
                    let Some(value) = symbolic::unary(op, value, self.budget)? else {
                        return Ok(false);
                    };
                    self.values.push(value);
                    return Ok(true);
                }
                self.values.push(match (op, value) {
                    ("!", Value::Bool(b)) => Value::Bool(!b),
                    ("-", Value::Number(ty, n)) => {
                        let Some(n) = n.checked_neg() else {
                            return Ok(false);
                        };
                        Value::checked_number(ty, n)?
                    }
                    ("*", Value::Reference(_, _, _, target)) => (*target).clone(),
                    _ => return Ok(false),
                });
            }
            Task::Binary(op) => {
                let right = pop(&mut self.values)?;
                let left = pop(&mut self.values)?;
                let Some(value) = binary(op, left, right, self.budget)? else {
                    return Ok(false);
                };
                self.values.push(value);
            }
            Task::Convert(ty) => {
                let value = pop(&mut self.values)?;
                let Some(value) = symbolic::convert(ty, value)? else {
                    return Ok(false);
                };
                self.values.push(value);
            }
            Task::Index => {
                let index = pop(&mut self.values)?;
                if symbolic::is_symbolic(&index) {
                    return Ok(false);
                }
                let index =
                    usize::try_from(index.number()?).map_err(|_| "invalid ideal array index")?;
                let Value::Array(array) = pop(&mut self.values)? else {
                    return Ok(false);
                };
                let Some(value) = aggregate::select(self.context, self.budget, array, index)?
                else {
                    return Ok(false);
                };
                self.values.push(value);
            }
            Task::Field(name) => {
                let Value::Record(_, fields) = pop(&mut self.values)? else {
                    return Ok(false);
                };
                let source = fields.get(name).ok_or("missing ideal record field")?;
                let Some(value) = Importer::new(self.context, self.budget).value(source, 0)? else {
                    return Ok(false);
                };
                self.values.push(value);
            }
            Task::Invoke(function, names) => return self.invoke(function, names),
            Task::Expression(expression, frame, expected, entry) => {
                return self.expression(expression, frame, expected, entry)
            }
        }
        Ok(true)
    }

    fn body(&mut self, frame: usize, index: usize) -> Result<bool> {
        let function = self.frames[frame].function;
        if let Some(statement) = function.body.get(index) {
            self.pending.push(Task::Body(frame, index + 1));
            let statement = if let Statement::Ideal(inner) = statement {
                if !function.ideal {
                    return Ok(true);
                }
                inner.as_ref()
            } else {
                statement
            };
            match statement {
                Statement::Fact { .. } | Statement::Proof { .. } => {}
                Statement::Effect(expression) => {
                    self.pending.extend([
                        Task::Discard,
                        Task::Expression(expression, frame, None, false),
                    ]);
                }
                Statement::Let { name, ty, value } => {
                    self.pending.push(Task::Bind(name, frame));
                    self.pending.push(Task::Expression(
                        value,
                        frame,
                        ty.as_ref().and_then(Context::declared_hint),
                        false,
                    ));
                }
                Statement::Assign {
                    target:
                        Expr {
                            kind: Kind::Name(name),
                            ..
                        },
                    value,
                    starts,
                } if starts.is_empty() => {
                    let expected = self.frames[frame].locals.get(name).map(Value::ty);
                    self.pending.push(Task::Bind(name, frame));
                    self.pending
                        .push(Task::Expression(value, frame, expected, false));
                }
                _ => return Ok(false),
            }
        } else {
            self.pending.push(Task::Expression(
                &function.result,
                frame,
                Context::declared_hint(&function.ret),
                false,
            ));
        }

        Ok(true)
    }

    fn invoke(&mut self, function: &'a Function, names: Vec<&'a str>) -> Result<bool> {
        if !eligible(self.context, function) {
            return Ok(false);
        }
        let begin = self
            .values
            .len()
            .checked_sub(names.len())
            .ok_or("missing ideal actuals")?;
        let mut arguments = names
            .into_iter()
            .map(str::to_owned)
            .zip(self.values.drain(begin..))
            .collect::<BTreeMap<_, _>>();
        for (name, ty) in &function.params {
            if arguments.contains_key(name) {
                continue;
            }
            if !function.ideal_params.contains(name) {
                return Ok(false);
            }
            let mut candidates = Vec::new();
            for (parameter, formal) in &function.params {
                if let Some(value) = arguments.get(parameter) {
                    parameters::infer_extent(formal, &value.ty(), name, &mut candidates);
                }
            }
            let Some(first) = candidates.first() else {
                return Ok(false);
            };
            if candidates.iter().any(|n| n != first) {
                return Ok(false);
            }
            let Some(ty) = Context::declared_hint(ty) else {
                return Ok(false);
            };
            self.budget.spend(first.terms.len().saturating_add(1))?;
            let value = if first.terms.is_empty() {
                Value::checked_number(ty, first.constant)?
            } else {
                Value::SymbolicNumber(ty, std::sync::Arc::new(first.clone()))
            };
            arguments.insert(name.clone(), value);
        }
        if self.frames.len() >= 8192 {
            return Err("ideal definition evaluation frame limit reached (8192)".into());
        }
        let frame = self.frames.len();
        self.frames.push(Frame {
            function,
            entry: arguments.clone(),
            locals: arguments,
        });
        self.pending
            .extend([Task::Return(frame), Task::Body(frame, 0)]);

        Ok(true)
    }

    fn expression(
        &mut self,
        expression: &'a Expr,
        frame: usize,
        expected: Option<Ty>,
        entry: bool,
    ) -> Result<bool> {
        let locals = if entry {
            &self.frames[frame].entry
        } else {
            &self.frames[frame].locals
        };
        let default_number = if self.frames[frame].function.ideal {
            Ty::Int
        } else {
            Ty::Machine(MachineInt::parse("isize").unwrap())
        };
        match &expression.kind {
            Kind::Name(name) => match locals.get(name) {
                Some(value) => self.values.push(value.clone()),
                None => return Ok(false),
            },
            Kind::Number(n) => self.values.push(Value::checked_number(
                expected
                    .filter(|ty| matches!(ty, Ty::Int | Ty::Nat | Ty::Machine(_)))
                    .unwrap_or(default_number),
                *n,
            )?),
            Kind::Constant(ty, n) => self
                .values
                .push(Value::checked_number(Ty::Machine(*ty), *n)?),
            Kind::Bool(b) => self.values.push(Value::Bool(*b)),
            Kind::Unit => self.values.push(Value::Unit),
            Kind::Bytes(bytes) => self
                .values
                .push(Value::Array(aggregate::Array::Bytes(bytes))),
            Kind::Field(base, name) => {
                self.pending.extend([
                    Task::Field(name),
                    Task::Expression(base, frame, None, entry),
                ]);
            }
            Kind::Index(base, index) => {
                self.pending.extend([
                    Task::Index,
                    Task::Expression(index, frame, Some(Ty::Nat), entry),
                    Task::Expression(base, frame, None, entry),
                ]);
            }
            Kind::Unary(op, value) if matches!(op.as_str(), "*" | "-" | "!") => {
                let hint = if op == "!" {
                    Some(Ty::Bool)
                } else if op == "-" {
                    expected.or_else(|| hint(value, locals, self.context))
                } else {
                    None
                };
                self.pending
                    .extend([Task::Unary(op), Task::Expression(value, frame, hint, entry)]);
            }
            Kind::Binary(op, a, b) => {
                let arithmetic = matches!(op.as_str(), "+" | "-" | "*");
                let ty = if matches!(op.as_str(), "&&" | "||" | "=>") {
                    Ty::Bool
                } else {
                    (if arithmetic { expected } else { None })
                        .or_else(|| hint(a, locals, self.context))
                        .or_else(|| hint(b, locals, self.context))
                        .unwrap_or(default_number)
                };
                self.pending.extend([
                    Task::Binary(op),
                    Task::Expression(b, frame, Some(ty.clone()), entry),
                    Task::Expression(a, frame, Some(ty), entry),
                ]);
            }
            Kind::If(condition, yes, no) => {
                self.pending.extend([
                    Task::Branch(yes, no, frame, expected, entry),
                    Task::Expression(condition, frame, Some(Ty::Bool), entry),
                ]);
            }
            Kind::Call(name, args) => {
                if name == "old" && args.len() == 1 {
                    self.pending
                        .push(Task::Expression(&args[0], frame, expected, true));
                } else if let Some(ty) =
                    MachineInt::parse(name)
                        .map(Ty::Machine)
                        .or(match name.as_str() {
                            "nat" => Some(Ty::Nat),
                            "integer" => Some(Ty::Int),
                            _ => None,
                        })
                {
                    let [argument] = args.as_slice() else {
                        return Ok(false);
                    };
                    let source = hint(argument, locals, self.context);
                    self.pending.extend([
                        Task::Convert(ty),
                        Task::Expression(argument, frame, source, entry),
                    ]);
                } else {
                    let Some(function) = self.context.declarations.functions.get(name) else {
                        return Ok(false);
                    };
                    if !eligible(self.context, function) {
                        return Ok(false);
                    }
                    let parameters = function.supplied_parameters(args.len())?;
                    self.pending.push(Task::Invoke(
                        function,
                        parameters.iter().map(|(name, _)| name.as_str()).collect(),
                    ));
                    for (argument, (_, ty)) in args.iter().zip(parameters).rev() {
                        self.pending.push(Task::Expression(
                            argument,
                            frame,
                            Context::declared_hint(ty),
                            entry,
                        ));
                    }
                }
            }
            _ => return Ok(false),
        }

        Ok(true)
    }
}

fn pop<'a>(values: &mut Vec<Value<'a>>) -> Result<Value<'a>> {
    values
        .pop()
        .ok_or_else(|| "ideal evaluation value stack underflow".into())
}

fn hint(
    expression: &Expr,
    locals: &BTreeMap<String, Value<'_>>,
    context: &Context<'_>,
) -> Option<Ty> {
    match &expression.kind {
        Kind::Name(name) => locals.get(name).map(Value::ty),
        Kind::Constant(ty, _) => Some(Ty::Machine(*ty)),
        Kind::Bool(_) => Some(Ty::Bool),
        Kind::Bytes(bytes) => Context::declared_hint(&Type::bytes(bytes.len(), expression.line)),
        Kind::Unary(op, base) if op == "*" => match hint(base, locals, context)? {
            Ty::Ref(ty) => Some(*ty),
            _ => None,
        },
        Kind::Index(base, _) => match hint(base, locals, context)? {
            Ty::Array(ty, _) => Some(*ty),
            _ => None,
        },
        Kind::Field(base, field) => {
            let Ty::Record(name) = hint(base, locals, context)? else {
                return None;
            };
            context
                .declarations
                .structs
                .get(&name)?
                .fields
                .iter()
                .find(|(name, _)| name == field)
                .and_then(|(_, ty)| Context::declared_hint(ty))
        }
        Kind::Call(name, _) => {
            MachineInt::parse(name)
                .map(Ty::Machine)
                .or_else(|| match name.as_str() {
                    "nat" => Some(Ty::Nat),
                    "integer" => Some(Ty::Int),
                    _ => context
                        .declarations
                        .functions
                        .get(name)
                        .and_then(|f| Context::declared_hint(&f.ret)),
                })
        }
        Kind::If(_, a, b) | Kind::Binary(_, a, b) => {
            hint(a, locals, context).or_else(|| hint(b, locals, context))
        }
        Kind::Unary(_, inner) => hint(inner, locals, context),
        _ => None,
    }
}

fn binary<'a>(
    op: &str,
    a: Value<'a>,
    b: Value<'a>,
    budget: &mut Budget,
) -> Result<Option<Value<'a>>> {
    if symbolic::is_symbolic(&a) || symbolic::is_symbolic(&b) {
        return symbolic::binary(op, a, b, budget);
    }
    if matches!(op, "&&" | "||" | "=>") {
        let (a, b) = (a.boolean()?, b.boolean()?);
        return Ok(Some(Value::Bool(match op {
            "&&" => a && b,
            "||" => a || b,
            _ => !a || b,
        })));
    }
    if matches!(op, "==" | "!=") {
        let equal = match (&a, &b) {
            (Value::Number(_, a), Value::Number(_, b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Reference(_, a, ap, _), Value::Reference(_, b, bp, _)) => a == b && ap == bp,
            (Value::Unit, Value::Unit) => true,
            _ => return Err("unsupported ideal equality".into()),
        };
        return Ok(Some(Value::Bool(if op == "==" { equal } else { !equal })));
    }
    let Value::Number(ty, a) = a else {
        return Err("ideal arithmetic requires numbers".into());
    };
    let b = b.number()?;
    let number = match op {
        "+" => a.checked_add(b),
        "-" => a
            .checked_sub(b)
            .map(|n| if ty == Ty::Nat { n.max(0) } else { n }),
        "*" => a.checked_mul(b),
        "<" => return Ok(Some(Value::Bool(a < b))),
        "<=" => return Ok(Some(Value::Bool(a <= b))),
        ">" => return Ok(Some(Value::Bool(a > b))),
        ">=" => return Ok(Some(Value::Bool(a >= b))),
        _ => return Err("unsupported ideal operator".into()),
    };
    let Some(number) = number else {
        return Ok(None);
    };
    Value::checked_number(ty, number).map(Some)
}
