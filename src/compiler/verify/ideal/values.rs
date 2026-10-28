use super::*;
use std::sync::Arc;

#[derive(Clone)]
pub(super) enum Value<'a> {
    Number(Ty, i128),
    Bool(bool),
    SymbolicNumber(Ty, Arc<Linear>),
    SymbolicBool(Arc<Formula>),
    Unit,
    Array(aggregate::Array<'a>),
    Record(&'a str, &'a BTreeMap<String, Symbol>),
    Reference(Box<Ty>, Reference, Vec<Projection<Linear>>, Arc<Value<'a>>),
}

impl Value<'_> {
    pub(super) fn ty(&self) -> Ty {
        match self {
            Self::Number(ty, _) | Self::SymbolicNumber(ty, _) => ty.clone(),
            Self::Bool(_) | Self::SymbolicBool(_) => Ty::Bool,
            Self::Unit => Ty::Unit,
            Self::Array(array) => array.ty(),
            Self::Record(name, _) => Ty::Record((*name).to_owned()),
            Self::Reference(ty, ..) => Ty::Ref(ty.clone()),
        }
    }

    pub(super) fn scalar(self) -> Option<Symbol> {
        match self {
            Self::Number(ty, n) => Some(Symbol::Number(ty, Linear::number(n))),
            Self::Bool(b) => Some(Symbol::Bool(if b { Formula::True } else { Formula::False })),
            Self::SymbolicNumber(ty, n) => Some(Symbol::Number(ty, Arc::unwrap_or_clone(n))),
            Self::SymbolicBool(p) => Some(Symbol::Bool(Arc::unwrap_or_clone(p))),
            Self::Unit => Some(Symbol::Unit),
            _ => None,
        }
    }

    pub(super) fn number(&self) -> Result<i128> {
        match self {
            Self::Number(_, n) => Ok(*n),
            _ => Err("ideal reduction expected a number".into()),
        }
    }

    pub(super) fn boolean(&self) -> Result<bool> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => Err("ideal reduction expected a Boolean".into()),
        }
    }

    pub(super) fn checked_number(ty: Ty, n: i128) -> Result<Self> {
        let valid = match &ty {
            Ty::Nat => n >= 0,
            Ty::Machine(machine) => {
                let (low, high) = machine.bounds();
                low <= n && n <= high
            }
            Ty::Int => true,
            _ => false,
        };
        if !valid {
            return Err("ideal definition evaluation produced an unrepresentable number".into());
        }
        Ok(Self::Number(ty, n))
    }
}

pub(super) struct Budget {
    pub(super) spent: usize,
    remaining: usize,
}

impl Budget {
    pub(super) fn new(remaining: usize) -> Self {
        Self {
            spent: 0,
            remaining,
        }
    }
    pub(super) fn tick(&mut self) -> Result<()> {
        self.spend(1)
    }
    pub(super) fn spend(&mut self, amount: usize) -> Result<()> {
        if self.remaining < amount {
            return Err("ideal definition evaluation work limit reached".into());
        }
        self.remaining -= amount;
        self.spent += amount;
        Ok(())
    }
}

pub(super) struct Importer<'a, 'c, 'b> {
    context: &'a Context<'c>,
    budget: &'b mut Budget,
    references: BTreeMap<(Reference, Vec<Projection<Linear>>), Arc<Value<'a>>>,
    visiting: BTreeSet<(Reference, Vec<Projection<Linear>>)>,
}

impl<'a, 'c, 'b> Importer<'a, 'c, 'b> {
    pub(super) fn new(context: &'a Context<'c>, budget: &'b mut Budget) -> Self {
        Self {
            context,
            budget,
            references: BTreeMap::new(),
            visiting: BTreeSet::new(),
        }
    }

    pub(super) fn value(&mut self, value: &'a Symbol, depth: usize) -> Result<Option<Value<'a>>> {
        self.budget.tick()?;
        if depth >= 128 {
            return Ok(None);
        }
        Ok(Some(match value {
            Symbol::Number(ty, n) if n.terms.is_empty() => {
                Value::checked_number(ty.clone(), n.constant)?
            }
            Symbol::Number(ty, n) => {
                self.budget.spend(n.terms.len().saturating_add(1))?;
                Value::SymbolicNumber(ty.clone(), Arc::new(n.clone()))
            }
            Symbol::Bool(p) => match closed_boolean(p) {
                Some(b) => Value::Bool(b),
                None => {
                    self.budget.spend(p.storage_weight()?)?;
                    Value::SymbolicBool(Arc::new(p.clone()))
                }
            },
            Symbol::Unit => Value::Unit,
            Symbol::Array { .. } => Value::Array(aggregate::Array::Stored(value)),
            Symbol::Record(name, fields) => Value::Record(name, fields),
            Symbol::Ref(ty, reference, path) => {
                if path
                    .iter()
                    .any(|p| matches!(p, Projection::Index(i) if !i.terms.is_empty()))
                {
                    return Ok(None);
                }
                let key = (*reference, path.clone());
                let target = if let Some(value) = self.references.get(&key) {
                    Arc::clone(value)
                } else {
                    if !self.visiting.insert(key.clone()) {
                        return Ok(None);
                    }
                    let source = project(self.context.storage.memory.read(*reference)?, path)?;
                    let Some(target) = self.value(source, depth + 1)? else {
                        return Ok(None);
                    };
                    let target = Arc::new(target);
                    self.visiting.remove(&key);
                    self.references.insert(key, Arc::clone(&target));
                    target
                };
                Value::Reference(ty.clone(), *reference, path.clone(), target)
            }
            _ => return Ok(None),
        }))
    }
}

pub(super) fn closed_boolean(p: &Formula) -> Option<bool> {
    Some(match p {
        Formula::True => true,
        Formula::False => false,
        Formula::Ge(n) if n.terms.is_empty() => n.constant >= 0,
        Formula::And(a, b) => closed_boolean(a)? && closed_boolean(b)?,
        Formula::Or(a, b) => closed_boolean(a)? || closed_boolean(b)?,
        Formula::Not(p) => !closed_boolean(p)?,
        Formula::Implies(a, b) => !closed_boolean(a)? || closed_boolean(b)?,
        _ => return None,
    })
}
