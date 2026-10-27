//! Generic lifetime claims. The total census includes opaque caller owners;
//! source Rc counters and library protocols are not recognized here.

use super::*;

#[cfg(test)]
mod tests;

pub(super) fn census_path() -> Vec<Projection<Linear>> {
    vec![Projection::Owners]
}

impl Context<'_> {
    fn note_census_write(&mut self, reference: Reference) -> Result<()> {
        if !self.storage.loops.is_empty() {
            return Err(
                "ownership transitions in loops need census shape invariants; unsupported".into(),
            );
        }
        self.note_state_write(self.storage.memory.plane(reference)?, &census_path())?;
        self.work.ownership_transitions += 1;
        Ok(())
    }

    pub(super) fn arbitrary_owner(&mut self, ty: &Ty) -> Result<Symbol> {
        let Symbol::Plane(_, reference) = self.arbitrary(&Ty::Plane(Box::new(ty.clone())))? else {
            return Err("owning-reference entry needs an allocation".into());
        };
        let plane = self.storage.memory.plane(reference)?;
        let owner = self.storage.memory.share_owner(plane)?;
        let reference = self.storage.memory.borrow_owned(owner)?;
        // One visible claim does not imply there are no caller-held claims.
        let count = Linear::variable(self.fresh_name());
        self.assume_from(
            &Formula::Ge(count.sub(&Linear::number(1))?),
            paths::Origin::Unresolved,
        )?;
        self.censuses.insert(reference, count);
        Ok(Symbol::Owner(Box::new(ty.clone()), owner))
    }

    pub(super) fn owning_reference(&self, value: &Symbol) -> Result<Reference> {
        match value {
            Symbol::Owner(_, owner) => {
                self.storage.memory.read(owner.reference())?;
                Ok(owner.reference())
            }
            Symbol::Plane(_, reference) => {
                self.storage.memory.read(*reference)?;
                Ok(*reference)
            }
            Symbol::Ref(_, reference, path) => {
                let target = project(self.storage.memory.read(*reference)?, path)?;
                if matches!(target, Symbol::Owner(..) | Symbol::Plane(..)) {
                    self.owning_reference(target)
                } else if path.is_empty() && self.censuses.contains_key(reference) {
                    Ok(*reference)
                } else {
                    Err(
                        "owner census requires an owning pointer or a borrow of its allocation"
                            .into(),
                    )
                }
            }
            _ => {
                Err("owner census requires an owning pointer or a borrow of its allocation".into())
            }
        }
    }

    fn census_value(&self, reference: Reference) -> Result<Linear> {
        if let Some(count) = self.censuses.get(&reference) {
            return Ok(count.clone());
        }
        // A unique plane is the only concrete default. Incoming owner(T)
        // values always carry their abstract total above.
        if self.storage.memory.owner_count(reference)? == 1 {
            Ok(Linear::number(1))
        } else {
            Err("missing symbolic owner census".into())
        }
    }

    pub(super) fn release_owning_reference(
        &mut self,
        owner: crate::shared::planes::OwnedReference,
        line: usize,
    ) -> Result<()> {
        let reference = self.storage.memory.borrow_owned(owner)?;
        let count = self.census_value(reference)?;
        self.prove(
            &Formula::Ge(count.sub(&Linear::number(2))?),
            "releasing an owner leaves another live claim",
            line,
        )?;
        self.note_census_write(reference)?;
        self.storage.memory.release_owner(owner)?;
        self.censuses
            .insert(reference, count.sub(&Linear::number(1))?);
        self.validate_live(line)
    }

    pub(super) fn owner_subject_reference(&self, expression: &Expr) -> Option<Reference> {
        let argument = match &expression.kind {
            Kind::Unary(op, place) if op == "&" => match &place.kind {
                Kind::Unary(op, pointer) if op == "*" => pointer,
                _ => place,
            },
            _ => expression,
        };
        self.stored_hint(argument)
            .and_then(|value| self.owning_reference(value).ok())
    }

    pub(super) fn recover_owning_reference(
        &mut self,
        ty: Box<Ty>,
        owner: crate::shared::planes::OwnedReference,
        line: usize,
    ) -> Result<Symbol> {
        let reference = self.storage.memory.borrow_owned(owner)?;
        let count = self.census_value(reference)?;
        self.prove(
            &equal(&count, &Linear::number(1))?,
            "unique owner recovery",
            line,
        )?;
        let census = self.storage.memory.owner_census(reference)?;
        self.note_census_write(reference)?;
        self.storage.memory.recover_unique_owner_at(owner, census)?;
        self.censuses.remove(&reference);
        Ok(Symbol::Plane(ty, reference))
    }

    pub(super) fn owner_operation(
        &mut self,
        name: &str,
        args: &[Expr],
        line: usize,
    ) -> Result<Symbol> {
        if args.len() != 1 {
            return Err(format!("{name} expects one argument"));
        }
        if name == "owners" {
            if self.execution.phase == Phase::Runtime {
                return Err("owners is an ideal census observation".into());
            }
            let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
            let value = self.eval(&args[0], None);
            self.execution.phase = phase;
            let value = value?;
            let reference = self.owning_reference(&value)?;
            return Ok(Symbol::Number(Ty::Nat, self.census_value(reference)?));
        }
        if self.execution.phase != Phase::Runtime || !self.storage.opened_planes.is_empty() {
            return Err(
                "ownership transitions require runtime execution with closed invariants".into(),
            );
        }
        let value = self.eval(&args[0], None)?;
        let result = match (name, value) {
            ("share_owner", Symbol::Plane(ty, reference)) => {
                let plane = self.storage.memory.plane(reference)?;
                self.note_census_write(reference)?;
                let owner = self.storage.memory.share_owner(plane)?;
                self.censuses.insert(reference, Linear::number(1));
                Ok(Symbol::Owner(ty, owner))
            }
            ("duplicate_owner", Symbol::Ref(_, reference, path)) => {
                let Symbol::Owner(ty, owner) =
                    project(self.storage.memory.read(reference)?, &path)?.clone()
                else {
                    return Err("duplicate_owner expects a borrowed owner(T)".into());
                };
                let reference = self.storage.memory.borrow_owned(owner)?;
                let count = self.census_value(reference)?.add(&Linear::number(1))?;
                self.note_census_write(reference)?;
                let owner = self.storage.memory.duplicate_owner(owner)?;
                self.censuses.insert(reference, count);
                Ok(Symbol::Owner(ty, owner))
            }
            ("release_owner", Symbol::Owner(_, owner)) => {
                self.release_owning_reference(owner, line)?;
                Ok(Symbol::Unit)
            }
            ("recover_owner", Symbol::Owner(ty, owner)) => {
                self.recover_owning_reference(ty, owner, line)
            }
            _ => Err(format!("invalid argument to {name}")),
        }?;
        self.validate_live(line)?;
        Ok(result)
    }
}
