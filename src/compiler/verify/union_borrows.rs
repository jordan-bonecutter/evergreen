//! A member view retains the original address and a checked interpretation.
//! Selecting a view never transfers payloads or creates ownership claims.

use super::*;

#[cfg(test)]
mod tests;

impl Context<'_> {
    pub(super) fn validate_member_path(
        &mut self,
        reference: Reference,
        path: &[Projection],
        line: usize,
    ) -> Result<()> {
        self.charge_value_work(path.len())?;
        for (offset, step) in path.iter().enumerate() {
            let Projection::Member { index, expected } = step else {
                continue;
            };
            self.charge_value_work(offset.saturating_add(1))?;
            let Symbol::Union {
                members,
                active,
                payloads,
            } = project(self.storage.memory.read(reference)?, &path[..offset])?
            else {
                return Err(format!(
                    "line {line}: union member view no longer refers to union storage"
                ));
            };
            if members.get(*index) != Some(expected)
                || payloads.get(*index).and_then(Option::as_ref).is_none()
            {
                return Err(format!(
                    "line {line}: union member view interpretation type changed"
                ));
            }
            let active = active.clone();
            self.prove(
                &equal(&active, &Linear::number(*index as i128))?,
                "union member view requires its current active type",
                line,
            )?;
        }
        Ok(())
    }

    pub(super) fn dormant_member_path(
        &mut self,
        reference: Reference,
        path: &[Projection],
    ) -> Result<bool> {
        self.charge_value_work(path.len())?;
        for (offset, step) in path.iter().enumerate() {
            let Projection::Member { index, expected } = step else {
                continue;
            };
            self.charge_value_work(offset.saturating_add(1))?;
            let Ok(Symbol::Union {
                members,
                active,
                payloads,
            }) = self
                .storage
                .memory
                .read(reference)
                .and_then(|root| project(root, &path[..offset]))
            else {
                return Ok(true);
            };
            if members.get(*index) != Some(expected)
                || payloads.get(*index).and_then(Option::as_ref).is_none()
            {
                return Ok(true);
            }
            let active = active.clone();
            if !self.checked_entails(&equal(&active, &Linear::number(*index as i128))?)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn borrow_union_member(
        &mut self,
        value: Symbol,
        target: &Ty,
        line: usize,
    ) -> Result<Symbol> {
        let mut selected = Vec::new();
        let base = self.proof.paths.clone();
        for mut case in guarded_references::cases(&value)? {
            self.proof.paths = extend(
                &base,
                &case.guard,
                false,
                self.session,
                &mut self.work.value_work,
            )?;
            let result: Result<Option<guarded_references::Case>> = (|| {
                let paths = self.proof.paths.clone();
                if self.checked_impossible(&paths, &Formula::True)? {
                    return Ok(None);
                }
                self.validate_member_path(case.reference, &case.path, line)?;
                let Symbol::Union {
                    members,
                    active,
                    payloads,
                } = project(self.storage.memory.read(case.reference)?, &case.path)?
                else {
                    return Err("member borrows require current union storage".into());
                };
                let index = members
                    .iter()
                    .position(|member| member == target)
                    .ok_or("reference target is not a raw union member")?;
                if payloads[index].is_none() {
                    return Err("union member has no accessible payload".into());
                }
                let expected = members[index].clone();
                let active = active.clone();
                self.prove(
                    &equal(&active, &Linear::number(index as i128))?,
                    "borrowing an active raw union member",
                    line,
                )?;
                case.path.push(Projection::Member { index, expected });
                Ok(Some(case))
            })();
            self.proof.paths = base.clone();
            selected.extend(result?);
        }
        self.reference_view(Box::new(target.clone()), selected)
    }
}
