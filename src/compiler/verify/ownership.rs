//! Generic lifetime claims. The total census includes opaque caller owners;
//! source Rc counters and library protocols are not recognized here.

use super::*;

#[cfg(test)]
mod tests;

pub(super) fn census_path() -> Vec<Projection<Linear>> {
    vec![Projection::Owners]
}

impl Context<'_> {
    pub(super) fn contains_shared(&self, value: &Symbol) -> bool {
        match value {
            Symbol::Shared(..) => true,
            Symbol::Record(_, fields) => fields.values().any(|value| self.contains_shared(value)),
            Symbol::Array { element, .. } => self.type_contains_shared(element),
            Symbol::Union { payloads, .. } => payloads
                .iter()
                .flatten()
                .any(|value| self.contains_shared(value)),
            _ => false,
        }
    }

    fn type_contains_shared(&self, ty: &Ty) -> bool {
        match ty {
            Ty::Shared(_) => true,
            Ty::Record(name) => self.declarations.structs.get(name).is_some_and(|record| {
                record
                    .runtime_fields()
                    .any(|(_, ty)| self.syntax_contains_shared(ty))
            }),
            Ty::Array(element, _) => self.type_contains_shared(element),
            Ty::Union(members) => members.iter().any(|ty| self.type_contains_shared(ty)),
            _ => false,
        }
    }

    fn syntax_contains_shared(&self, ty: &Type) -> bool {
        match ty {
            Type::Shared(_) => true,
            Type::Named(name) => self.declarations.structs.get(name).is_some_and(|record| {
                record
                    .runtime_fields()
                    .any(|(_, ty)| self.syntax_contains_shared(ty))
            }),
            Type::Array(element, _) => self.syntax_contains_shared(element),
            Type::Union(members) => members.iter().any(|ty| self.syntax_contains_shared(ty)),
            _ => false,
        }
    }

    pub(super) fn owner_start_sources(
        &mut self,
        sources: &[Expr],
    ) -> Result<Vec<crate::shared::planes::OwnedReference>> {
        if sources.is_empty() {
            return Ok(Vec::new());
        }
        if self.execution.phase != Phase::Runtime || !self.storage.opened_planes.is_empty() {
            return Err("starts_owner requires a runtime store with closed invariants".into());
        }
        sources
            .iter()
            .map(|source| {
                if !source.pure_read() || !source.stored_place() {
                    return Err(format!(
                        "line {}: starts_owner requires a pure stored shared-pointer place",
                        source.line
                    ));
                }
                let Symbol::Shared(_, owner) = self.storage(source)? else {
                    return Err(format!(
                        "line {}: starts_owner requires a live shared pointer",
                        source.line
                    ));
                };
                self.storage.memory.borrow_owned(owner)?;
                Ok(owner)
            })
            .collect()
    }

    pub(super) fn start_owners(
        &mut self,
        owners: &[crate::shared::planes::OwnedReference],
    ) -> Result<()> {
        for &owner in owners {
            let reference = self.storage.memory.borrow_owned(owner)?;
            let count = self.census_value(reference)?.add(&Linear::number(1))?;
            self.note_census_write(reference)?;
            self.storage.memory.begin_owner(owner)?;
            self.censuses.insert(reference, count);
        }
        Ok(())
    }

    pub(super) fn copy_pointer_read(&mut self, value: Symbol, line: usize) -> Result<Symbol> {
        if self.execution.phase == Phase::Specification
            || self.symbol_is_move_only(&value)
            || !self.contains_shared(&value)
        {
            return Ok(value);
        }
        if self.execution.phase != Phase::Runtime || !self.storage.opened_planes.is_empty() {
            return Err(
                "shared pointer copies require runtime execution with closed invariants".into(),
            );
        }
        let copied = self.copy_shared_fields(value)?;
        self.validate_live(line)?;
        self.validate_argument(&copied, line)?;
        Ok(copied)
    }

    fn copy_shared_fields(&mut self, value: Symbol) -> Result<Symbol> {
        self.charge_value_work(1)?;
        Ok(match value {
            Symbol::Shared(ty, owner) => {
                let reference = self.storage.memory.borrow_owned(owner)?;
                let count = self.census_value(reference)?;
                if self.storage.memory.has_early_owner(owner)? {
                    if !self.storage.loops.is_empty() {
                        return Err(
                            "materializing early owners in loops requires a resource frame".into(),
                        );
                    }
                } else {
                    self.note_census_write(reference)?;
                }
                let copied = self.storage.memory.copy_owner(owner)?;
                let count = if copied.started_lifetime() {
                    count.add(&Linear::number(1))?
                } else {
                    count
                };
                self.censuses.insert(reference, count);
                Symbol::Shared(ty, copied.owner())
            }
            Symbol::Record(name, fields) => Symbol::Record(
                name,
                fields
                    .into_iter()
                    .map(|(name, value)| Ok((name, self.copy_shared_fields(value)?)))
                    .collect::<Result<_>>()?,
            ),
            Symbol::Array {
                element,
                len,
                items,
                cells,
                identity,
            } if self.type_contains_shared(&element) => {
                let items = if let Some(items) = items {
                    items
                } else {
                    let length = constant_index(&len)
                        .ok_or("copying shared-pointer arrays needs a fixed extent")?;
                    self.charge_value_work(length)?;
                    (0..length)
                        .map(|index| {
                            self.read_array(
                                &element,
                                &identity,
                                &Linear::number(index as i128),
                                None,
                                &cells,
                            )
                        })
                        .collect::<Result<Vec<_>>>()?
                };
                let items = items
                    .into_iter()
                    .map(|value| self.copy_shared_fields(value))
                    .collect::<Result<Vec<_>>>()?;
                Symbol::Array {
                    element,
                    len,
                    items: Some(items),
                    cells: BTreeMap::new(),
                    identity: self.fresh_name(),
                }
            }
            other => other,
        })
    }

    pub(super) fn coerce_pointer(
        &mut self,
        value: Symbol,
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        if let (Ty::Ref(source), Some(Ty::Ref(target))) = (value.ty(), expected) {
            if matches!(source.as_ref(), Ty::Union(members) if members.contains(target)) {
                return self.borrow_union_member(value, target, line);
            }
        }
        match (value, expected) {
            (Symbol::Unique(source, reference), Some(Ty::Unique(target)))
                if Self::empty_array_target(&source, target) =>
            {
                self.narrow_empty_array(&source, reference, target, line)
            }
            (Symbol::Unique(ty, reference), Some(Ty::Shared(target))) => {
                if self.execution.phase != Phase::Runtime || !self.storage.opened_planes.is_empty()
                {
                    return Err("pointer authority changes require runtime execution with closed invariants".into());
                }
                self.compatible(&ty, target, line)?;
                let plane = self.storage.memory.plane(reference)?;
                self.note_census_write(reference)?;
                let owner = self.storage.memory.share_owner(plane)?;
                self.censuses.insert(reference, Linear::number(1));
                Ok(Symbol::Shared(ty, owner))
            }
            (Symbol::Shared(ty, owner), Some(Ty::Unique(target))) => {
                if self.execution.phase != Phase::Runtime || !self.storage.opened_planes.is_empty()
                {
                    return Err("pointer authority changes require runtime execution with closed invariants".into());
                }
                self.compatible(&ty, target, line)?;
                self.recover_owning_reference(ty, owner, line)
            }
            (value, _) => Ok(value),
        }
    }

    pub(super) fn leak_shared(
        &mut self,
        owner: crate::shared::planes::OwnedReference,
        line: usize,
    ) -> Result<()> {
        let reference = self.storage.memory.borrow_owned(owner)?;
        let count = self.census_value(reference)?.sub(&Linear::number(1))?;
        self.note_census_write(reference)?;
        self.storage.memory.release_owner(owner)?;
        self.censuses.insert(reference, count);
        if self.execution.replacing_cleanup != 0 {
            return Ok(());
        }
        self.validate_live(line)
    }

    pub(super) fn leak_value(&mut self, value: Symbol, line: usize) -> Result<()> {
        self.charge_value_work(1)?;
        match value {
            Symbol::Shared(_, owner) => self.leak_shared(owner, line),
            Symbol::Unique(_, reference) => {
                let plane = self.storage.memory.plane(reference)?;
                self.note_census_write(reference)?;
                let owner = self.storage.memory.share_owner(plane)?;
                self.storage.memory.release_owner(owner)?;
                self.censuses.insert(reference, Linear::number(0));
                self.validate_live(line)
            }
            Symbol::Record(_, fields) => {
                for value in fields.into_values() {
                    self.leak_value(value, line)?;
                }
                Ok(())
            }
            Symbol::Array {
                items: Some(items), ..
            } => {
                for value in items {
                    self.leak_value(value, line)?;
                }
                Ok(())
            }
            Symbol::Array { element, len, .. }
                if len != Linear::number(0)
                    && heap::owns_planes_type(
                        &heap::syntax_type(&element, line)?,
                        self.declarations.structs,
                    ) =>
            {
                Err("leaking opaque owning-pointer arrays needs exact claim storage".into())
            }
            Symbol::Union { .. } => {
                Err("leaking raw union storage requires proving its active member".into())
            }
            _ => Ok(()),
        }
    }

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
        let Symbol::Unique(_, reference) = self.arbitrary(&Ty::Unique(Box::new(ty.clone())))?
        else {
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
        Ok(Symbol::Shared(Box::new(ty.clone()), owner))
    }

    pub(super) fn owning_reference(&self, value: &Symbol) -> Result<Reference> {
        match value {
            Symbol::Shared(_, owner) => {
                self.storage.memory.read(owner.reference())?;
                Ok(owner.reference())
            }
            Symbol::Unique(_, reference) => {
                self.storage.memory.read(*reference)?;
                Ok(*reference)
            }
            Symbol::Ref(_, reference, path) => {
                let target = project(self.storage.memory.read(*reference)?, path)?;
                if matches!(target, Symbol::Shared(..) | Symbol::Unique(..)) {
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
        // A unique plane is the only concrete default. Incoming shared(T)
        // values always carry their abstract total above.
        if self.storage.memory.owner_count(reference)? == 1 {
            Ok(Linear::number(1))
        } else {
            Err("missing symbolic owner census".into())
        }
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
        Ok(Symbol::Unique(ty, reference))
    }

    pub(super) fn observe_owner_count(&mut self, args: &[Expr]) -> Result<Symbol> {
        if args.len() != 1 {
            return Err("owner_count expects one argument".into());
        }
        if self.execution.phase == Phase::Runtime {
            return Err("owner_count is an ideal census observation".into());
        }
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let value = self.eval(&args[0], None);
        self.execution.phase = phase;
        let value = value?;
        if matches!(value, Symbol::Ref(..) | Symbol::RefCases(..)) {
            self.validate_reference_addresses(&value)?;
        }
        let reference = self.owning_reference(&value)?;
        Ok(Symbol::Number(Ty::Nat, self.census_value(reference)?))
    }
}
