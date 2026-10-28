//! Direct binding and record-field replacement. Evaluate the RHS once, then
//! clean up the current destination while the replacement still owns its data.

use super::*;

impl Context<'_> {
    pub(super) fn assign_starting_owners(
        &mut self,
        place: &Expr,
        value: &Expr,
        starts: &[Expr],
    ) -> Result<()> {
        let owners = self.owner_start_sources(starts)?;
        if place.indirect_place() {
            return self.assign_indirect(place, value, &owners);
        }

        fn path(e: &Expr, fields: &mut Vec<String>) -> Result<String> {
            match &e.kind {
                Kind::Name(n) => Ok(n.clone()),
                Kind::Field(base, n) => {
                    let root = path(base, fields)?;
                    fields.push(n.clone());
                    Ok(root)
                }
                _ => Err(format!(
                    "line {}: assignment requires a variable or struct field",
                    e.line
                )),
            }
        }

        fn replace(root: &mut Symbol, fields: &[String], value: Symbol) -> Result<()> {
            if fields.is_empty() {
                *root = value;
                return Ok(());
            }
            let Symbol::Record(_, members) = root else {
                return Err("field assignment requires a struct".into());
            };
            let member = members.get_mut(&fields[0]).ok_or("unknown field")?;
            replace(member, &fields[1..], value)
        }
        let mut fields = Vec::new();
        let name = path(place, &mut fields)?;
        self.runtime_name(&name)?;
        let old = if let Kind::Name(n) = &place.kind {
            if let Some(value) = self
                .locals
                .places
                .get(n)
                .and_then(|id| self.storage.memory.get(*id).ok())
            {
                value.clone()
            } else {
                self.locals
                    .values
                    .get(n)
                    .cloned()
                    .ok_or("unknown assignment target")?
            }
        } else {
            self.storage(place)?
        };
        let mut new = self.eval(value, Some(&old.ty()))?;
        let old_live = self
            .locals
            .places
            .get(&name)
            .is_none_or(|id| self.storage.memory.get(*id).is_ok());
        // The right-hand side can replace this slot itself. Its former value
        // may already have been consumed; cleanup belongs to what is there now.
        let old = if old_live { self.storage(place)? } else { old };
        self.compatible(&new.ty(), &old.ty(), place.line)?;
        if self.execution.dropping && self.symbol_is_move_only(&old) {
            return Err(
                "destructors cannot replace owning fields without cleanup/effect proofs".into(),
            );
        }
        let replace_plane = !self.same_layout(&old, &new)?;
        if !replace_plane {
            self.preserve_views(&old, &mut new)?;
        }
        if !fields.is_empty() && !old_live {
            return Err(format!("line {}: field assignment cannot restore shape(T); replace consumed owner {name} as a whole", place.line));
        }
        let cleaned_old = old_live
            && self.has_runtime_cleanup(&old.ty())
            && !self.uninitialized_union(&old, place.line)?;
        if cleaned_old {
            self.validate_argument(&old, place.line)?;
            // The computed replacement remains an owner during old cleanup.
            // Destructors may hold permitted borrows into its allocations.
            let pending = self.fresh_name();
            self.charge_value_work(symbol_weight(&new)?)?;
            self.locals.values.insert(pending.clone(), new.clone());
            // The old slot remains observable during its destructor. Validate
            // retained caller views after installing the replacement, when the
            // destroyed old payload no longer inhabits that slot.
            self.execution.replacing_cleanup += 1;
            let cleanup = self.cleanup_value(old, place.line);
            self.execution.replacing_cleanup -= 1;
            self.locals.values.remove(&pending);
            cleanup?;
        }
        let mut root = if let Some(value) = self
            .locals
            .places
            .get(&name)
            .and_then(|id| self.storage.memory.get(*id).ok())
        {
            value.clone()
        } else {
            self.locals
                .values
                .get(&name)
                .cloned()
                .ok_or("unknown assignment target")?
        };
        replace(&mut root, &fields, new)?;
        let lifted = self
            .locals
            .places
            .get(&name)
            .and_then(|plane| self.storage.opened_planes.get(plane))
            .cloned()
            .unwrap_or_default();
        if let Some(id) = self.locals.places.get(&name).copied() {
            let projections = fields
                .iter()
                .cloned()
                .map(Projection::Field)
                .collect::<Vec<_>>();
            self.note_state_write(id, &projections)?;
            self.storage.memory.write(id, root.clone(), replace_plane)?;
        }
        self.start_owners(&owners)?;
        self.retained_valid_with(&root, place.line, &lifted)?;
        self.locals.values.insert(name, root);
        self.validate_opened_planes(place.line)?;
        if cleaned_old {
            self.finish_replacement_cleanup(place.line)?;
        }
        Ok(())
    }
}
