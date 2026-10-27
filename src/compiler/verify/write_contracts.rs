//! Write authority and guarded input footprints, independent of runtime stores.

use super::*;

impl Context<'_> {
    pub(super) fn write_permitted(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
        owned: bool,
    ) -> Result<bool> {
        let grants = std::mem::take(&mut self.storage.writable);
        let result = self.write_permitted_by(&grants, reference, path, owned);
        self.storage.writable = grants;
        result
    }

    pub(super) fn write_permitted_by(
        &mut self,
        grants: &[WritePlace],
        reference: Reference,
        path: &[Projection<Linear>],
        owned: bool,
    ) -> Result<bool> {
        let condition = self.write_permission_condition(grants, reference, path, owned)?;
        self.checked_entails(&condition)
    }

    fn write_permission_condition(
        &mut self,
        grants: &[WritePlace],
        reference: Reference,
        path: &[Projection<Linear>],
        owned: bool,
    ) -> Result<Formula> {
        if owned {
            return Ok(Formula::True);
        }
        let plane = self.storage.memory.plane(reference)?;
        let mut condition = Formula::False;
        for grant in grants {
            self.charge_value_work(1 + grant.path.len() + grant.guard.storage_weight()?)?;
            if self.storage.memory.plane(grant.reference).ok() == Some(plane)
                && grant.path.len() <= path.len()
            {
                let aliases =
                    guarded_references::paths_equal(&grant.path, &path[..grant.path.len()])?;
                condition = condition.or(grant.guard.clone().and(aliases));
            }
        }
        Ok(condition)
    }

    pub(super) fn write_contract_permitted(
        &mut self,
        write: &WritePlace,
        owned: bool,
    ) -> Result<bool> {
        let grants = std::mem::take(&mut self.storage.writable);
        let result = self.write_contract_permitted_by(&grants, write, owned);
        self.storage.writable = grants;
        result
    }

    pub(super) fn write_contract_permitted_by(
        &mut self,
        grants: &[WritePlace],
        write: &WritePlace,
        owned: bool,
    ) -> Result<bool> {
        let available =
            self.write_permission_condition(grants, write.reference, &write.path, owned)?;
        self.checked_entails(&write.guard.clone().not().or(available))
    }

    pub(super) fn write_places(
        &mut self,
        function: &Function,
        inputs: &[InputReference],
    ) -> Result<Vec<WritePlace>> {
        let phase = std::mem::replace(&mut self.execution.phase, Phase::Specification);
        let result = self.collect_write_places(function, inputs);
        self.execution.phase = phase;
        result
    }

    fn collect_write_places(
        &mut self,
        function: &Function,
        inputs: &[InputReference],
    ) -> Result<Vec<WritePlace>> {
        let mut places: Vec<WritePlace> = Vec::new();
        for expression in &function.modifies {
            let origin = input_reference_origin(expression)
                .ok_or("effect must project an incoming reference")?;
            let value = self.incoming_borrow(expression, inputs)?;
            let Ty::Ref(ty) = value.ty() else {
                return Err("effect entries must denote references".into());
            };
            for case in guarded_references::cases(&value)? {
                self.charge_value_work(
                    inputs.len() + places.len() + case.path.len() + case.guard.storage_weight()?,
                )?;
                if self.checked_entails(&case.guard.clone().not())? {
                    continue;
                }
                let place = WritePlace {
                    origin: origin.clone(),
                    guard: case.guard,
                    reference: case.reference,
                    path: case.path,
                    ty: ty.clone(),
                };
                let base = self.proof.paths.clone();
                self.proof.paths = extend(
                    &base,
                    &place.guard,
                    false,
                    self.session,
                    &mut self.work.value_work,
                )?;
                let checked = self.check_write_region(function, inputs, &place);
                self.proof.paths = base;
                checked?;
                if let Some(previous) = places.iter_mut().find(|previous| {
                    previous.origin == place.origin
                        && previous.reference == place.reference
                        && previous.path == place.path
                        && previous.ty == place.ty
                }) {
                    previous.guard = previous.guard.clone().or(place.guard);
                } else {
                    places.push(place);
                }
            }
        }
        Ok(places)
    }

    fn check_write_region(
        &mut self,
        function: &Function,
        inputs: &[InputReference],
        place: &WritePlace,
    ) -> Result<()> {
        // Erasure belongs to the projected storage slot, not to a pointer
        // carried in ideal data. Origin coverage was checked above.
        let mut erased = None;
        for input in inputs.iter().filter(|input| {
            input.origin == place.origin
                && input.reference == place.reference
                && input.path.len() <= place.path.len()
        }) {
            if !self.paths_equal(&input.path, &place.path[..input.path.len()])? {
                continue;
            }
            let mut proof_slot = self.proof_storage(&input.pointee);
            let mut target = project(self.storage.memory.read(input.reference)?, &input.path)?;
            for step in &place.path[input.path.len()..] {
                if let (Symbol::Record(name, _), Projection::Field(field)) = (target, step) {
                    proof_slot |= self.declarations.structs[name].ideal_fields.contains(field);
                }
                target = project(target, std::slice::from_ref(step))?;
            }
            erased = Some(proof_slot);
            break;
        }
        let erased = erased.ok_or("missing incoming reference for write footprint")?;
        if function.ideal && !erased {
            return Err("ideal modifies must target proof storage; erased references do not grant writes to runtime pointees".into());
        }
        let supported_region = match &*place.ty {
            Ty::Machine(_) | Ty::Bool => true,
            Ty::Nat | Ty::Int => erased,
            Ty::Record(_) => {
                self.history_element(&place.ty)
                    || erased && self.erased_ty(&place.ty) && self.scalar_field_value(&place.ty)
            }
            Ty::Array(element, _) => {
                matches!(**element, Ty::Machine(_) | Ty::Bool)
                    || matches!(**element, Ty::Record(_)) && self.history_element(element)
            }
            _ => false,
        };
        if !supported_region {
            return Err("modifies targets require machine scalars, Booleans, proof-only integer/nat slots, copyable scalar-field records, or supported arrays".into());
        }
        Ok(())
    }
}
