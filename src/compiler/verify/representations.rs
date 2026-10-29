//! Opaque storage representations carry no read permission or ownership.
//! Equality concerns a particular storage revision, including padding bytes.

use super::*;

mod ranges;
#[cfg(test)]
mod tests;

impl Context<'_> {
    fn representation_operand(&mut self, expression: &Expr) -> Result<(Ty, Linear)> {
        let pointer = self.eval(expression, None)?;
        let Symbol::Ref(ty, reference, path) = pointer else {
            return Err("representation observations require a reference to storage".into());
        };
        self.validate_argument(
            &Symbol::Ref(ty.clone(), reference, path.clone()),
            expression.line,
        )?;
        let represented = match *ty {
            Ty::Union(ref members) => {
                let mut live = members.iter().filter(|ty| !matches!(ty, Ty::Shape(_)));
                let ty = live
                    .next()
                    .ok_or("representation observations need a live type")?;
                if live.next().is_some() {
                    return Err("representation observations need an unambiguous live type".into());
                }
                ty.clone()
            }
            Ty::Shape(inner) => *inner,
            ty => ty,
        };
        // Reading a representation does not select or read a live T. Only a
        // known vacant payload can already carry a copied byte identity.
        let copied = match project(self.storage.memory.read(reference)?, &path)? {
            Symbol::Representation { identity, .. } => Some((Formula::True, identity.clone())),
            Symbol::Union {
                members,
                active,
                payloads,
            } => members
                .iter()
                .enumerate()
                .find_map(|(index, member)| {
                    if member != &Ty::Shape(Box::new(represented.clone())) {
                        return None;
                    }
                    let Some(Symbol::Representation { identity, .. }) = &payloads[index] else {
                        return None;
                    };
                    Some(
                        equal(active, &Linear::number(index as i128))
                            .map(|guard| (guard, identity.clone())),
                    )
                })
                .transpose()?,
            _ => None,
        };
        if let Some((guard, identity)) = copied {
            if self.checked_entails(&guard)? {
                return Ok((represented, identity));
            }
        }
        self.charge_value_work(1 + path.len())?;
        let stamp = self
            .proof
            .subjects
            .observe(&self.storage.memory, reference, path)?;
        let identity = if let Some(identity) = self.proof.representations.get(&stamp) {
            identity.clone()
        } else {
            let identity = Linear::variable(&self.fresh_name());
            self.proof.representations.insert(stamp, identity.clone());
            identity
        };
        Ok((represented, identity))
    }

    pub(super) fn representation_call(
        &mut self,
        name: &str,
        args: &[Expr],
        line: usize,
    ) -> Result<Symbol> {
        if args.len() == 3 {
            return self.range_representation_call(name, args, line);
        }
        match (name, args) {
            ("copy_representation", [source]) => {
                if self.execution.phase != Phase::Runtime {
                    return Err("representation copies are runtime operations".into());
                }
                let (ty, identity) = self.representation_operand(source)?;
                Ok(Symbol::Representation {
                    ty: Box::new(ty),
                    identity,
                })
            }
            ("same_representation", [left, right]) => {
                if self.execution.phase == Phase::Runtime {
                    return Err("representation equality is ideal-only".into());
                }
                let (a, left) = self.representation_operand(left)?;
                let (b, right) = self.representation_operand(right)?;
                self.compatible(&a, &b, line)?;
                Ok(Symbol::Bool(equal(&left, &right)?))
            }
            ("transfer_type", [source, target]) => {
                self.transfer_representation_type(source, target, line)
            }
            _ => Err(format!(
                "line {line}: {name} has the wrong number of arguments"
            )),
        }
    }

    fn transfer_representation_type(
        &mut self,
        source: &Expr,
        target: &Expr,
        line: usize,
    ) -> Result<Symbol> {
        if self.execution.phase != Phase::Runtime {
            return Err(
                "type transfers are runtime ownership transitions and cannot be erased".into(),
            );
        }
        if !source.pure_read() || !target.pure_read() {
            return Err("type transfers require pure reference expressions".into());
        }
        let (ty, source_bits) = self.representation_operand(source)?;
        let (target_ty, target_bits) = self.representation_operand(target)?;
        self.compatible(&ty, &target_ty, line)?;
        self.prove(
            &equal(&source_bits, &target_bits)?,
            "identical representations for type transfer",
            line,
        )?;
        let source_place = Expr {
            kind: Kind::Unary("*".into(), Box::new(source.clone())),
            line,
        };
        let target_place = Expr {
            kind: Kind::Unary("*".into(), Box::new(target.clone())),
            line,
        };
        if !self.union_move_place(&source_place, &ty) || !self.union_move_place(&target_place, &ty)
        {
            return Err("type transfer requires T | shape(T) storage at both ends".into());
        }
        let Symbol::Ref(target_union, reference, path) = self.eval(target, None)? else {
            return Err("type transfer needs an unambiguous destination reference".into());
        };
        let stored = project(self.storage.memory.read(reference)?, &path)?.clone();
        self.union_coercion(
            stored,
            Some(&Ty::Shape(Box::new(ty.clone()))),
            line,
            Some(&target_place),
        )?;
        let source_value = match self.eval(source, None)? {
            Symbol::Ref(source_union, source_reference, source_path)
                if source_union == target_union =>
            {
                self.array_element_identity(source_reference, &source_path)?
            }
            _ => None,
        };
        let value = self.move_union_member_into_shape(
            &source_place,
            &ty,
            Symbol::Representation {
                ty: Box::new(ty.clone()),
                identity: source_bits.clone(),
            },
        )?;
        let initialized = self.union_coercion(value, Some(&target_union), line, None)?;
        // The moved value remains owned by this temporary until it is installed.
        let pending = self.fresh_name();
        self.locals
            .values
            .insert(pending.clone(), initialized.clone());
        let stored = self.replace_reference_contents(reference, &path, initialized, line);
        self.locals.values.remove(&pending);
        stored?;
        if let (Some(source), Some((destination, _))) =
            (source_value, self.array_element_identity(reference, &path)?)
        {
            self.arrays.value_transfers.insert(destination, source);
        }
        let stamp = self
            .proof
            .subjects
            .observe(&self.storage.memory, reference, path)?;
        self.proof.representations.insert(stamp, source_bits);
        self.validate_live(line)?;
        Ok(Symbol::Unit)
    }
    fn array_element_identity(
        &mut self,
        reference: Reference,
        path: &[Projection<Linear>],
    ) -> Result<Option<(String, Linear)>> {
        let Some((Projection::Index(index), parent)) = path.split_last() else {
            return Ok(None);
        };
        self.charge_value_work(1 + parent.len() + index.terms.len())?;
        let Symbol::Array { identity, .. } = project(self.storage.memory.read(reference)?, parent)?
        else {
            return Ok(None);
        };
        Ok(Some((identity.clone(), index.clone())))
    }
}
