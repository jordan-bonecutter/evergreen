//! Untagged storage has an ideal active-member selector. A selector proof is
//! required before interpreting payload bytes. It is never emitted as a tag.

use super::*;

#[cfg(test)]
mod tests;

pub(super) fn type_equal(a: &Ty, b: &Ty) -> Result<Formula> {
    Ok(match (a, b) {
        (Ty::Array(a, al), Ty::Array(b, bl)) => type_equal(a, b)?.and(equal(al, bl)?),
        (Ty::Ref(a), Ty::Ref(b)) | (Ty::Plane(a), Ty::Plane(b)) | (Ty::Shape(a), Ty::Shape(b)) => {
            type_equal(a, b)?
        }
        _ => {
            if a == b {
                Formula::True
            } else {
                Formula::False
            }
        }
    })
}

pub(super) fn observations_equal(a: &Symbol, b: &Symbol) -> Result<Formula> {
    let (
        Symbol::Type {
            members: a,
            active: ai,
        },
        Symbol::Type {
            members: b,
            active: bi,
        },
    ) = (a, b)
    else {
        return Err("type equality requires two ideal type observations".into());
    };
    let mut result = Formula::False;
    for (i, a) in a.iter().enumerate() {
        for (j, b) in b.iter().enumerate() {
            result = result.or(type_equal(a, b)?
                .and(equal(ai, &Linear::number(i as i128))?)
                .and(equal(bi, &Linear::number(j as i128))?));
        }
    }
    Ok(result)
}

impl Context<'_> {
    pub(super) fn type_literal(&self, expression: &Expr) -> Option<Ty> {
        match &expression.kind {
            Kind::Unary(op, inner) if op == "&" => {
                self.type_literal(inner).map(|ty| Ty::Ref(Box::new(ty)))
            }
            Kind::Unit => Some(Ty::Unit),
            Kind::Call(name, args) if name == "plane" && args.len() == 1 => self
                .type_literal(&args[0])
                .map(|ty| Ty::Plane(Box::new(ty))),
            Kind::Name(name) => {
                MachineInt::parse(name)
                    .map(Ty::Machine)
                    .or_else(|| match name.as_str() {
                        "bool" => Some(Ty::Bool),
                        "unit" => Some(Ty::Unit),
                        "integer" => Some(Ty::Int),
                        "nat" => Some(Ty::Nat),
                        _ if self.declarations.structs.contains_key(name) => {
                            Some(Ty::Record(name.clone()))
                        }
                        _ if self.locals.module.as_ref().is_some_and(|module| {
                            self.declarations
                                .structs
                                .contains_key(&format!("{module}::{name}"))
                        }) =>
                        {
                            Some(Ty::Record(format!(
                                "{}::{name}",
                                self.locals.module.as_ref().unwrap()
                            )))
                        }
                        _ => None,
                    })
            }
            Kind::Call(name, args) if name == "shape" && args.len() == 1 => self
                .type_literal(&args[0])
                .filter(|ty| !matches!(ty, Ty::Shape(_)))
                .map(|ty| Ty::Shape(Box::new(ty))),
            _ => None,
        }
    }

    pub(super) fn resolve_union(&mut self, source: &[Type]) -> Result<Ty> {
        if !(2..=16).contains(&source.len()) {
            return Err("raw unions require between 2 and 16 distinct members".into());
        }
        let mut members = source
            .iter()
            .map(|ty| self.resolve(ty))
            .collect::<Result<Vec<_>>>()?;
        members.sort();
        if members.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err("duplicate raw union member".into());
        }
        for member in source {
            // Pointer alternatives need guarded ownership/borrow footprints.
            // Never instantiate inactive pointer members as extra authorities.
            if type_has_reference(member, self.declarations.structs) {
                return Err("raw union pointer members need conditional ownership and borrow footprints; not implemented yet".into());
            }
        }
        Ok(Ty::Union(members))
    }

    pub(super) fn fresh_union_tag(&mut self, members: usize) -> Result<Linear> {
        let active = Linear::variable(self.fresh_name());
        self.assume_from(&Formula::Ge(active.clone()), paths::Origin::Unresolved)?;
        self.assume_from(
            &Formula::Ge(Linear::number(members as i128 - 1).sub(&active)?),
            paths::Origin::Unresolved,
        )?;
        Ok(active)
    }

    pub(super) fn arbitrary_union(&mut self, members: &[Ty]) -> Result<Symbol> {
        let active = self.fresh_union_tag(members.len())?;
        let base = self.proof.paths.clone();
        let mut alternatives = paths::Paths::default();
        let mut payloads = Vec::with_capacity(members.len());
        for (index, ty) in members.iter().enumerate() {
            self.proof.paths = extend(
                &base,
                &equal(&active, &Linear::number(index as i128))?,
                false,
                self.session,
                &mut self.work.value_work,
            )?;
            // A member's refinement holds only while that member is active.
            // An uninhabited alternative cannot make another one impossible.
            payloads.push(Some(self.arbitrary(ty)?));
            alternatives.extend(self.proof.paths.clone());
        }
        self.proof.paths = paths::bounded(alternatives, self.session, &mut self.work.value_work)?;
        Ok(Symbol::Union {
            members: members.to_vec(),
            active,
            payloads,
        })
    }

    pub(super) fn union_coercion(
        &mut self,
        value: Symbol,
        expected: Option<&Ty>,
        line: usize,
        source: Option<&Expr>,
    ) -> Result<Symbol> {
        let Some(expected) = expected else {
            return Ok(value);
        };
        if &value.ty() == expected {
            return Ok(value);
        }
        if let Ty::Union(members) = expected {
            if let Some(index) = members.iter().position(|ty| ty == &value.ty()) {
                let mut payloads = vec![None; members.len()];
                payloads[index] = Some(value);
                return Ok(Symbol::Union {
                    members: members.clone(),
                    active: Linear::number(index as i128),
                    payloads,
                });
            }
        }
        if let Symbol::Union {
            members,
            active,
            mut payloads,
        } = value
        {
            if let Some(index) = members.iter().position(|ty| ty == expected) {
                let subjects = source
                    .map(|source| self.claim_subjects(source))
                    .transpose()?
                    .and_then(|snapshot| {
                        snapshot.key.map(|key| {
                            subjects::Snapshot::from_key(subjects::ClaimKey::Binary(
                                "==".into(),
                                Box::new(subjects::ClaimKey::Unary("typeof".into(), Box::new(key))),
                                Box::new(subjects::ClaimKey::Type(expected.clone())),
                            ))
                        })
                    });
                let proof = self.prove_subjects(
                    &equal(&active, &Linear::number(index as i128))?,
                    subjects.as_ref(),
                    "active raw union member",
                    line,
                )?;
                return match payloads[index].take() {
                    Some(value) => Ok(value),
                    None => {
                        let parents = self.proof.contract_parents.clone();
                        self.proof.contract_parents.push(proof);
                        let value = self.arbitrary(expected);
                        self.proof.contract_parents = parents;
                        value
                    }
                };
            }
            return Err(format!(
                "line {line}: {expected:?} is not a raw union member"
            ));
        }
        Ok(value)
    }

    pub(super) fn eval_type_operation(
        &mut self,
        name: &str,
        args: &[Expr],
        expected: Option<&Ty>,
        line: usize,
    ) -> Result<Symbol> {
        if args.len() != 1 {
            return Err(format!("line {line}: {name} expects one argument"));
        }
        if name == "shape" {
            let inner = self
                .type_literal(&args[0])
                .ok_or("shape requires a type, not a value")?;
            if matches!(inner, Ty::Shape(_)) {
                return Err("shape(shape(T)) is not a distinct storage state".into());
            }
            if self.execution.phase == Phase::Runtime
                && !runtime_type(&heap::syntax_type(&inner, line)?, self.declarations.structs)
            {
                return Err("ideal types have no runtime shape storage".into());
            }
            return Ok(if expected == Some(&Ty::Type) {
                Symbol::Type {
                    members: vec![Ty::Shape(Box::new(inner))],
                    active: Linear::number(0),
                }
            } else {
                Symbol::Shape(Box::new(inner))
            });
        }
        if self.execution.phase == Phase::Runtime {
            return Err("typeof is ideal; no runtime tag exists for a raw union".into());
        }
        if let Kind::Name(name) = &args[0].kind {
            if self
                .locals
                .places
                .get(name)
                .is_some_and(|plane| self.storage.memory.get(*plane).is_err())
            {
                let ty = self
                    .locals
                    .values
                    .get(name)
                    .ok_or("unknown moved storage")?
                    .ty();
                let ty = if matches!(ty, Ty::Shape(_)) {
                    ty
                } else {
                    Ty::Shape(Box::new(ty))
                };
                return Ok(Symbol::Type {
                    members: vec![ty],
                    active: Linear::number(0),
                });
            }
        }
        let value = self.eval(&args[0], None)?;
        Ok(match value {
            Symbol::Union {
                members, active, ..
            } => Symbol::Type { members, active },
            value => Symbol::Type {
                members: vec![value.ty()],
                active: Linear::number(0),
            },
        })
    }

    pub(super) fn union_literal_hint(expected: Option<&Ty>) -> Option<Ty> {
        let Some(Ty::Union(members)) = expected else {
            return expected.cloned();
        };
        let mut numeric = members
            .iter()
            .filter(|ty| matches!(ty, Ty::Machine(_) | Ty::Int | Ty::Nat));
        let first = numeric.next()?.clone();
        numeric.next().is_none().then_some(first)
    }
}
