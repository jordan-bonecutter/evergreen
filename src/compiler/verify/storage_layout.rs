//! Storage compatibility while replacing values. Pointee extents do not alter
//! pointer representation; value compatibility is checked separately.

use super::*;

impl Context<'_> {
    pub(super) fn same_layout(&mut self, a: &Symbol, b: &Symbol) -> Result<bool> {
        match (a, b) {
            (Symbol::Union { members: a, .. }, Symbol::Union { members: b, .. }) => {
                Ok(same_union_storage(a, b))
            }
            (Symbol::Shape(a), Symbol::Shape(b)) => Ok(a == b),
            (Symbol::Record(an, a), Symbol::Record(bn, b)) => {
                if an != bn || a.len() != b.len() {
                    return Ok(false);
                }
                for (name, value) in a {
                    let Some(other) = b.get(name) else {
                        return Ok(false);
                    };
                    if !self.same_layout(value, other)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (
                Symbol::Array {
                    len: a,
                    items: av,
                    element,
                    identity: ai,
                    ..
                },
                Symbol::Array {
                    len: b,
                    items: bv,
                    identity: bi,
                    ..
                },
            ) => {
                self.work.obligations += 1;
                for path in extend(
                    &self.proof.paths,
                    &equal(a, b)?,
                    true,
                    self.session,
                    &mut self.work.value_work,
                )?
                .iter()
                {
                    if !self.session.probe(path)? {
                        return Ok(false);
                    }
                }
                match (av, bv) {
                    (Some(a), Some(b)) => {
                        if a.len() != b.len() {
                            return Ok(false);
                        }
                        for (a, b) in a.iter().zip(b) {
                            if !self.same_layout(a, b)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(ai == bi
                        || self.history_element(element)
                        || matches!(
                            **element,
                            Ty::Int | Ty::Nat | Ty::Machine(_) | Ty::Bool | Ty::Ref(_) | Ty::Unit
                        )),
                }
            }
            (Symbol::Number(_, _), Symbol::Number(_, _))
            | (Symbol::Bool(_), Symbol::Bool(_))
            | (Symbol::Ref(..), Symbol::Ref(..))
            | (Symbol::Plane(..), Symbol::Plane(..))
            | (Symbol::Owner(..), Symbol::Owner(..))
            | (Symbol::Unit, Symbol::Unit) => Ok(true),
            (a, b) if matches!(a.ty(), Ty::Ref(_)) && matches!(b.ty(), Ty::Ref(_)) => Ok(true),
            _ => Ok(false),
        }
    }
}

// Pointer bounds are proof data, not bytes in the pointer header. Inline array
// bounds still affect storage and must agree before retaining slot references.
fn same_union_storage(a: &[Ty], b: &[Ty]) -> bool {
    a.len() == b.len()
        && a.iter().all(|a| b.iter().any(|b| same_type_storage(a, b)))
        && b.iter().all(|b| a.iter().any(|a| same_type_storage(a, b)))
}

fn same_type_storage(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Plane(_), Ty::Plane(_)) | (Ty::Owner(_), Ty::Owner(_)) | (Ty::Ref(_), Ty::Ref(_)) => {
            true
        }
        (Ty::Shape(a), Ty::Shape(b)) => same_type_storage(a, b),
        (Ty::Array(a, n), Ty::Array(b, m)) => n == m && same_type_storage(a, b),
        (Ty::Union(a), Ty::Union(b)) => same_union_storage(a, b),
        _ => a == b,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn union_storage_checks_both_member_sets_and_keeps_inline_extents() {
        let byte = Ty::Machine(MachineInt::parse("u8").unwrap());
        let array = |n| Ty::Array(Box::new(byte.clone()), Linear::number(n));
        let pointer = |n| Ty::Plane(Box::new(array(n)));
        let zero = Ty::Record("Zero".into());
        assert!(same_union_storage(
            &[zero.clone(), pointer(2)],
            &[zero.clone(), pointer(4)]
        ));
        assert!(!same_union_storage(
            &[pointer(2), pointer(4)],
            &[pointer(8), Ty::Record("Large".into())]
        ));
        assert!(!same_union_storage(
            &[zero.clone(), array(2)],
            &[zero, array(4)]
        ));
    }
}
