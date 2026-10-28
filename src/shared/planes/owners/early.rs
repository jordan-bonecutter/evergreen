//! Early owners are counted lifetime obligations without pointer authority.
//! They are host metadata, never a source Credit type or runtime object.

use super::*;
use std::collections::BTreeSet;

/// An already counted owner whose pointer value has not been materialized.
/// Copying this host handle denotes the same obligation, not another owner.
/// Only materialization can turn it into a usable owning reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EarlyOwner {
    reference: Reference,
    token: u64,
}

/// Outstanding obligations inherited by a nested body. A marker grants no
/// pointer authority; a body must fulfill every additional owner it starts.
pub struct OwnerScope {
    arena: u64,
    inherited: BTreeSet<u64>,
}

/// Whether a pointer copy starts a lifetime or fulfills an existing early one.
pub struct OwnerCopy {
    owner: OwnedReference,
    started: bool,
}
impl OwnerCopy {
    pub fn owner(&self) -> OwnedReference {
        self.owner
    }
    pub fn started_lifetime(&self) -> bool {
        self.started
    }
}

impl<T> Memory<T> {
    /// Start one additional owner's lifetime using an existing live owner.
    /// The new claim immediately blocks sole-owner recovery and deallocation.
    pub fn begin_owner(&mut self, owner: OwnedReference) -> Result<EarlyOwner, String> {
        let id = self.owner_plane(owner)?;
        let Ownership::Shared(tokens) = &self.planes[id.slot].ownership else {
            unreachable!()
        };
        tokens
            .len()
            .checked_add(1)
            .ok_or("shared owner count exhausted")?;
        let outstanding = self
            .early_owners
            .checked_add(1)
            .ok_or("early owner count exhausted")?;
        let token = fresh_token()?;
        let revision = fresh_revision()?;
        let Ownership::Shared(tokens) = &mut self.planes[id.slot].ownership else {
            unreachable!()
        };
        tokens.insert(token, OwnerState::Early);
        self.early_owners = outstanding;
        self.planes[id.slot].census_revision = revision;
        Ok(EarlyOwner {
            reference: owner.reference,
            token,
        })
    }

    /// Fulfill precisely this obligation. Its lifetime and census token already
    /// exist, so materialization neither adds an owner nor changes the census.
    /// The originating owner need no longer exist: the early claim kept the
    /// allocation alive. A second materialization fails before changing state.
    pub fn materialize_owner(&mut self, early: EarlyOwner) -> Result<OwnedReference, String> {
        let id = self.plane(early.reference)?;
        let Ownership::Shared(tokens) = &mut self.planes[id.slot].ownership else {
            return Err("early owner does not belong to shared storage".into());
        };
        let state = tokens
            .get_mut(&early.token)
            .filter(|state| **state == OwnerState::Early)
            .ok_or("early owner was already materialized or belongs to another plane")?;
        let outstanding = self
            .early_owners
            .checked_sub(1)
            .ok_or("early owner bookkeeping is inconsistent")?;
        *state = OwnerState::Materialized;
        self.early_owners = outstanding;
        Ok(OwnedReference {
            reference: early.reference,
            token: early.token,
        })
    }

    pub fn has_early_owner(&self, owner: OwnedReference) -> Result<bool, String> {
        let id = self.owner_plane(owner)?;
        if self.early_owners == 0 {
            return Ok(false);
        }
        let Ownership::Shared(tokens) = &self.planes[id.slot].ownership else {
            unreachable!()
        };
        Ok(tokens.values().any(|state| *state == OwnerState::Early))
    }

    /// A normal source-level copy fulfills the most recent pending owner of this
    /// allocation, or starts a new lifetime when no promise is pending.
    pub fn copy_owner(&mut self, owner: OwnedReference) -> Result<OwnerCopy, String> {
        let id = self.owner_plane(owner)?;
        if self.early_owners == 0 {
            return Ok(OwnerCopy {
                owner: self.duplicate_owner(owner)?,
                started: true,
            });
        }
        let Ownership::Shared(tokens) = &self.planes[id.slot].ownership else {
            unreachable!()
        };
        let early = tokens.iter().rev().find_map(|(&token, &state)| {
            (state == OwnerState::Early).then_some(EarlyOwner {
                reference: owner.reference,
                token,
            })
        });
        match early {
            Some(early) => Ok(OwnerCopy {
                owner: self.materialize_owner(early)?,
                started: false,
            }),
            None => Ok(OwnerCopy {
                owner: self.duplicate_owner(owner)?,
                started: true,
            }),
        }
    }

    /// Record inherited promises without copying allocation payloads or owners.
    pub fn owner_scope(&self) -> OwnerScope {
        OwnerScope {
            arena: self.owner,
            inherited: if self.early_owners == 0 {
                BTreeSet::new()
            } else {
                self.early_owner_tokens().collect()
            },
        }
    }

    /// A returning body must fulfill every owner it started. Promises belonging
    /// to its caller may remain pending across an ordinary nested call.
    pub fn require_owner_scope(&self, scope: &OwnerScope) -> Result<(), String> {
        if scope.arena != self.owner {
            return Err("owner scope belongs to a different plane arena".into());
        }
        if self.early_owners == 0 {
            return Ok(());
        }
        if self
            .early_owner_tokens()
            .any(|token| !scope.inherited.contains(&token))
        {
            return Err(
                "early shared ownership must be materialized before leaving its scope".into(),
            );
        }
        Ok(())
    }

    /// No promise may escape the outer boundary unfulfilled.
    pub fn require_materialized_owners(&self) -> Result<(), String> {
        self.require_owner_scope(&OwnerScope {
            arena: self.owner,
            inherited: BTreeSet::new(),
        })
    }

    fn early_owner_tokens(&self) -> impl Iterator<Item = u64> + '_ {
        self.planes.iter().flat_map(|plane| {
            let tokens = match &plane.ownership {
                Ownership::Unique => None,
                Ownership::Shared(tokens) => Some(tokens),
            };
            tokens
                .into_iter()
                .flat_map(|tokens| tokens.iter())
                .filter_map(|(&token, &state)| (state == OwnerState::Early).then_some(token))
        })
    }
}

#[cfg(test)]
mod tests;
