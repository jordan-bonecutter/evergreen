import Std
set_option warningAsError true
set_option autoImplicit false

namespace Evergreen

-- A first specification, not yet a verified implementation of an allocator.
structure Plane where
  id : Nat
  epoch : Nat
  live : Bool

structure Reference where
  plane : Nat
  epoch : Nat

def Valid (p : Plane) (r : Reference) : Prop :=
  p.live = true ∧ r.plane = p.id ∧ r.epoch = p.epoch

def dropPlane (p : Plane) : Plane :=
  { id := p.id, epoch := p.epoch + 1, live := false }

def replacePlane (p : Plane) : Plane :=
  { id := p.id, epoch := p.epoch + 1, live := true }

theorem dropped_references_invalid (p : Plane) (r : Reference) :
    ¬ Valid (dropPlane p) r := by
  simp [Valid, dropPlane]

theorem replacement_invalidates (p : Plane) (r : Reference)
    (h : Valid p r) : ¬ Valid (replacePlane p) r := by
  simp only [Valid, replacePlane] at *
  omega

-- Same-layout writes preserve live storage identity. Writing into shape(T)
-- restores initialization with a fresh epoch; it cannot revive old references.
def writePlane (p : Plane) (replace : Bool) : Plane :=
  if replace || !p.live then
    { id := p.id, epoch := p.epoch + 1, live := true }
  else { p with live := true }

theorem same_layout_write_preserves (p : Plane) (r : Reference)
    (h : Valid p r) : Valid (writePlane p false) r := by
  simp [writePlane, Valid, h.1, h.2.1, h.2.2]

theorem restore_does_not_revive (p : Plane) (r : Reference)
    (h : Valid p r) : ¬ Valid (writePlane (dropPlane p) false) r := by
  simp only [Valid, dropPlane, writePlane, Bool.not_false, Bool.false_or,
    if_true] at *
  omega

-- Once both generations are valid in one current plane, handle identity is
-- fixed. Projection paths distinguish locations within that plane separately.
theorem valid_reference_handles_unique (p : Plane) (a b : Reference)
    (ha : Valid p a) (hb : Valid p b) : a = b := by
  cases a
  cases b
  simp_all [Valid]

-- Aliasing itself is allowed: validity contains no uniqueness requirement.
theorem aliases_allowed (p : Plane) (a b : Reference)
    (ha : Valid p a) (hb : Valid p b) : Valid p a ∧ Valid p b := by
  exact ⟨ha, hb⟩

-- Bookkeeping may change independently of a borrowed handle. This model does
-- not give that handle allocation authority or prove Rust erasure/affinity.
structure IdealBorrow (Metadata : Type) where
  metadata : Metadata
  reference : Reference

def mapMetadata {Before After : Type} (borrow : IdealBorrow Before) (next : After) :
    IdealBorrow After := ⟨next, borrow.reference⟩

theorem metadata_preserves_validity {Before After : Type} (p : Plane)
    (borrow : IdealBorrow Before) (next : After) :
    Valid p (mapMetadata borrow next).reference ↔ Valid p borrow.reference := Iff.rfl

theorem metadata_cannot_revive_dropped_borrow {Before After : Type} (p : Plane)
    (borrow : IdealBorrow Before) (next : After) :
    ¬ Valid (dropPlane p) (mapMetadata borrow next).reference :=
  dropped_references_invalid p borrow.reference

theorem metadata_cannot_revive_restored_borrow {Before After : Type} (p : Plane)
    (borrow : IdealBorrow Before) (next : After) (valid : Valid p borrow.reference) :
    ¬ Valid (writePlane (dropPlane p) false) (mapMetadata borrow next).reference :=
  restore_does_not_revive p borrow.reference valid

-- An atomic update publishes only a new state satisfying its invariant.
def commit {State : Type} (invariant : State → Prop)
    (next : State) (proof : invariant next) : { s : State // invariant s } :=
  ⟨next, proof⟩

theorem commit_preserves {State : Type} (invariant : State → Prop)
    (next : State) (proof : invariant next) :
    invariant (commit invariant next proof).val := by
  exact (commit invariant next proof).property

end Evergreen
