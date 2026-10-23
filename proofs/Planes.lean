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

-- Aliasing itself is allowed: validity contains no uniqueness requirement.
theorem aliases_allowed (p : Plane) (a b : Reference)
    (ha : Valid p a) (hb : Valid p b) : Valid p a ∧ Valid p b := by
  exact ⟨ha, hb⟩

-- An atomic update publishes only a new state satisfying its invariant.
def commit {State : Type} (invariant : State → Prop)
    (next : State) (proof : invariant next) : { s : State // invariant s } :=
  ⟨next, proof⟩

theorem commit_preserves {State : Type} (invariant : State → Prop)
    (next : State) (proof : invariant next) :
    invariant (commit invariant next proof).val := by
  exact (commit invariant next proof).property

end Evergreen
