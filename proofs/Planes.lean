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

-- Erasing record fields is modeled as a projection. Replacing proof fields
-- frames runtime-only properties, but a joint record invariant still needs a
-- new check. This specifies separation, not the Rust/native representation.
structure PhasedRecord (Runtime Ideal : Type) where
  runtime : Runtime
  ideal : Ideal

def replaceIdeal {Runtime Before After : Type} (record : PhasedRecord Runtime Before)
    (next : After) : PhasedRecord Runtime After := ⟨record.runtime, next⟩

theorem ideal_field_replacement_erases {Runtime Before After : Type}
    (record : PhasedRecord Runtime Before) (next : After) :
    (replaceIdeal record next).runtime = record.runtime := rfl

theorem ideal_fields_frame_runtime_property {Runtime Before After : Type}
    (record : PhasedRecord Runtime Before) (next : After) (property : Runtime → Prop)
    (valid : property record.runtime) : property (replaceIdeal record next).runtime := valid

example : (⟨7, 7⟩ : PhasedRecord Nat Nat).runtime = 7 ∧
    (replaceIdeal (⟨7, 7⟩ : PhasedRecord Nat Nat) 42).runtime ≠
      (replaceIdeal (⟨7, 7⟩ : PhasedRecord Nat Nat) 42).ideal := by decide

-- The owner slot and separately allocated payload have distinct identities.
-- These equations specify the intended transitions, not the compiler's
-- enforcement of uniqueness or the native allocator's implementation.
structure OwnedAllocation where
  ownerSlot : Plane
  payload : Plane

def moveAllocationOwner (allocation : OwnedAllocation) : OwnedAllocation :=
  { allocation with ownerSlot := dropPlane allocation.ownerSlot }

def freeAllocation (allocation : OwnedAllocation) : OwnedAllocation :=
  { ownerSlot := dropPlane allocation.ownerSlot,
    payload := dropPlane allocation.payload }

theorem owner_move_keeps_payload_reference (allocation : OwnedAllocation)
    (reference : Reference) (valid : Valid allocation.payload reference) :
    Valid (moveAllocationOwner allocation).payload reference := valid

theorem owner_move_invalidates_old_slot (allocation : OwnedAllocation)
    (reference : Reference) :
    ¬ Valid (moveAllocationOwner allocation).ownerSlot reference :=
  dropped_references_invalid allocation.ownerSlot reference

theorem freeing_invalidates_payload_reference (allocation : OwnedAllocation)
    (reference : Reference) :
    ¬ Valid (freeAllocation allocation).payload reference :=
  dropped_references_invalid allocation.payload reference

-- An atomic update publishes only a new state satisfying its invariant.
def commit {State : Type} (invariant : State → Prop)
    (next : State) (proof : invariant next) : { s : State // invariant s } :=
  ⟨next, proof⟩

theorem commit_preserves {State : Type} (invariant : State → Prop)
    (next : State) (proof : invariant next) :
    invariant (commit invariant next proof).val := by
  exact (commit invariant next proof).property

-- Generic ownership roles, independent of any Rc counter or library type.
-- This census represents all live owning bindings for one allocation, including
-- bindings outside the current function. Borrowed references are not entries.
-- Connecting this model to source affinity and compiler stores is still work.
namespace OwnerReferences

structure Store where
  plane : Plane
  owned : List Nat
  borrowed : List Reference

def ownerCount (s : Store) : Nat := s.owned.length

def WellFormed (s : Store) : Prop := s.owned.Nodup

def Owns (s : Store) (token : Nat) (reference : Reference) : Prop :=
  token ∈ s.owned ∧ Valid s.plane reference

def borrow (s : Store) (reference : Reference) : Store :=
  { s with borrowed := reference :: s.borrowed }

theorem borrow_does_not_change_owner_count (s : Store) (reference : Reference) :
    ownerCount (borrow s reference) = ownerCount s := rfl

theorem borrow_does_not_create_ownership (s : Store) (reference view : Reference)
    (token : Nat) : Owns (borrow s reference) token view ↔ Owns s token view := Iff.rfl

theorem borrow_preserves_well_formedness (s : Store) (reference : Reference)
    (well : WellFormed s) : WellFormed (borrow s reference) := well

-- Fresh token IDs distinguish owners even when their machine addresses agree.
def duplicate (s : Store) (fresh : Nat) : Store :=
  { s with owned := fresh :: s.owned }

theorem duplicate_count (s : Store) (fresh : Nat) :
    ownerCount (duplicate s fresh) = ownerCount s + 1 := by
  simp [ownerCount, duplicate]

theorem duplicate_preserves_well_formedness (s : Store) (fresh : Nat)
    (well : WellFormed s) (unused : fresh ∉ s.owned) :
    WellFormed (duplicate s fresh) := by
  exact List.nodup_cons.mpr ⟨unused, well⟩

theorem duplicate_preserves_borrow_validity (s : Store) (fresh : Nat)
    (reference : Reference) :
    Valid (duplicate s fresh).plane reference ↔ Valid s.plane reference := Iff.rfl

theorem duplicate_produces_owner (s : Store) (fresh existing : Nat)
    (reference : Reference) (owned : Owns s existing reference) :
    Owns (duplicate s fresh) fresh reference := by
  exact ⟨by simp [duplicate], owned.2⟩

-- Moving/rearranging bindings does not copy a token or change its allocation.
def moveBindings (s : Store) (next : List Nat) (_same : s.owned.Perm next) : Store :=
  { s with owned := next }

theorem move_preserves_owner_count (s : Store) (next : List Nat)
    (same : s.owned.Perm next) : ownerCount (moveBindings s next same) = ownerCount s := by
  exact same.length_eq.symm

theorem move_preserves_well_formedness (s : Store) (next : List Nat)
    (same : s.owned.Perm next) (well : WellFormed s) :
    WellFormed (moveBindings s next same) := same.nodup_iff.mp well

def release (s : Store) (token : Nat) : Store :=
  { s with owned := s.owned.erase token }

theorem release_count (s : Store) (token : Nat) (member : token ∈ s.owned) :
    ownerCount (release s token) + 1 = ownerCount s := by
  have positive := List.length_pos_of_mem member
  have erased := List.length_erase_of_mem member
  simp only [ownerCount, release]
  omega

theorem release_preserves_well_formedness (s : Store) (token : Nat)
    (well : WellFormed s) : WellFormed (release s token) :=
  List.Nodup.sublist List.erase_sublist well

theorem release_preserves_borrow_validity (s : Store) (token : Nat)
    (reference : Reference) :
    Valid (release s token).plane reference ↔ Valid s.plane reference := Iff.rfl

theorem one_owner_is_unique (s : Store) (token : Nat)
    (member : token ∈ s.owned) (one : ownerCount s = 1) : s.owned = [token] := by
  obtain ⟨only, equal⟩ := List.length_eq_one_iff.mp one
  have same : token = only := by simpa [equal] using member
  simpa [same] using equal

-- Recovery requires both an actual live owning reference and the current count.
-- A borrowed reference alone cannot construct this witness.
structure UniqueOwner (s : Store) where
  token : Nat
  reference : Reference
  owned : Owns s token reference
  unique : ownerCount s = 1

def recoverUnique (s : Store) (token : Nat) (reference : Reference)
    (owned : Owns s token reference) (unique : ownerCount s = 1) : UniqueOwner s :=
  ⟨token, reference, owned, unique⟩

theorem recovered_owner_is_sole (s : Store) (owner : UniqueOwner s) :
    s.owned = [owner.token] := one_owner_is_unique s owner.token owner.owned.1 owner.unique

theorem duplication_invalidates_old_uniqueness (s : Store) (owner : UniqueOwner s)
    (fresh : Nat) : ownerCount (duplicate s fresh) ≠ 1 := by
  rw [duplicate_count, owner.unique]
  omega

def freeUnique (s : Store) (_owner : UniqueOwner s) : Store :=
  { s with plane := dropPlane s.plane, owned := [] }

theorem free_leaves_no_owners (s : Store) (owner : UniqueOwner s) :
    ownerCount (freeUnique s owner) = 0 := rfl

theorem free_invalidates_borrows (s : Store) (owner : UniqueOwner s)
    (reference : Reference) : ¬ Valid (freeUnique s owner).plane reference :=
  dropped_references_invalid s.plane reference

theorem free_invalidates_owner (s : Store) (owner : UniqueOwner s)
    (token : Nat) (reference : Reference) : ¬ Owns (freeUnique s owner) token reference := by
  simp [Owns, freeUnique]

theorem owner_free_does_not_revive_after_restore (s : Store) (owner : UniqueOwner s)
    (reference : Reference) (valid : Valid s.plane reference) :
    ¬ Valid (writePlane (freeUnique s owner).plane false) reference :=
  restore_does_not_revive s.plane reference valid

theorem borrowing_an_unowned_plane_cannot_recover_ownership (s : Store)
    (empty : s.owned = []) (reference view : Reference) (token : Nat) :
    ¬ Owns (borrow s reference) token view := by
  simp [Owns, borrow, empty]

-- Only these guarded transitions are executable model steps. The raw functions
-- above describe candidate states; arbitrary calls to them are not ownership rules.
inductive Step : Store → Store → Prop where
  | borrow (s : Store) (reference : Reference) (valid : Valid s.plane reference) :
      Step s (borrow s reference)
  | duplicate (s : Store) (existing fresh : Nat) (reference : Reference)
      (owned : Owns s existing reference) (unused : fresh ∉ s.owned) :
      Step s (duplicate s fresh)
  | move (s : Store) (next : List Nat) (same : s.owned.Perm next) :
      Step s (moveBindings s next same)
  | release (s : Store) (token : Nat) (reference : Reference)
      (owned : Owns s token reference) : Step s (release s token)
  | free (s : Store) (owner : UniqueOwner s) : Step s (freeUnique s owner)

theorem step_preserves_well_formedness {before after : Store}
    (well : WellFormed before) (step : Step before after) : WellFormed after := by
  cases step with
  | borrow reference _ => exact borrow_preserves_well_formedness before reference well
  | duplicate _ fresh _ _ unused => exact duplicate_preserves_well_formedness before fresh well unused
  | move next same => exact move_preserves_well_formedness before next same well
  | release token _ _ => exact release_preserves_well_formedness before token well
  | free _ => simp [WellFormed, freeUnique]

theorem step_cannot_mint_from_no_owners {before after : Store}
    (empty : ownerCount before = 0) (step : Step before after) : ownerCount after = 0 := by
  cases step with
  | borrow _ _ => exact empty
  | duplicate _ _ _ owned _ =>
      have positive := List.length_pos_of_mem owned.1
      simp only [ownerCount] at empty
      omega
  | move _ _ => rw [move_preserves_owner_count]; exact empty
  | release _ _ owned =>
      have positive := List.length_pos_of_mem owned.1
      simp only [ownerCount] at empty
      omega
  | free _ => rfl

inductive Runs : Store → Store → Prop where
  | refl (s : Store) : Runs s s
  | next {start middle finish : Store} : Runs start middle → Step middle finish → Runs start finish

theorem runs_cannot_resurrect_ownership {before after : Store}
    (empty : ownerCount before = 0) (run : Runs before after) : ownerCount after = 0 := by
  induction run with
  | refl => exact empty
  | next _ step previous => exact step_cannot_mint_from_no_owners previous step

theorem runs_preserve_well_formedness {before after : Store}
    (well : WellFormed before) (run : Runs before after) : WellFormed after := by
  induction run with
  | refl => exact well
  | next _ step previous => exact step_preserves_well_formedness previous step

end OwnerReferences

end Evergreen
