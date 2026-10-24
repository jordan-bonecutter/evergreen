import Std
set_option warningAsError true
set_option autoImplicit false

namespace Evergreen.MemoryContracts

-- Scalar leaves of a fixed layout. Field and index steps remain distinguished.
-- This model specifies the disjoint-write rule, not an allocator or x86 memory.
inductive Step where
  | field : Nat → Step
  | index : Nat → Step
  deriving DecidableEq

structure Address where
  plane : Nat
  path : List Step
  deriving DecidableEq

def Disjoint (a b : Address) : Prop :=
  a.plane ≠ b.plane ∨ (¬ a.path <+: b.path) ∧ (¬ b.path <+: a.path)

theorem disjoint_ne (a b : Address) (h : Disjoint a b) : a ≠ b := by
  intro same
  subst b
  rcases h with different | ⟨noPrefix, _⟩
  · exact different rfl
  · exact noPrefix ⟨[], by simp⟩

theorem distinct_fields_disjoint (plane left right : Nat) (h : left ≠ right) :
    Disjoint ⟨plane, [.field left]⟩ ⟨plane, [.field right]⟩ := by
  right
  constructor
  · rintro ⟨tail, equal⟩
    cases tail with
    | nil => simp at equal; exact h equal
    | cons head rest => simp at equal
  · rintro ⟨tail, equal⟩
    cases tail with
    | nil => simp at equal; exact h equal.symm
    | cons head rest => simp at equal

def indexed (plane index : Nat) : Address := ⟨plane, [.index index]⟩

theorem indexed_eq_iff (plane i j : Nat) : indexed plane i = indexed plane j ↔ i = j := by
  simp [indexed, Address.mk.injEq]

def Store := Address → Int

def write (store : Store) (target : Address) (value : Int) : Store :=
  fun queried => if queried = target then value else store queried

theorem read_write (store : Store) (target : Address) (value : Int) :
    write store target value target = value := by simp [write]

-- No disjointness premise: a dynamic index may alias the written cell.
theorem indexed_write (store : Store) (plane i j : Nat) (value : Int) :
    write store (indexed plane i) value (indexed plane j) =
      if j = i then value else store (indexed plane j) := by
  simp [write, indexed_eq_iff]

theorem frame (store : Store) (target other : Address) (value : Int)
    (h : other ≠ target) : write store target value other = store other := by
  simp [write, h]

theorem disjoint_writes_commute (store : Store) (a b : Address) (x y : Int)
    (h : Disjoint a b) :
    write (write store a x) b y = write (write store b y) a x := by
  have different := disjoint_ne a b h
  funext queried
  by_cases at_a : queried = a
  · subst queried
    simp [write, different]
  · by_cases at_b : queried = b
    · subst queried
      simp [write, at_a]
    · simp [write, at_a, at_b]

def swap (store : Store) (a b : Address) : Store :=
  write (write store a (store b)) b (store a)

theorem swap_postcondition (store : Store) (a b : Address) (h : Disjoint a b) :
    swap store a b a = store b ∧ swap store a b b = store a := by
  have different := disjoint_ne a b h
  simp [swap, write, different]

theorem swap_frame (store : Store) (a b other : Address)
    (not_a : other ≠ a) (not_b : other ≠ b) :
    swap store a b other = store other := by
  simp [swap, write, not_a, not_b]

theorem swap_involution (store : Store) (a b : Address) (h : Disjoint a b) :
    swap (swap store a b) a b = store := by
  have post := swap_postcondition store a b h
  funext queried
  by_cases at_a : queried = a
  · subst queried
    rw [(swap_postcondition (swap store a b) a b h).1, post.2]
  · by_cases at_b : queried = b
    · subst queried
      rw [(swap_postcondition (swap store a b) a b h).2, post.1]
    · rw [swap_frame _ a b queried at_a at_b, swap_frame _ a b queried at_a at_b]

-- One input array gives the body a shared alias model. Its two indices need
-- not be distinct: both postconditions remain valid when they denote one cell.
theorem swap_postcondition_with_aliases (store : Store) (a b : Address) :
    swap store a b a = store b ∧ swap store a b b = store a := by
  by_cases same : a = b
  · subst b
    simp [swap, write]
  · simp [swap, write, same]

-- A region contract forgets arbitrary contents inside its footprint while
-- preserving everything outside. These are specification rules; there is no
-- claim here that the Rust frontend or native backend refines this model.
def Region := Address → Prop

def Modifies (region : Region) (before after : Store) : Prop :=
  ∀ queried, ¬ region queried → after queried = before queried

-- Repeated or coincident places form an idempotent permission union.
theorem modifies_repeated (region : Region) (before after : Store) :
    Modifies (fun queried => region queried ∨ region queried) before after ↔
      Modifies region before after := by
  simp only [Modifies, or_self]

theorem swap_modifies_union (store : Store) (a b : Address) :
    Modifies (fun queried => queried = a ∨ queried = b) store (swap store a b) := by
  intro queried outside
  apply swap_frame
  · intro equal
    exact outside (Or.inl equal)
  · intro equal
    exact outside (Or.inr equal)

def within (root queried : Address) : Prop :=
  queried.plane = root.plane ∧ root.path <+: queried.path

theorem within_trans (root child leaf : Address)
    (first : within root child) (second : within child leaf) : within root leaf := by
  exact ⟨second.1.trans first.1, first.2.trans second.2⟩

theorem region_frame (region : Region) (before after : Store)
    (effect : Modifies region before after) (queried : Address)
    (outside : ¬ region queried) : after queried = before queried := by
  exact effect queried outside

theorem modifies_weaken (small large : Region) (before after : Store)
    (included : ∀ address, small address → large address)
    (effect : Modifies small before after) : Modifies large before after := by
  intro queried outside
  apply effect queried
  intro inside
  exact outside (included queried inside)

theorem modifies_sequence (region : Region) (before middle after : Store)
    (first : Modifies region before middle) (second : Modifies region middle after) :
    Modifies region before after := by
  intro queried outside
  rw [second queried outside, first queried outside]

-- A nominal invariant can observe several planes through stored references.
-- Its read footprint must include those targets, not just the record's header.
def ReadsOnly (property : Store → Prop) (footprint : Region) : Prop :=
  ∀ before after, (∀ address, footprint address → before address = after address) →
    (property before ↔ property after)

theorem frame_invariant (property : Store → Prop) (reads writes : Region)
    (before after : Store) (observations : ReadsOnly property reads)
    (effects : Modifies writes before after)
    (separate : ∀ address, reads address → ¬ writes address)
    (valid : property before) : property after := by
  apply (observations before after ?_).mp valid
  intro address observed
  exact (effects address (separate address observed)).symm

example (header counter : Address) (separate : header ≠ counter) :
    write (fun _ => 1) counter 0 header = 1 ∧
      ¬ (write (fun _ => 1) counter 0 counter > 0) := by
  simp [write, separate]

def replaceRegion (store replacement : Store) (region : Region)
    [DecidablePred region] : Store :=
  fun queried => if region queried then replacement queried else store queried

theorem replace_region_modifies (store replacement : Store) (region : Region)
    [DecidablePred region] : Modifies region store (replaceRegion store replacement region) := by
  intro queried outside
  simp [replaceRegion, outside]

theorem replace_region_read (store replacement : Store) (region : Region)
    [DecidablePred region] (queried : Address) (inside : region queried) :
    replaceRegion store replacement region queried = replacement queried := by
  simp [replaceRegion, inside]

-- A conditional reference stays in one plane. Guarded index equalities and
-- branch-local bounds justify the selected view; an unconstrained fresh index
-- would not establish either theorem.
theorem joined_index_bounds (flag : Bool) (length left right selected : Nat)
    (left_bound : flag = true → left < length)
    (right_bound : flag = false → right < length)
    (left_case : flag = true → selected = left)
    (right_case : flag = false → selected = right) : selected < length := by
  cases flag <;> simp_all

theorem joined_index_read (store : Store) (plane : Nat) (flag : Bool)
    (left right selected : Nat)
    (left_case : flag = true → selected = left)
    (right_case : flag = false → selected = right) :
    store (indexed plane selected) =
      if flag then store (indexed plane left) else store (indexed plane right) := by
  cases flag <;> simp_all

-- A field update is a structural store of one complete record. This models
-- value framing, not record layouts, references, destructors, or Rust lowering.
def RecordArray := Nat → Nat → Int

def storeRecord (data : RecordArray) (index : Nat) (value : Nat → Int) : RecordArray :=
  fun queried => if queried = index then value else data queried

def storeField (data : RecordArray) (index field : Nat) (value : Int) : RecordArray :=
  storeRecord data index (fun queried => if queried = field then value else data index queried)

theorem record_field_store (data : RecordArray) (index field queried selected : Nat)
    (value : Int) :
    storeField data index field value queried selected =
      if queried = index ∧ selected = field then value else data queried selected := by
  by_cases same_record : queried = index <;>
    by_cases same_field : selected = field <;>
    simp_all [storeField, storeRecord]

theorem store_record_preserves_invariant (data : RecordArray) (index : Nat)
    (value : Nat → Int) (invariant : (Nat → Int) → Prop)
    (before : ∀ queried, invariant (data queried))
    (validated : invariant value) :
    ∀ queried, invariant (storeRecord data index value queried) := by
  intro queried
  by_cases same : queried = index
  · simp [storeRecord, same, validated]
  · simp [storeRecord, same, before queried]

-- The updated record's validity is an obligation; the store cannot grant it.
theorem stored_record_requires_invariant (data : RecordArray) (index : Nat)
    (value : Nat → Int) (invariant : (Nat → Int) → Prop)
    (after : ∀ queried, invariant (storeRecord data index value queried)) :
    invariant value := by
  simpa [storeRecord] using after index

end Evergreen.MemoryContracts
