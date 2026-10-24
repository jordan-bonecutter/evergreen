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

end Evergreen.MemoryContracts
