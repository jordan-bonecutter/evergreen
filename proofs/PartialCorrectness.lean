import Std
set_option warningAsError true
set_option autoImplicit false

namespace Evergreen.PartialCorrectness

-- Abstract return semantics. None represents no ordinary return, including
-- divergence or an execution-budget abort. Total concerns the chosen abstract
-- run; it does not claim a bounded executor finishes every mathematical input.
-- This is not a Rust/VM refinement.
def Correct {Input Output : Type} (pre : Input → Prop)
    (run : Input → Option Output) (post : Input → Output → Prop) : Prop :=
  ∀ input output, pre input → run input = some output → post input output

def Total {Input Output : Type} (pre : Input → Prop)
    (run : Input → Option Output) : Prop :=
  ∀ input, pre input → ∃ output, run input = some output

theorem nonreturning_has_any_partial_postcondition {Input Output : Type}
    (pre : Input → Prop) (post : Input → Output → Prop) :
    Correct pre (fun _ => (none : Option Output)) post := by
  intro input output _ returned
  contradiction

-- A partial postcondition needs an actual return witness. It cannot by itself
-- provide a logical value, even if the postcondition happens to be False.
theorem observe_return {Input Output : Type} (pre : Input → Prop)
    (run : Input → Option Output) (post : Input → Output → Prop)
    (checked : Correct pre run post) (input : Input) (output : Output)
    (allowed : pre input) (returned : run input = some output) : post input output := by
  exact checked input output allowed returned

theorem total_observation {Input Output : Type} (pre : Input → Prop)
    (run : Input → Option Output) (post : Input → Output → Prop)
    (checked : Correct pre run post) (terminates : Total pre run)
    (input : Input) (allowed : pre input) :
    ∃ output, run input = some output ∧ post input output := by
  obtain ⟨output, returned⟩ := terminates input allowed
  exact ⟨output, returned, checked input output allowed returned⟩

theorem false_post_requires_no_return {Input Output : Type} (pre : Input → Prop)
    (run : Input → Option Output)
    (checked : Correct pre run (fun _ _ => False))
    (input : Input) (allowed : pre input) : ¬ ∃ output, run input = some output := by
  rintro ⟨output, returned⟩
  exact checked input output allowed returned

theorem correct_sequence {Input Middle Output : Type}
    (pre : Input → Prop) (middle : Middle → Prop) (post : Output → Prop)
    (first : Input → Option Middle) (second : Middle → Option Output)
    (first_checked : Correct pre first (fun _ value => middle value))
    (second_checked : Correct middle second (fun _ value => post value)) :
    Correct pre (fun input => (first input).bind second) (fun _ value => post value) := by
  intro input output allowed returned
  cases step : first input with
  | none => simp [step] at returned
  | some value =>
    have intermediate := first_checked input value allowed step
    exact second_checked value output intermediate (by simpa [step] using returned)

-- An independent-port summary covers only its disjoint input configurations.
-- The overlapping configurations need their own proof of the SAME execution,
-- such as checking the body with actual shared storage. Neither branch alone
-- licenses assuming its postcondition in the other configuration.
theorem correct_by_alias_partition {Input Output : Type}
    (pre separate : Input → Prop) (run : Input → Option Output)
    (post : Input → Output → Prop)
    (disjoint_checked : Correct (fun input => pre input ∧ separate input) run post)
    (overlap_checked : Correct (fun input => pre input ∧ ¬ separate input) run post) :
    Correct pre run post := by
  classical
  intro input output allowed returned
  by_cases disjoint : separate input
  · exact disjoint_checked input output ⟨allowed, disjoint⟩ returned
  · exact overlap_checked input output ⟨allowed, disjoint⟩ returned

example : Correct (fun _ : Unit => True) (fun _ => (none : Option Nat))
    (fun _ _ => False) := nonreturning_has_any_partial_postcondition _ _

example : ¬ Total (fun _ : Unit => True) (fun _ => (none : Option Nat)) := by
  intro terminates
  obtain ⟨output, returned⟩ := terminates () True.intro
  contradiction

-- A helper's endpoint postcondition cannot establish a retained invariant at
-- intermediate writes. An actual trace supplies that separate obligation.
def Maintains {State : Type} (retained : State → Prop) (states : List State) : Prop :=
  ∀ state ∈ states, retained state

theorem maintains_append {State : Type} (retained : State → Prop)
    (first second : List State) :
    Maintains retained (first ++ second) ↔
      Maintains retained first ∧ Maintains retained second := by
  simp only [Maintains, List.mem_append]
  constructor
  · intro checked
    exact ⟨fun state present => checked state (Or.inl present),
      fun state present => checked state (Or.inr present)⟩
  · rintro ⟨left, right⟩ state (present | present)
    · exact left state present
    · exact right state present

theorem update_exit {State : Type} (retained lifted : State → Prop)
    (initial final : State) (body : List State)
    (checked : Maintains retained (initial :: body ++ [final]))
    (restored : lifted final) : retained final ∧ lifted final := by
  exact ⟨checked final (by simp), restored⟩

example : Maintains (fun n : Nat => n > 0) [1, 2, 1] := by simp [Maintains]
example : (1 : Nat) > 0 ∧ ¬ Maintains (fun n : Nat => n > 0) [1, 0, 1] := by simp [Maintains]

-- Numeric release ordering, not allocation or actual owner-set authority.
def ZeroSafe (counts : Nat × Nat) : Prop := counts.1 = 0 → counts.2 = 0

theorem owner_first_release_trace (count : Nat) (positive : 0 < count) :
    Maintains ZeroSafe [(count, count), (count, count - 1), (count - 1, count - 1)] := by
  simp [Maintains, ZeroSafe]
  omega

theorem count_first_release_breaks_last_unit :
    ¬ Maintains ZeroSafe [(1, 1), (0, 1), (0, 0)] := by
  simp [Maintains, ZeroSafe]

end Evergreen.PartialCorrectness
