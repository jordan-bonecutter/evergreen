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

example : Correct (fun _ : Unit => True) (fun _ => (none : Option Nat))
    (fun _ _ => False) := nonreturning_has_any_partial_postcondition _ _

example : ¬ Total (fun _ : Unit => True) (fun _ => (none : Option Nat)) := by
  intro terminates
  obtain ⟨output, returned⟩ := terminates () True.intro
  contradiction

end Evergreen.PartialCorrectness
