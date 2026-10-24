import Std
set_option warningAsError true
set_option autoImplicit false

namespace Evergreen.LinearCertificates

-- Mathematical model of the internal kernel's weighted-row rule. This is not
-- a proof that the Rust frontend, finite-map implementation, or emitter refines
-- the model. Machine arithmetic must additionally fail closed on overflow.
structure Row (variables : Nat) where
  constant : Int
  coefficient : Fin variables → Int

def sum (n : Nat) (f : Fin n → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => f 0 + sum k (fun i => f i.succ)

theorem sum_add (n : Nat) (a b : Fin n → Int) :
    sum n (fun i => a i + b i) = sum n a + sum n b := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sum, ih]
    omega

theorem sum_scale (n : Nat) (w : Int) (a : Fin n → Int) :
    sum n (fun i => w * a i) = w * sum n a := by
  induction n with
  | zero => simp [sum]
  | succ k ih => simp [sum, ih, Int.mul_add]

theorem sum_zero (n : Nat) : sum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sum, ih]

def evaluate {n : Nat} (row : Row n) (valuation : Fin n → Int) : Int :=
  row.constant + sum n (fun i => row.coefficient i * valuation i)

def zero (n : Nat) : Row n := ⟨0, fun _ => 0⟩
def add {n : Nat} (a b : Row n) : Row n :=
  ⟨a.constant + b.constant, fun i => a.coefficient i + b.coefficient i⟩
def scale {n : Nat} (w : Int) (a : Row n) : Row n :=
  ⟨w * a.constant, fun i => w * a.coefficient i⟩

theorem evaluate_zero (n : Nat) (v : Fin n → Int) : evaluate (zero n) v = 0 := by
  simp [evaluate, zero, sum_zero]

theorem evaluate_add {n : Nat} (a b : Row n) (v : Fin n → Int) :
    evaluate (add a b) v = evaluate a v + evaluate b v := by
  simp only [evaluate, add, Int.add_mul, sum_add]
  omega

theorem evaluate_scale {n : Nat} (w : Int) (a : Row n) (v : Fin n → Int) :
    evaluate (scale w a) v = w * evaluate a v := by
  simp [evaluate, scale, Int.mul_assoc, sum_scale, Int.mul_add]

-- Unlike the search algorithm, this checker can only combine original rows.
-- Missing row indices and negative weights fail instead of adding assumptions.
def combine {n : Nat} (rows : List (Row n)) : List (Nat × Int) → Option (Row n)
  | [] => some (zero n)
  | (index, weight) :: rest =>
    if weight < 0 then none else
      match rows[index]?, combine rows rest with
      | some row, some total => some (add total (scale weight row))
      | _, _ => none

theorem combine_nonnegative {n : Nat} (rows : List (Row n))
    (weights : List (Nat × Int)) (total : Row n) (v : Fin n → Int)
    (valid : ∀ row ∈ rows, 0 ≤ evaluate row v)
    (accepted : combine rows weights = some total) : 0 ≤ evaluate total v := by
  induction weights generalizing total with
  | nil =>
    simp only [combine, Option.some.injEq] at accepted
    subst total
    simp [evaluate_zero]
  | cons entry rest ih =>
    rcases entry with ⟨index, weight⟩
    simp only [combine] at accepted
    split at accepted
    · contradiction
    · rename_i nonnegative
      cases lookup : rows[index]? with
      | none => simp [lookup] at accepted
      | some row =>
        cases tail : combine rows rest with
        | none => simp [lookup, tail] at accepted
        | some previous =>
          simp only [lookup, tail, Option.some.injEq] at accepted
          subst total
          rw [evaluate_add, evaluate_scale]
          have row_valid := valid row (List.mem_of_getElem? lookup)
          have weight_valid : 0 ≤ weight := by omega
          exact Int.add_nonneg (ih previous tail) (Int.mul_nonneg weight_valid row_valid)

def check {n : Nat} (rows : List (Row n)) (weights : List (Nat × Int)) : Bool :=
  match combine rows weights with
  | none => false
  | some total => decide (total.constant < 0 ∧ ∀ i, total.coefficient i = 0)

theorem check_sound {n : Nat} (rows : List (Row n)) (weights : List (Nat × Int))
    (accepted : check rows weights = true) :
    ¬ ∃ valuation, ∀ row ∈ rows, 0 ≤ evaluate row valuation := by
  intro ⟨valuation, valid⟩
  unfold check at accepted
  cases combined : combine rows weights with
  | none => simp [combined] at accepted
  | some total =>
    simp only [combined, decide_eq_true_eq] at accepted
    have nonnegative := combine_nonnegative rows weights total valuation valid combined
    have evaluation : evaluate total valuation = total.constant := by
      simp [evaluate, accepted.2, sum_zero]
    rw [evaluation] at nonnegative
    omega

-- Canonical conjunction keys may disregard row order and repetitions. The
-- retained path itself keeps its original rows for certificate indexing.
theorem same_rows_same_models {n : Nat} (left right : List (Row n))
    (same : ∀ row, row ∈ left ↔ row ∈ right) (valuation : Fin n → Int) :
    (∀ row ∈ left, 0 ≤ evaluate row valuation) ↔
      (∀ row ∈ right, 0 ≤ evaluate row valuation) := by
  constructor
  · intro valid row present
    exact valid row ((same row).mpr present)
  · intro valid row present
    exact valid row ((same row).mp present)

-- An overflow path may be removed only after its contradiction is checked.
theorem certified_path_removal {n : Nat} (rows : List (Row n))
    (weights : List (Nat × Int)) (accepted : check rows weights = true)
    (valuation : Fin n → Int) (remaining : Prop) :
    ((∀ row ∈ rows, 0 ≤ evaluate row valuation) ∨ remaining) ↔ remaining := by
  constructor
  · rintro (invalid | kept)
    · exact False.elim (check_sound rows weights accepted ⟨valuation, invalid⟩)
    · exact kept
  · intro kept
    exact Or.inr kept

-- Concrete certificates also exercise the executable model's rejection paths.
def atLeastOne : Row 1 := ⟨-1, fun _ => 1⟩
def atMostZero : Row 1 := ⟨0, fun _ => -1⟩
example : check [atLeastOne, atMostZero] [(0, 1), (1, 1)] = true := by decide
example : check [atLeastOne, atMostZero] [(0, -1)] = false := by decide
example : check [atLeastOne, atMostZero] [(2, 1)] = false := by decide
example : check [atLeastOne, atMostZero] [(0, 1)] = false := by decide
example : check [atLeastOne, atMostZero] [] = false := by decide

end Evergreen.LinearCertificates
