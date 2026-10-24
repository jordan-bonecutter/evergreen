import Std
set_option warningAsError true
set_option autoImplicit false

namespace Evergreen.PropositionalProofs

-- Independent specification of the structural proof rules. This does not
-- establish that the Rust frontend or its normalization implements these rules.
inductive Formula where
  | atom : Nat → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | neg : Formula → Formula

def Holds (valuation : Nat → Prop) : Formula → Prop
  | .atom name => valuation name
  | .bot => False
  | .conj a b => Holds valuation a ∧ Holds valuation b
  | .disj a b => Holds valuation a ∨ Holds valuation b
  | .implies a b => Holds valuation a → Holds valuation b
  | .neg a => ¬ Holds valuation a

inductive Derives : List Formula → Formula → Prop where
  | hypothesis {context : List Formula} {p : Formula} :
      p ∈ context → Derives context p
  | conjunction {context : List Formula} {a b : Formula} :
      Derives context a → Derives context b → Derives context (.conj a b)
  | left {context : List Formula} {a b : Formula} :
      Derives context a → Derives context (.disj a b)
  | right {context : List Formula} {a b : Formula} :
      Derives context b → Derives context (.disj a b)
  | intro {context : List Formula} {a b : Formula} :
      Derives (a :: context) b → Derives context (.implies a b)
  | apply {context : List Formula} {a b : Formula} :
      Derives context (.implies a b) → Derives context a → Derives context b
  | negate {context : List Formula} {a : Formula} :
      Derives (a :: context) .bot → Derives context (.neg a)
  | refute {context : List Formula} {a : Formula} :
      Derives context (.neg a) → Derives context a → Derives context .bot

theorem sound {context : List Formula} {p : Formula}
    (derivation : Derives context p) (valuation : Nat → Prop) :
    (∀ q, q ∈ context → Holds valuation q) → Holds valuation p := by
  induction derivation with
  | hypothesis present =>
    intro known
    exact known _ present
  | conjunction _ _ first second =>
    intro known
    exact ⟨first known, second known⟩
  | left _ checked =>
    intro known
    exact Or.inl (checked known)
  | right _ checked =>
    intro known
    exact Or.inr (checked known)
  | intro _ checked =>
    intro known premise
    apply checked
    intro q member
    rcases List.mem_cons.mp member with same | previous
    · subst q
      exact premise
    · exact known q previous
  | apply _ _ implication premise =>
    intro known
    exact (implication known) (premise known)
  | negate _ checked =>
    intro known premise
    apply checked
    intro q member
    rcases List.mem_cons.mp member with same | previous
    · subst q
      exact premise
    · exact known q previous
  | refute _ _ negative positive =>
    intro known
    exact (negative known) (positive known)

-- The arithmetic frontend lowers implication to this classical Boolean form.
theorem implication_as_disjunction (valuation : Nat → Prop) (a b : Formula) :
    Holds valuation (.implies a b) ↔ Holds valuation (.disj (.neg a) b) := by
  change (Holds valuation a → Holds valuation b) ↔
    (¬ Holds valuation a ∨ Holds valuation b)
  classical
  constructor
  · intro implication
    by_cases premise : Holds valuation a
    · exact Or.inr (implication premise)
    · exact Or.inl premise
  · rintro (absent | present) allowed
    · exact False.elim (absent allowed)
    · exact present

-- A hypothesis can close its own subgoal but cannot survive an intro scope.
example : Derives [.bot] .bot := .hypothesis (by simp)

theorem no_closed_false : ¬ Derives [] .bot := by
  intro derivation
  exact sound derivation (fun _ => False) (by
    intro q member
    cases member)

end Evergreen.PropositionalProofs
