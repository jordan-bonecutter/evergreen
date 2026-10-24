import Std
set_option warningAsError true
set_option autoImplicit false

namespace Evergreen.SharedOwnership

-- Per-allocation protocol, with distinct affine token identities. This is not
-- yet an implementation of allocation authority or of the atomic instructions.
inductive Stage where
  | owner | reserved | retiring
  deriving DecidableEq

structure Token where
  id : Nat
  stage : Stage
  deriving DecidableEq

inductive Life where
  | active | reclaiming (lastToken : Nat) | freed
  deriving DecidableEq

structure State where
  tokens : List Token
  count : Nat
  fresh : Nat
  life : Life

structure Valid (limit : Nat) (s : State) : Prop where
  accounting : s.count = s.tokens.length
  bounded : s.count ≤ limit
  unique : (s.tokens.map Token.id).Nodup
  fresh : ∀ t ∈ s.tokens, t.id < s.fresh
  life : match s.life with
    | .active => 0 < s.count
    | .reclaiming id => s.count = 0 ∧ id < s.fresh
    | .freed => s.count = 0

def initial : State := ⟨[⟨0, .owner⟩], 1, 1, .active⟩

theorem initial_valid (limit : Nat) (positive : 0 < limit) : Valid limit initial := by
  constructor <;> simp [initial]
  · omega

def change (id : Nat) (stage : Stage) (t : Token) : Token :=
  if t.id = id then { t with stage := stage } else t

@[simp] theorem change_id (id : Nat) (stage : Stage) (t : Token) :
    (change id stage t).id = t.id := by
  unfold change
  split <;> rfl

@[simp] theorem changed_ids (id : Nat) (stage : Stage) (tokens : List Token) :
    ((tokens.map (change id stage)).map Token.id) = tokens.map Token.id := by
  simp [List.map_map, Function.comp_def]

def reserve (s : State) : State :=
  {s with tokens := ⟨s.fresh, .reserved⟩ :: s.tokens,
          count := s.count + 1, fresh := s.fresh + 1}

def changeStage (s : State) (id : Nat) (stage : Stage) : State :=
  {s with tokens := s.tokens.map (change id stage)}

def decrement (s : State) (id : Nat) : State :=
  {s with tokens := s.tokens.erase ⟨id, .retiring⟩,
          count := s.count - 1,
          life := if s.count = 1 then .reclaiming id else .active}

def free (s : State) : State := {s with life := .freed}

-- Reserve and decrement are indivisible counter steps. Publish and retire
-- change only the ideal classification of an already-owned token.
inductive Step (limit : Nat) : State → State → Prop where
  | reserve (s : State) (owner : Nat)
      (owned : ⟨owner, .owner⟩ ∈ s.tokens) (active : s.life = .active)
      (room : s.count < limit) : Step limit s (reserve s)
  | publish (s : State) (id : Nat) (pending : ⟨id, .reserved⟩ ∈ s.tokens) :
      Step limit s (changeStage s id .owner)
  | retire (s : State) (id : Nat) (owned : ⟨id, .owner⟩ ∈ s.tokens) :
      Step limit s (changeStage s id .retiring)
  | decrement (s : State) (id : Nat) (pending : ⟨id, .retiring⟩ ∈ s.tokens)
      (active : s.life = .active) : Step limit s (decrement s id)
  | free (s : State) (id : Nat) (permit : s.life = .reclaiming id) :
      Step limit s (free s)

theorem reserve_valid {limit : Nat} {s : State} (h : Valid limit s)
    (active : s.life = .active) (room : s.count < limit) : Valid limit (reserve s) := by
  have freshId : s.fresh ∉ s.tokens.map Token.id := by
    intro member
    obtain ⟨t, member, equal⟩ := List.mem_map.mp member
    have older := h.fresh t member
    omega
  constructor
  · simp [reserve, h.accounting]
  · simp only [reserve]
    omega
  · simpa [reserve] using (List.nodup_cons.mpr ⟨freshId, h.unique⟩)
  · intro t member
    simp only [reserve, List.mem_cons] at member
    rcases member with equal | member
    · subst t
      simp [reserve]
    · have older := h.fresh t member
      simp only [reserve]
      omega
  · simp [reserve, active]

theorem change_valid {limit : Nat} {s : State} (h : Valid limit s)
    (id : Nat) (stage : Stage) : Valid limit (changeStage s id stage) := by
  constructor
  · simpa [changeStage] using h.accounting
  · exact h.bounded
  · change (List.map Token.id (s.tokens.map (change id stage))).Nodup
    rw [changed_ids]
    exact h.unique
  · intro t member
    change t ∈ s.tokens.map (change id stage) at member
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
    have older := h.fresh old oldMember
    subst t
    simpa [changeStage] using older
  · exact h.life

theorem decrement_valid {limit : Nat} {s : State} (h : Valid limit s)
    (id : Nat) (pending : ⟨id, .retiring⟩ ∈ s.tokens) : Valid limit (decrement s id) := by
  have positive := List.length_pos_of_mem pending
  have older := h.fresh ⟨id, .retiring⟩ pending
  constructor
  · simp [decrement, List.length_erase_of_mem pending, h.accounting]
  · simp only [decrement]
    have bound := h.bounded
    omega
  · exact h.unique.sublist (List.erase_sublist.map Token.id)
  · intro t member
    exact h.fresh t (List.mem_of_mem_erase member)
  · by_cases last : s.count = 1
    · simpa [decrement, last] using older
    · simp only [decrement, last, if_false]
      have accounting := h.accounting
      omega

theorem free_valid {limit : Nat} {s : State} (h : Valid limit s)
    (id : Nat) (permit : s.life = .reclaiming id) : Valid limit (free s) := by
  refine ⟨h.accounting, h.bounded, h.unique, h.fresh, ?_⟩
  have life : s.count = 0 ∧ id < s.fresh := by simpa [permit] using h.life
  exact life.left

theorem step_preserves {limit : Nat} {s t : State} (h : Valid limit s)
    (step : Step limit s t) : Valid limit t := by
  cases step with
  | reserve owner owned active room => exact reserve_valid h active room
  | publish id pending => exact change_valid h id .owner
  | retire id owned => exact change_valid h id .retiring
  | decrement id pending active => exact decrement_valid h id pending
  | free id permit => exact free_valid h id permit

-- All interleavings, rather than a fixed enumeration of clone/drop examples.
inductive Runs (limit : Nat) : State → State → Prop where
  | refl (s : State) : Runs limit s s
  | next {s t u : State} : Runs limit s t → Step limit t u → Runs limit s u

theorem runs_preserve {limit : Nat} {s t : State} (h : Valid limit s)
    (run : Runs limit s t) : Valid limit t := by
  induction run with
  | refl => exact h
  | next run step ih => exact step_preserves ih step

theorem zero_has_no_tokens {limit : Nat} {s : State} (h : Valid limit s)
    (zero : s.count = 0) : s.tokens = [] := by
  apply List.length_eq_zero_iff.mp
  have accounting := h.accounting
  omega

theorem token_protects_allocation {limit : Nat} {s : State} (h : Valid limit s)
    (token : Token) (held : token ∈ s.tokens) : s.life = .active := by
  have positive := List.length_pos_of_mem held
  have accounting := h.accounting
  have life := h.life
  cases phase : s.life with
  | active => rfl
  | reclaiming id => simp only [phase] at life; omega
  | freed => simp only [phase] at life; omega

theorem reserve_identity_is_fresh {limit : Nat} {s : State} (h : Valid limit s)
    (stage : Stage) : ⟨s.fresh, stage⟩ ∉ s.tokens := by
  intro held
  have older := h.fresh ⟨s.fresh, stage⟩ held
  exact Nat.lt_irrefl s.fresh older

theorem change_consumes_old_stage (s : State) (id : Nat) (before after : Stage)
    (different : after ≠ before) : ⟨id, before⟩ ∉ (changeStage s id after).tokens := by
  intro held
  obtain ⟨old, _, equal⟩ := List.mem_map.mp held
  have ids := congrArg Token.id equal
  simp only [change_id] at ids
  have stages := congrArg Token.stage equal
  simp [change, ids] at stages
  exact different stages

theorem final_decrement_grants_reclamation {limit : Nat} {s : State}
    (h : Valid limit s) (id : Nat) (held : ⟨id, .retiring⟩ ∈ s.tokens)
    (last : s.count = 1) :
    (decrement s id).life = .reclaiming id ∧ (decrement s id).tokens = [] := by
  constructor
  · simp [decrement, last]
  · apply zero_has_no_tokens (decrement_valid h id held)
    simp [decrement, last]

theorem only_final_decrement_grants_reclamation (s : State) (id recipient : Nat)
    (permit : (decrement s id).life = .reclaiming recipient) :
    s.count = 1 ∧ recipient = id := by
  by_cases last : s.count = 1
  · simp [decrement, last] at permit
    exact ⟨last, permit.symm⟩
  · simp [decrement, last] at permit

theorem reclamation_has_no_owners_or_pending_operations {limit : Nat} {s : State}
    (h : Valid limit s) (id : Nat) (permit : s.life = .reclaiming id) :
    s.tokens = [] := by
  apply zero_has_no_tokens h
  have life : s.count = 0 ∧ id < s.fresh := by simpa [permit] using h.life
  exact life.left

theorem freed_is_terminal {limit : Nat} {s t : State} (h : Valid limit s)
    (freed : s.life = .freed) (step : Step limit s t) : False := by
  cases step with
  | reserve owner owned active room => simp [freed] at active
  | publish id held =>
    have active := token_protects_allocation h ⟨id, .reserved⟩ held
    simp [freed] at active
  | retire id held =>
    have active := token_protects_allocation h ⟨id, .owner⟩ held
    simp [freed] at active
  | decrement id held active => simp [freed] at active
  | free id permit => simp [freed] at permit

theorem cannot_free_twice_or_resurrect {limit : Nat} {s t : State}
    (h : Valid limit s) (freed : s.life = .freed) (run : Runs limit s t) : t = s := by
  induction run with
  | refl => rfl
  | next run step ih =>
    cases ih
    exact False.elim (freed_is_terminal h freed step)

-- The original owner disappears before the clone is published. The reserved
-- token still protects the allocation, even with no completed owner remaining.
example :
    let pending := decrement (changeStage (reserve initial) 0 .retiring) 0
    pending.tokens = [⟨1, .reserved⟩] ∧ pending.count = 1 ∧ pending.life = .active := by
  decide

-- Two non-atomic increments can both read 1 and write 2 while creating two
-- pending clones. Such a lost update violates accounting; it is not a Step.
example : ¬ Valid 3
    ⟨[⟨0, .owner⟩, ⟨1, .reserved⟩, ⟨2, .reserved⟩], 2, 3, .active⟩ := by
  intro h
  have accounting := h.accounting
  simp at accounting

-- The word effect of a strong compare-exchange, abstracted at its atomic point.
def casWord (current expected desired : Nat) : Nat :=
  if current = expected then desired else current

def reserveAttempt (limit : Nat) (s : State) (observed : Nat) : State :=
  if s.count = observed ∧ observed < limit then reserve s else s

def decrementAttempt (s : State) (id observed : Nat) : State :=
  if s.count = observed ∧ observed > 0 then decrement s id else s

theorem reserve_attempt_word_effect {limit : Nat} {s : State}
    (observed : Nat) (wordBound : observed ≤ limit) :
    (reserveAttempt limit s observed).count =
      casWord s.count observed (if observed = limit then observed else observed + 1) := by
  by_cases same : s.count = observed
  · by_cases room : observed < limit
    · have notFull : observed ≠ limit := by omega
      simp [reserveAttempt, casWord, same, room, reserve, notFull]
    · have full : observed = limit := by omega
      simp [reserveAttempt, casWord, same, full]
  · simp [reserveAttempt, casWord, same]

theorem reserve_attempt_is_step_or_stutter {limit : Nat} {s : State}
    (h : Valid limit s) (owner observed : Nat) (held : ⟨owner, .owner⟩ ∈ s.tokens) :
    reserveAttempt limit s observed = s ∨ Step limit s (reserveAttempt limit s observed) := by
  by_cases success : s.count = observed ∧ observed < limit
  · right
    simp only [reserveAttempt, success]
    exact Step.reserve s owner held (token_protects_allocation h ⟨owner, .owner⟩ held)
      (by omega)
  · left
    simp [reserveAttempt, success]

theorem decrement_attempt_word_effect {s : State}
    (id observed : Nat) :
    (decrementAttempt s id observed).count =
      casWord s.count observed (if observed = 0 then 0 else observed - 1) := by
  by_cases same : s.count = observed
  · by_cases zero : observed = 0
    · simp [decrementAttempt, casWord, same, zero]
    · have positive : observed > 0 := by omega
      simp [decrementAttempt, casWord, same, zero, positive, decrement]
  · simp [decrementAttempt, casWord, same]

theorem decrement_attempt_is_step_or_stutter {limit : Nat} {s : State}
    (h : Valid limit s) (id observed : Nat) (held : ⟨id, .retiring⟩ ∈ s.tokens) :
    decrementAttempt s id observed = s ∨ Step limit s (decrementAttempt s id observed) := by
  by_cases success : s.count = observed ∧ observed > 0
  · right
    simp only [decrementAttempt, success]
    exact Step.decrement s id held (token_protects_allocation h ⟨id, .retiring⟩ held)
  · left
    simp [decrementAttempt, success]

end Evergreen.SharedOwnership
