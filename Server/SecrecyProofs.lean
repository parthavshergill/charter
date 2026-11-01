import Server.Secrecy

/-!
# Proofs about `observe`

The statements a reader should read are in `Server/SecrecyPromise.lean`.
-/

namespace CharterServer.SecrecyProofs

open Charter CharterServer

variable {G : GameDef}

/-- Whether the viewer sees an entry's amount does not depend on the amount. -/
theorem seesAmount_amount (sec : Secrecy) (v : Option Seat) (e : Entry) (n : Nat) :
    sec.seesAmount v { e with amount := n } = sec.seesAmount v e := rfl

/-- How `observe` shows one journal entry. -/
abbrev shown (sec : Secrecy) (v : Option Seat) (e : Entry) : Entry := sec.shownEntry v e

/-- What `observe` writes in the journal: the same list as mapping `shown` over it. -/
theorem journal_eq_map (sec : Secrecy) (v : Option Seat) (l : List Entry) :
    (if sec.hidden.isEmpty then l else l.map (shown sec v)) = l.map (shown sec v) := by
  split
  · rename_i h
    have hnil : sec.hidden = [] := by simpa [List.isEmpty_iff] using h
    have hs : ∀ e, shown sec v e = e := fun e => by simp [shown, Secrecy.shownEntry, Secrecy.seesAmount, hnil]
    rw [show shown sec v = id from funext hs, List.map_id]
  · rfl

/-- `observe` on a running game, written out. -/
theorem observe_running (sec : Secrecy) (v : Option Seat) (s : State G) (h : s.phase ≠ .ended) :
    observe sec v s =
      { s with
        books := fun a r => if sec.seesHolding v a r then s.books a r else 0
        journal := s.journal.map (shown sec v)
        declared := fun p r => if sec.seesDeclared v p then s.declared p r else 0
        lastRoll := if sec.seesRoll v s then s.lastRoll else none
        seed := 0 } := by
  simp only [observe, h, ↓reduceIte]
  rw [journal_eq_map]

theorem observe_phase (sec : Secrecy) (v : Option Seat) (s : State G) :
    (observe sec v s).phase = s.phase := by
  unfold observe; split <;> rfl

/-- Two entries look the same, exactly when they are related as `HiddenDifference` asks. -/
theorem shown_eq_iff (sec : Secrecy) (v : Option Seat) (x y : Entry) :
    shown sec v x = shown sec v y ↔
      ({ x with amount := 0 } = { y with amount := 0 } ∧ (sec.seesAmount v x → x = y)) := by
  have hz : ∀ e : Entry, sec.seesAmount v { e with amount := 0 } = sec.seesAmount v e :=
    fun e => seesAmount_amount sec v e 0
  constructor
  · intro h
    by_cases hx : sec.seesAmount v x <;> by_cases hy : sec.seesAmount v y <;>
      simp only [shown, Secrecy.shownEntry, hx, hy, ↓reduceIte, Bool.false_eq_true] at h
    · exact ⟨by rw [h], fun _ => h⟩
    · exfalso
      have := congrArg (sec.seesAmount v) h
      rw [hz] at this
      simp_all
    · exfalso
      have := congrArg (sec.seesAmount v) h
      rw [hz] at this
      simp_all
    · exact ⟨h, fun hx' => absurd hx' (by simp [hx])⟩
  · rintro ⟨h0, h1⟩
    by_cases hx : sec.seesAmount v x
    · have hxy := h1 hx
      subst hxy
      rfl
    · have hy : sec.seesAmount v y = false := by
        have := congrArg (sec.seesAmount v) h0
        rw [hz, hz] at this
        simp_all
      simp [shown, Secrecy.shownEntry, hx, hy, h0]

theorem map_eq_iff_zip {α β : Type} (f : α → β) (l₁ l₂ : List α) :
    l₁.map f = l₂.map f ↔ l₁.length = l₂.length ∧ ∀ xy ∈ l₁.zip l₂, f xy.1 = f xy.2 := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp
  | cons a t ih =>
    cases l₂ with
    | nil => simp
    | cons b u => simp [ih, and_left_comm]

/-- Two states agree in what decides whether a roll is seen, when their other fields agree. -/
theorem currentSeat_of_restSame {s₁ s₂ : State G}
    (h : { s₁ with books := s₂.books, journal := s₂.journal, declared := s₂.declared,
                   lastRoll := s₂.lastRoll, seed := s₂.seed } = s₂) :
    s₁.currentSeat = s₂.currentSeat := by
  rw [← h]; rfl

theorem phase_of_restSame {s₁ s₂ : State G}
    (h : { s₁ with books := s₂.books, journal := s₂.journal, declared := s₂.declared,
                   lastRoll := s₂.lastRoll, seed := s₂.seed } = s₂) :
    s₁.phase = s₂.phase := by
  rw [← h]

/-- The main result: while a game runs, two states look the same to a viewer exactly when they differ
only in what is hidden from it. -/
theorem observe_eq_iff (sec : Secrecy) (v : Option Seat) (s₁ s₂ : State G)
    (h : s₁.phase ≠ .ended) :
    observe sec v s₁ = observe sec v s₂ ↔ HiddenDifference sec v s₁ s₂ := by
  constructor
  · intro heq
    have h₂ : s₂.phase ≠ .ended := by
      have := congrArg State.phase heq
      rw [observe_phase, observe_phase] at this
      rw [← this]; exact h
    rw [observe_running sec v s₁ h, observe_running sec v s₂ h₂] at heq
    have hcur : s₁.currentSeat = s₂.currentSeat := by
      have h1 := congrArg State.turnOrder heq
      have h2 := congrArg State.turnIndex heq
      simp only [] at h1 h2
      simp [State.currentSeat, h1, h2]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · let back : State G → State G := fun t =>
        { t with books := s₂.books, journal := s₂.journal, declared := s₂.declared, lastRoll := s₂.lastRoll, seed := s₂.seed }
      have hb := congrArg back heq
      exact hb
    · intro a r hs
      have := congrFun (congrFun (congrArg State.books heq) a) r
      simpa [State.balance, hs] using this
    · have := congrArg State.journal heq
      simp only [] at this
      rw [map_eq_iff_zip] at this
      exact ⟨this.1, fun xy hxy => (shown_eq_iff sec v xy.1 xy.2).1 (this.2 xy hxy)⟩
    · intro p r hs
      have := congrFun (congrFun (congrArg State.declared heq) p) r
      simpa [hs] using this
    · intro hs
      have := congrArg State.lastRoll heq
      have hs₂ : sec.seesRoll v s₂ = true := by
        simpa [Secrecy.seesRoll, hcur] using hs
      simpa [hs, hs₂] using this
  · intro hd
    have h₂ : s₂.phase ≠ .ended := by rw [← phase_of_restSame hd.restSame]; exact h
    have hcur := currentSeat_of_restSame hd.restSame
    rw [observe_running sec v s₁ h, observe_running sec v s₂ h₂]
    have hb : (fun a r => if sec.seesHolding v a r then s₁.books a r else 0) =
        (fun a r => if sec.seesHolding v a r then s₂.books a r else 0) := by
      funext a r
      by_cases hs : sec.seesHolding v a r
      · simpa [hs, State.balance] using hd.holdings a r hs
      · simp [hs]
    have hj : s₁.journal.map (shown sec v) = s₂.journal.map (shown sec v) := by
      rw [map_eq_iff_zip]
      exact ⟨hd.journal.1, fun xy hxy => (shown_eq_iff sec v xy.1 xy.2).2 (hd.journal.2 xy hxy)⟩
    have hdecl : (fun p r => if sec.seesDeclared v p then s₁.declared p r else 0) =
        (fun p r => if sec.seesDeclared v p then s₂.declared p r else 0) := by
      funext p r
      by_cases hs : sec.seesDeclared v p
      · simpa [hs] using hd.declared p r hs
      · simp [hs]
    have hroll : (if sec.seesRoll v s₁ then s₁.lastRoll else none) =
        (if sec.seesRoll v s₂ then s₂.lastRoll else none) := by
      have hsr : sec.seesRoll v s₂ = sec.seesRoll v s₁ := by simp [Secrecy.seesRoll, hcur]
      rw [hsr]
      by_cases hs : sec.seesRoll v s₁
      · simp [hs, hd.roll hs]
      · simp [hs]
    rw [hb, hj, hdecl, hroll]
    let mask : State G → State G := fun t =>
      { t with
        books := fun a r => if sec.seesHolding v a r then s₂.books a r else 0
        journal := s₂.journal.map (shown sec v)
        declared := fun p r => if sec.seesDeclared v p then s₂.declared p r else 0
        lastRoll := if sec.seesRoll v s₂ then s₂.lastRoll else none
        seed := 0 }
    have hm := congrArg mask hd.restSame
    exact hm

/-- After the end, nothing is hidden. -/
theorem observe_ended (sec : Secrecy) (v : Option Seat) (s : State G) (h : s.phase = .ended) :
    observe sec v s = s := by
  simp [observe, h]

/-- A game that marks nothing hides only the seed. -/
theorem observe_unmarked (v : Option Seat) (s : State G) (h : s.phase ≠ .ended) :
    observe {} v s = { s with seed := 0 } := by
  rw [observe_running _ v s h]
  have hs : ∀ e, shown {} v e = e := fun e => by simp [shown, Secrecy.shownEntry, Secrecy.seesAmount]
  rw [show shown {} v = id from funext hs, List.map_id]
  simp [Secrecy.seesHolding, Secrecy.seesDeclared, Secrecy.seesRoll]

end CharterServer.SecrecyProofs
