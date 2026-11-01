import Charter.Proofs.Ledger

/-!
# Turns and events are limited

A game has at most `maxTurns` turns and `maxEvents` events. `TurnInv` says where a game is in its
order of turns. `EventInv` counts events against turns and the actions used this turn.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

theorem valid_rounds (hG : G.Valid) : 1 ≤ G.rounds := by
  have hG := valid_shape hG
  simp only [GameDef.shapeChecks, Bool.and_eq_true, decide_eq_true_eq] at hG
  omega

theorem valid_target (hG : G.Valid) : 1 ≤ G.targetPoints := by
  have hG := valid_shape hG
  simp only [GameDef.shapeChecks, Bool.and_eq_true, decide_eq_true_eq] at hG
  omega

/-! ## What `startNextTurn` does, stage by stage -/

section stages
variable {s : State G} {roll : Nat}

theorem startNextTurn_setupTurn {i : Nat} (h : nextStage s = .setupTurn i) :
    (startNextTurn s roll).phase = s.phase ∧ (startNextTurn s roll).round = s.round := by
  unfold startNextTurn; rw [h]; exact ⟨rfl, rfl⟩

theorem startNextTurn_firstRound (h : nextStage s = .firstRound) :
    (startNextTurn s roll).phase = .actions ∧ (startNextTurn s roll).round = s.round ∧
      (startNextTurn s roll).turnIndex = 0 := by
  unfold startNextTurn; rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem startNextTurn_sameRound {i : Nat} (h : nextStage s = .sameRound i) :
    (startNextTurn s roll).phase = .actions ∧ (startNextTurn s roll).round = s.round ∧
      (startNextTurn s roll).turnIndex = i := by
  unfold startNextTurn; rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem startNextTurn_newRound (h : nextStage s = .newRound) :
    (startNextTurn s roll).phase = .actions ∧ (startNextTurn s roll).round = s.round + 1 ∧
      (startNextTurn s roll).turnIndex = 0 := by
  unfold startNextTurn; rw [h]; exact ⟨rfl, rfl, rfl⟩

theorem startNextTurn_gameOver (h : nextStage s = .gameOver) :
    (startNextTurn s roll).phase = .ended := by
  unfold startNextTurn; rw [h]

end stages

/-! ## Where a game is in its turns -/

/-- How many turns have been taken, by phase. `n` is the number of seats. -/
structure TurnInv (s : State G) : Prop where
  setup : s.phase = .setup → s.round = 1 ∧ s.turnsTaken < 2 * s.turnOrder.length
  actions : s.phase = .actions →
    1 ≤ s.round ∧ s.round ≤ G.rounds ∧ s.turnIndex < s.turnOrder.length ∧
    s.turnsTaken = 2 * s.turnOrder.length + (s.round - 1) * s.turnOrder.length + s.turnIndex
  ended : s.phase = .ended → s.turnsTaken ≤ maxTurns G s.turnOrder.length

/-- Until the game ends, there are turns left. -/
theorem TurnInv.lt_max {s : State G} (ht : TurnInv s) (he : s.phase ≠ .ended) :
    s.turnsTaken < maxTurns G s.turnOrder.length := by
  unfold maxTurns
  cases hp : s.phase with
  | ended => exact absurd hp he
  | setup =>
    have := (ht.setup hp).2
    omega
  | actions =>
    obtain ⟨h1, h2, h3, h4⟩ := ht.actions hp
    have hm : s.round * s.turnOrder.length ≤ G.rounds * s.turnOrder.length :=
      Nat.mul_le_mul_right _ h2
    obtain ⟨r, hr⟩ : ∃ r, s.round = r + 1 := ⟨s.round - 1, by omega⟩
    rw [hr] at h4 hm
    simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul] at h4 hm
    omega

theorem TurnInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64)
    (nonces : List UInt64) (h1 : minSeats ≤ seats) :
    TurnInv (initialState G seats serverSeed nonces) := by
  have : 2 ≤ seats := h1
  refine ⟨fun _ => ⟨rfl, ?_⟩, fun h => (by cases h), fun h => (by cases h)⟩
  simp [initialState]
  omega

/-- Which stage comes next, by phase. -/
theorem nextStage_cases {s : State G} (he : s.phase ≠ .ended) :
    (s.phase = .setup ∧
      ((∃ i, nextStage s = .setupTurn i ∧ s.turnsTaken + 1 < 2 * s.turnOrder.length) ∨
       (nextStage s = .firstRound ∧ 2 * s.turnOrder.length ≤ s.turnsTaken + 1))) ∨
    (s.phase = .actions ∧
      ((s.turnIndex + 1 ≠ s.turnOrder.length ∧ nextStage s = .sameRound (s.turnIndex + 1)) ∨
       (s.turnIndex + 1 = s.turnOrder.length ∧ s.round < G.rounds ∧ nextStage s = .newRound) ∨
       (s.turnIndex + 1 = s.turnOrder.length ∧ G.rounds ≤ s.round ∧ nextStage s = .gameOver))) := by
  cases hp : s.phase with
  | ended => exact absurd hp he
  | setup =>
    left
    refine ⟨rfl, ?_⟩
    have hs : nextStage s = setupStage s.turnOrder.length (s.turnsTaken + 1) := by
      unfold nextStage; rw [hp]
    rw [hs]
    unfold setupStage
    split
    · exact Or.inl ⟨_, rfl, by omega⟩
    · split
      · exact Or.inl ⟨_, rfl, by assumption⟩
      · exact Or.inr ⟨rfl, by omega⟩
  | actions =>
    right
    refine ⟨rfl, ?_⟩
    have hl : s.isLastTurn = decide (s.turnIndex + 1 = s.turnOrder.length) := by
      simp only [State.isLastTurn, hp]
      by_cases h : s.turnIndex + 1 = s.turnOrder.length <;> simp [h]
    have hs : nextStage s =
        if s.isLastTurn then (if G.rounds ≤ s.round then .gameOver else .newRound)
        else .sameRound (s.turnIndex + 1) := by
      unfold nextStage; rw [hp]
    rw [hs, hl]
    by_cases h1 : s.turnIndex + 1 = s.turnOrder.length
    · by_cases h2 : G.rounds ≤ s.round
      · exact Or.inr (Or.inr ⟨h1, h2, by simp [h1, h2]⟩)
      · exact Or.inr (Or.inl ⟨h1, by omega, by simp [h1, h2]⟩)
    · exact Or.inl ⟨h1, by simp [h1]⟩

/-- Ending a turn moves a game one step along its order of turns. -/
theorem TurnInv.startNextTurn {s : State G} (hG : G.Valid) (ht : TurnInv s) (he : s.phase ≠ .ended)
    (roll : Nat) : TurnInv (startNextTurn s roll) := by
  have hr1 := valid_rounds hG
  have hlt := ht.lt_max he
  have hT : (Engine.startNextTurn s roll).turnOrder = s.turnOrder := startNextTurn_turnOrder _ _
  have hK : (Engine.startNextTurn s roll).turnsTaken = s.turnsTaken + 1 :=
    startNextTurn_turnsTaken _ _
  rcases nextStage_cases he with ⟨hp, ⟨i, hs, hle⟩ | ⟨hs, hge⟩⟩ | ⟨hp, ⟨hne, hs⟩ | ⟨hl, hr, hs⟩ | ⟨_, _, hs⟩⟩
  · obtain ⟨h1, h2⟩ := startNextTurn_setupTurn (roll := roll) hs
    have hs1 := ht.setup hp
    refine ⟨fun _ => ⟨?_, ?_⟩, fun h => ?_, fun h => ?_⟩
    · rw [h2]; exact hs1.1
    · rw [hT, hK]; exact hle
    · rw [h1, hp] at h; cases h
    · rw [h1, hp] at h; cases h
  · obtain ⟨h1, h2, h3⟩ := startNextTurn_firstRound (roll := roll) hs
    have hs1 := ht.setup hp
    have hround : (Engine.startNextTurn s roll).round = 1 := h2.trans hs1.1
    have hpos : 0 < s.turnOrder.length := by omega
    refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_⟩
    · rw [h1] at h; cases h
    · rw [hT, hK, h3, hround]
      refine ⟨by omega, hr1, hpos, ?_⟩
      simp only [Nat.sub_self, Nat.zero_mul]
      omega
    · rw [h1] at h; cases h
  · obtain ⟨h1, h2, h3⟩ := startNextTurn_sameRound (roll := roll) hs
    obtain ⟨a1, a2, a3, a4⟩ := ht.actions hp
    refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_⟩
    · rw [h1] at h; cases h
    · rw [hT, hK, h2, h3]
      exact ⟨a1, a2, by omega, by omega⟩
    · rw [h1] at h; cases h
  · obtain ⟨h1, h2, h3⟩ := startNextTurn_newRound (roll := roll) hs
    obtain ⟨a1, a2, a3, a4⟩ := ht.actions hp
    refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_⟩
    · rw [h1] at h; cases h
    · rw [hT, hK, h2, h3]
      refine ⟨by omega, by omega, by omega, ?_⟩
      obtain ⟨r, hr'⟩ : ∃ r, s.round = r + 1 := ⟨s.round - 1, by omega⟩
      rw [hr'] at a4 ⊢
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul] at a4 ⊢
      omega
    · rw [h1] at h; cases h
  · have h1 := startNextTurn_gameOver (roll := roll) hs
    refine ⟨fun h => ?_, fun h => ?_, fun _ => ?_⟩
    · rw [h1] at h; cases h
    · rw [h1] at h; cases h
    · rw [hT, hK]; omega

/-- An event body and a possible early end keep the phase, or end the game. -/
theorem act_phase {s s1 s' : State G} {e : Event} (hb : bodyOf s e = .ok s1)
    (hf : finish (countAction s1 (seatOf e)) e = .ok s') :
    s'.phase = s.phase ∨ s'.phase = .ended := by
  have f := bodyOf_frame hb
  rcases finish_cases hf with rfl | ⟨w, h⟩
  · exact Or.inl f.phase
  · obtain ⟨_, _, rfl⟩ := endGame_ok h
    exact Or.inr rfl

theorem TurnInv.step {s s' : State G} {e : Event} (hG : G.Valid) (ht : TurnInv s)
    (h : Engine.step G s e = .ok s') : TurnInv s' := by
  have he := step_not_ended h
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨b, _, rfl⟩ := endTurnNow_ok h
    exact TurnInv.startNextTurn (s := { s with books := b, journal := _, pieces := _ }) hG
      ⟨ht.1, ht.2, ht.3⟩ he _
  · have f := act_frame hb hf
    have hlt := ht.lt_max he
    rcases act_phase hb hf with hp | hp
    · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rw [f.round, f.turnsTaken, f.turnOrder]
        exact ht.setup (hp.symm.trans h)
      · rw [f.round, f.turnsTaken, f.turnOrder, f.turnIndex]
        exact ht.actions (hp.symm.trans h)
      · exact absurd (hp.symm.trans h) he
    · refine ⟨fun h => ?_, fun h => ?_, fun _ => ?_⟩
      · rw [hp] at h; cases h
      · rw [hp] at h; cases h
      · rw [f.turnsTaken, f.turnOrder]; omega

/-- The bound on turns. -/
theorem TurnInv.turns_le {s : State G} (ht : TurnInv s) :
    s.turnsTaken ≤ maxTurns G s.turnOrder.length := by
  cases hp : s.phase with
  | ended => exact ht.ended hp
  | setup => exact Nat.le_of_lt (ht.lt_max (by simp [hp]))
  | actions => exact Nat.le_of_lt (ht.lt_max (by simp [hp]))

/-- When all the turns are used, the game has ended. -/
theorem TurnInv.ended_at_max {s : State G} (ht : TurnInv s)
    (h : s.turnsTaken = maxTurns G s.turnOrder.length) : s.phase = .ended := by
  cases hp : s.phase with
  | ended => rfl
  | setup =>
    have := ht.lt_max (by simp [hp])
    omega
  | actions =>
    have := ht.lt_max (by simp [hp])
    omega

/-! ## Counting events -/

theorem sum_count (T : List Seat) (hT : T.Nodup) {seat : Seat} (hs : seat ∈ T) (f : Seat → Nat) :
    (T.map fun q => if q = seat then f q + 1 else f q).sum = (T.map f).sum + 1 := by
  induction T with
  | nil => cases hs
  | cons a t ih =>
    obtain ⟨hat, hnd⟩ := List.nodup_cons.mp hT
    simp only [List.map_cons, List.sum_cons]
    by_cases ha : a = seat
    · subst ha
      have : (t.map fun q => if q = a then f q + 1 else f q) = t.map f := by
        apply List.map_congr_left
        intro q hq
        have : q ≠ a := fun e => hat (e ▸ hq)
        simp [this]
      rw [this]
      simp only [ite_true]
      omega
    · have hst : seat ∈ t := by
        cases List.mem_cons.mp hs with
        | inl h => exact absurd h.symm ha
        | inr h => exact h
      rw [ih hnd hst]
      simp only [ha, ite_false]
      omega

theorem sum_le_mul (T : List Seat) (f : Seat → Nat) (c : Nat) (h : ∀ q ∈ T, f q ≤ c) :
    (T.map f).sum ≤ T.length * c := by
  induction T with
  | nil => simp
  | cons a t ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Events so far, against turns so far and the actions used this turn. -/
structure EventInv (s : State G) : Prop where
  actions_le : ∀ q ∈ s.turnOrder, s.actionsThisTurn q ≤ maxActionsPerTurn
  count : s.eventsApplied ≤ s.turnsTaken * (s.turnOrder.length * maxActionsPerTurn + 1) +
    (s.turnOrder.map s.actionsThisTurn).sum
  zero_at_max : s.turnsTaken = maxTurns G s.turnOrder.length →
    ∀ q ∈ s.turnOrder, s.actionsThisTurn q = 0

theorem EventInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    EventInv (initialState G seats serverSeed nonces) :=
  ⟨by simp [initialState], by simp [initialState], by simp [initialState]⟩

theorem EventInv.step {s s' : State G} {e : Event} (hev : EventInv s) (ht : TurnInv s)
    (hT : s.turnOrder.Nodup) (h : Engine.step G s e = .ok s') : EventInv s' := by
  have he := step_not_ended h
  have hlt := ht.lt_max he
  rcases step_view h with ⟨_, h⟩ | ⟨_, hc, s1, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    have hle := sum_le_mul s.turnOrder s.actionsThisTurn maxActionsPerTurn hev.actions_le
    have hcnt := hev.count
    refine ⟨?_, ?_, ?_⟩
    · simp [maxActionsPerTurn]
    · simp only [startNextTurn_eventsApplied, startNextTurn_turnsTaken, startNextTurn_turnOrder,
        startNextTurn_actionsThisTurn, Nat.add_mul, Nat.one_mul]
      simp only [List.map_const']
      have : (List.replicate s.turnOrder.length 0).sum = 0 := by simp
      rw [this]
      omega
    · simp
  · have f := act_frame hb hf
    obtain ⟨hs, hlim⟩ := canAct_mem hc
    refine ⟨?_, ?_, ?_⟩
    · rw [f.turnOrder, f.actionsThisTurn]
      intro q hq
      have := hev.actions_le q hq
      simp only
      split
      · subst_vars; omega
      · exact this
    · rw [f.turnOrder, f.actionsThisTurn, f.eventsApplied, f.turnsTaken,
        sum_count _ hT hs s.actionsThisTurn]
      have := hev.count
      omega
    · rw [f.turnOrder, f.turnsTaken]
      intro hm
      omega

/-- The bound on events. -/
theorem events_le {s : State G} (hev : EventInv s) (ht : TurnInv s) :
    s.eventsApplied ≤ maxEvents G s.turnOrder.length := by
  unfold maxEvents
  have hcnt := hev.count
  have hle := sum_le_mul s.turnOrder s.actionsThisTurn maxActionsPerTurn hev.actions_le
  have hmax := ht.turns_le
  by_cases hm : s.turnsTaken = maxTurns G s.turnOrder.length
  · have hz : (s.turnOrder.map s.actionsThisTurn).sum = 0 := by
      have := sum_le_mul s.turnOrder s.actionsThisTurn 0
        (fun q hq => Nat.le_of_eq (hev.zero_at_max hm q hq))
      simpa using this
    rw [hz, hm] at hcnt
    exact hcnt
  · have hstep : (s.turnsTaken + 1) * (s.turnOrder.length * maxActionsPerTurn + 1) ≤
        maxTurns G s.turnOrder.length * (s.turnOrder.length * maxActionsPerTurn + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hstep
    omega

end Charter.Proofs
