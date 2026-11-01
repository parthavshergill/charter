import Charter.Proofs.Entries

/-!
# What events leave alone

An event body never changes who plays, the turn, the dice, the action counters or the winner.
A turn change never changes the seats, the pieces, the laws or the seed.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## Event bodies -/

/-- The fields no event body changes. -/
structure BodyFrame (s s1 : State G) : Prop where
  turnOrder : s1.turnOrder = s.turnOrder
  phase : s1.phase = s.phase
  round : s1.round = s.round
  turnIndex : s1.turnIndex = s.turnIndex
  turnsTaken : s1.turnsTaken = s.turnsTaken
  rollsMade : s1.rollsMade = s.rollsMade
  lastRoll : s1.lastRoll = s.lastRoll
  seed : s1.seed = s.seed
  seedCommitment : s1.seedCommitment = s.seedCommitment
  actionsThisTurn : s1.actionsThisTurn = s.actionsThisTurn
  eventsApplied : s1.eventsApplied = s.eventsApplied
  winner : s1.winner = s.winner

/-- Proves `BodyFrame` for a state written out with `{ s with ... }`. -/
macro "body_frame" : tactic => `(tactic| (constructor <;> rfl))

theorem decideLaw_frame (s : State G) (id : Nat) (L : Law) : BodyFrame s (decideLaw s id L) := by
  unfold decideLaw
  simp only
  split <;> body_frame

theorem startDeal_frame {s s1 : State G} {id : Nat} {d : Deal} (h : startDeal s id d = .ok s1) :
    BodyFrame s s1 := by
  obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h
  body_frame

theorem bodyOf_frame {s s1 : State G} {e : Event} (h : bodyOf s e = .ok s1) : BodyFrame s s1 := by
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    cases m with
    | endTurn => cases h
    | place k loc =>
      rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        body_frame
      · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
        body_frame
    | bankTrade a b =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok h
      obtain ⟨_, _, rfl⟩ := record_ok hr
      body_frame
    | offer t a b =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok h
      body_frame
    | accept i =>
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok h
      body_frame
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok h
      body_frame
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok h
      body_frame
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> body_frame
  | vote seat i y =>
    obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · exact decideLaw_frame _ _ _
    · body_frame
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · exact startDeal_frame h
    · body_frame
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    body_frame

/-- Only a declaration changes the declared numbers in an event body. -/
theorem bodyOf_declared {s s1 : State G} {e : Event} (h : bodyOf s e = .ok s1)
    (hne : ∀ p r n, e ≠ .move p (.declare r n)) : s1.declared = s.declared := by
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    cases m with
    | endTurn => cases h
    | place k loc =>
      rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        rfl
      · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
        rfl
    | bankTrade a b =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok h
      obtain ⟨_, _, rfl⟩ := record_ok hr
      rfl
    | offer t a b =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok h
      rfl
    | accept i =>
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok h
      rfl
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok h
      rfl
    | declare r n => exact absurd rfl (hne p r n)
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> rfl
  | vote seat i y =>
    obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · unfold decideLaw
      simp only
      split <;> rfl
    · rfl
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h
      rfl
    · rfl
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    rfl

/-! ## After the body -/

/-- `finish` either leaves the state alone or ends the game. -/
theorem finish_cases {s s' : State G} {e : Event} (h : finish s e = .ok s') :
    s' = s ∨ ∃ w, endGame s w = .ok s' := by
  cases e with
  | move p m => exact (checkWin_ok h).elim (fun x => Or.inl x.1) Or.inr
  | vote a b c => exact (checkWin_ok h).elim (fun x => Or.inl x.1) Or.inr
  | propose a b => exact Or.inl (by simpa [finish] using h.symm)
  | sign a b => exact Or.inl (by simpa [finish] using h.symm)
  | exit a b => exact Or.inl (by simpa [finish] using h.symm)
  | forceEndTurn => exact Or.inl (by simpa [finish] using h.symm)

/-- An accepted event that does not end the turn changes these fields only in this way. -/
structure ActFrame (s s' : State G) (seat : Seat) : Prop where
  turnOrder : s'.turnOrder = s.turnOrder
  round : s'.round = s.round
  turnIndex : s'.turnIndex = s.turnIndex
  turnsTaken : s'.turnsTaken = s.turnsTaken
  rollsMade : s'.rollsMade = s.rollsMade
  lastRoll : s'.lastRoll = s.lastRoll
  seed : s'.seed = s.seed
  seedCommitment : s'.seedCommitment = s.seedCommitment
  eventsApplied : s'.eventsApplied = s.eventsApplied + 1
  actionsThisTurn : s'.actionsThisTurn =
    fun q => if q = seat then s.actionsThisTurn q + 1 else s.actionsThisTurn q

theorem act_frame {s s1 s' : State G} {e : Event} (hb : bodyOf s e = .ok s1)
    (hf : finish (countAction s1 (seatOf e)) e = .ok s') : ActFrame s s' (seatOf e) := by
  have f := bodyOf_frame hb
  rcases finish_cases hf with rfl | ⟨w, h⟩
  · exact ⟨f.turnOrder, f.round, f.turnIndex, f.turnsTaken, f.rollsMade, f.lastRoll, f.seed,
      f.seedCommitment, by simp [countAction, f.eventsApplied], by simp [countAction, f.actionsThisTurn]⟩
  · obtain ⟨_, _, rfl⟩ := endGame_ok h
    exact ⟨f.turnOrder, f.round, f.turnIndex, f.turnsTaken, f.rollsMade, f.lastRoll, f.seed,
      f.seedCommitment, by simp [countAction, f.eventsApplied], by simp [countAction, f.actionsThisTurn]⟩

/-! ## The turn change -/

section startNextTurn
variable (s : State G) (roll : Nat)

@[simp] theorem startNextTurn_turnOrder : (startNextTurn s roll).turnOrder = s.turnOrder := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_books : (startNextTurn s roll).books = s.books := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_journal : (startNextTurn s roll).journal = s.journal := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_pieces : (startNextTurn s roll).pieces = s.pieces := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_laws : (startNextTurn s roll).laws = s.laws := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_seed : (startNextTurn s roll).seed = s.seed := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_seedCommitment :
    (startNextTurn s roll).seedCommitment = s.seedCommitment := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_turnsTaken :
    (startNextTurn s roll).turnsTaken = s.turnsTaken + 1 := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_eventsApplied :
    (startNextTurn s roll).eventsApplied = s.eventsApplied + 1 := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_actionsThisTurn :
    (startNextTurn s roll).actionsThisTurn = fun _ => 0 := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_offers : (startNextTurn s roll).offers = [] := by
  unfold startNextTurn; split <;> rfl

theorem startNextTurn_deals_sub {d : ActiveDeal} (h : d ∈ (startNextTurn s roll).deals) :
    d ∈ s.deals := by
  unfold startNextTurn at h
  split at h
  · exact h
  · exact h
  · exact h
  · exact (List.mem_filter.mp h).1
  · cases h

theorem startNextTurn_openProposals_sub {p : OpenProposal}
    (h : p ∈ (startNextTurn s roll).openProposals) : p ∈ s.openProposals := by
  unfold startNextTurn at h
  split at h
  · exact h
  · exact (List.mem_filter.mp h).1
  · exact (List.mem_filter.mp h).1
  · exact (List.mem_filter.mp h).1
  · cases h

/-- A turn change rolls once or not at all. -/
theorem startNextTurn_rolls :
    ((startNextTurn s roll).rollsMade = s.rollsMade ∧
      (startNextTurn s roll).lastRoll = s.lastRoll) ∨
    ((startNextTurn s roll).rollsMade = s.rollsMade + 1 ∧
      (startNextTurn s roll).lastRoll = some roll) := by
  unfold startNextTurn
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

end startNextTurn

/-! ## Whole steps -/

theorem step_turnOrder {s s' : State G} {e : Event} (h : step G s e = .ok s') :
    s'.turnOrder = s.turnOrder := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    simp
  · exact (act_frame hb hf).turnOrder

theorem step_seed {s s' : State G} {e : Event} (h : step G s e = .ok s') : s'.seed = s.seed := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    simp
  · exact (act_frame hb hf).seed

theorem step_seedCommitment {s s' : State G} {e : Event} (h : step G s e = .ok s') :
    s'.seedCommitment = s.seedCommitment := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    simp
  · exact (act_frame hb hf).seedCommitment

/-- A step rolls the dice at most once, and a roll depends only on the seed and the roll count. -/
theorem step_rolls {s s' : State G} {e : Event} (h : step G s e = .ok s') :
    (s'.rollsMade = s.rollsMade ∧ s'.lastRoll = s.lastRoll) ∨
    (s'.rollsMade = s.rollsMade + 1 ∧ s'.lastRoll = some (rollAt G s.seed s.rollsMade)) := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    exact startNextTurn_rolls _ _
  · have f := act_frame hb hf
    exact Or.inl ⟨f.rollsMade, f.lastRoll⟩

end Charter.Proofs
