import Charter.Proofs.Turns

/-!
# What every other event does

No game that is still running has a seat at the target, because every event that can change points
looks for a winner at once. So an offer or a cancel can never end the game by surprise.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## New entries -/

theorem newEntries_of {s s' : State G} {es : List Entry} (h : s'.journal = s.journal ++ es) :
    newEntries s s' = es := by
  simp [newEntries, h]

theorem newEntries_nil {s s' : State G} (h : s'.journal = s.journal) : newEntries s s' = [] := by
  simp [newEntries, h]

/-! ## Points and the target -/

theorem pointsOf_congr {s s' : State G} (hp : s'.pieces = s.pieces) (hl : s'.laws = s.laws)
    (q : Seat) : s'.pointsOf q = s.pointsOf q := by
  simp only [State.pointsOf, State.rules, hp, hl]

theorem seatsAtTarget_congr {s s' : State G} (hT : s'.turnOrder = s.turnOrder)
    (hp : s'.pieces = s.pieces) (hl : s'.laws = s.laws) :
    seatsAtTarget s' = seatsAtTarget s := by
  unfold seatsAtTarget
  rw [hT]
  apply List.filter_congr
  intro q _
  rw [pointsOf_congr hp hl]

theorem checkWin_of_nil {s : State G} (h : seatsAtTarget s = []) : checkWin s = .ok s := by
  unfold checkWin
  rw [h]
  rfl

/-- While a game runs, no seat is at the target. -/
def NoPending (s : State G) : Prop := s.phase ≠ .ended → seatsAtTarget s = []

theorem NoPending.start {G : GameDef} (hG : G.Valid) (seats : Nat) (serverSeed : UInt64)
    (nonces : List UInt64) : NoPending (initialState G seats serverSeed nonces) := by
  intro _
  have := valid_target hG
  unfold seatsAtTarget
  apply List.filter_eq_nil_iff.mpr
  intro q _
  simp [State.pointsOf, initialState]
  omega

/-! ## What bodies leave alone -/

theorem decideLaw_fields (s : State G) (id : Nat) (L : Law) :
    (decideLaw s id L).pieces = s.pieces ∧ (decideLaw s id L).journal = s.journal ∧
    (decideLaw s id L).books = s.books ∧ (decideLaw s id L).deals = s.deals := by
  unfold decideLaw
  simp only
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Only a place move changes the pieces. -/
theorem body_pieces {s s1 : State G} {e : Event} (hne : ∀ p k loc, e ≠ .move p (.place k loc))
    (h : bodyOf s e = .ok s1) : s1.pieces = s.pieces := by
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    cases m with
    | endTurn => cases h
    | place k loc => exact absurd rfl (hne p k loc)
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
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> rfl
  | vote seat i y =>
    obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · exact (decideLaw_fields _ _ _).1
    · rfl
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h
      rfl
    · rfl
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    rfl

/-- Only a vote changes the laws. -/
theorem body_laws {s s1 : State G} {e : Event} (hne : ∀ a b c, e ≠ .vote a b c)
    (h : bodyOf s e = .ok s1) : s1.laws = s.laws := by
  cases e with
  | forceEndTurn => cases h
  | vote a b c => exact absurd rfl (hne a b c)
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
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> rfl
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h
      rfl
    · rfl
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    rfl

theorem NoPending.step {s s' : State G} {e : Event} (hn : NoPending s)
    (h : Engine.step G s e = .ok s') : NoPending s' := by
  have he := step_not_ended h
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    intro _
    rw [seatsAtTarget_congr (s := s) (by simp) (by simp) (by simp)]
    exact hn he
  · have f := bodyOf_frame hb
    intro hne
    cases e with
    | forceEndTurn => cases hb
    | move p m =>
      rcases checkWin_ok hf with ⟨rfl, hnil⟩ | ⟨w, hw⟩
      · exact hnil
      · obtain ⟨_, _, rfl⟩ := endGame_ok hw
        exact absurd rfl hne
    | vote a b c =>
      rcases checkWin_ok hf with ⟨rfl, hnil⟩ | ⟨w, hw⟩
      · exact hnil
      · obtain ⟨_, _, rfl⟩ := endGame_ok hw
        exact absurd rfl hne
    | propose a b =>
      obtain rfl : s' = countAction s1 a := (Except.ok.inj hf).symm
      exact (seatsAtTarget_congr (s := s) f.turnOrder (body_pieces (by simp) hb)
        (body_laws (by simp) hb)).trans (hn he)
    | sign a b =>
      obtain rfl : s' = countAction s1 a := (Except.ok.inj hf).symm
      exact (seatsAtTarget_congr (s := s) f.turnOrder (body_pieces (by simp) hb)
        (body_laws (by simp) hb)).trans (hn he)
    | exit a b =>
      obtain rfl : s' = countAction s1 a := (Except.ok.inj hf).symm
      exact (seatsAtTarget_congr (s := s) f.turnOrder (body_pieces (by simp) hb)
        (body_laws (by simp) hb)).trans (hn he)

/-! ## One event at a time -/

theorem step_act {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hne : ¬ EndsTurn s e) :
    canAct s (seatOf e) = true ∧ ∃ s1, bodyOf s e = .ok s1 ∧
      finish (countAction s1 (seatOf e)) e = .ok s' := by
  rcases step_view h with ⟨h1, _⟩ | ⟨_, hc, s1, hb, hf⟩
  · exact absurd h1 hne
  · exact ⟨hc, s1, hb, hf⟩

/-- A move that changes neither the pieces nor the laws leaves the state as counted. -/
theorem move_no_win {s s1 s' : State G} {p : Seat} (hn : NoPending s)
    (he : s.phase ≠ .ended) (hT : s1.turnOrder = s.turnOrder) (hp : s1.pieces = s.pieces)
    (hl : s1.laws = s.laws) (hf : checkWin (countAction s1 p) = .ok s') :
    s' = countAction s1 p := by
  have hnil : seatsAtTarget (countAction s1 p) = [] :=
    (seatsAtTarget_congr (s := s) hT hp hl).trans (hn he)
  rw [checkWin_of_nil hnil] at hf
  exact (Except.ok.inj hf).symm

theorem refundEntries_congr {s s' : State G} (hb : s'.books = s.books) (d : ActiveDeal) :
    s'.refundEntries d = s.refundEntries d := by
  simp only [State.refundEntries, State.balance, hb]
  rfl

theorem all_contains_iff (signers signed : List Seat) (seat : Seat) :
    signers.all (signed ++ [seat]).contains = true ↔ ∀ j ∈ signers, j ∈ signed ∨ j = seat := by
  simp [List.all_eq_true]

/-- `every_other_event_is_exact`, in terms of `NoPending`. -/
theorem step_is_exact {s s' : State G} {e : Event} (hn : NoPending s)
    (h : Engine.step G s e = .ok s') :
    (∀ seat dealId, e = .exit seat dealId → newEntries s s' = []) ∧
    (∀ p to give get, e = .move p (.offer to give get) → newEntries s s' = []) ∧
    (∀ p id, e = .move p (.cancel id) → newEntries s s' = []) ∧
    (∀ seat d, e = .propose seat (.deal d) → newEntries s s' = []) ∧
    (∀ seat L, e = .propose seat (.law L) → newEntries s s' = lawFeeEntries G seat) ∧
    (∀ seat id, e = .sign seat id → ∃ p d,
      s.openProposal? id = some p ∧ p.body = .deal d ∧
      ((∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
        newEntries s s' = depositEntries s.dealsStarted d) ∧
      ((¬ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) → newEntries s s' = [])) ∧
    (∀ seat id yes, e = .vote seat id yes →
      (s'.phase = .ended → newEntries s s' = s.deals.flatMap s.refundEntries) ∧
      (s'.phase ≠ .ended → newEntries s s' = [])) ∧
    (∀ p id, e = .move p (.accept id) → ∃ o, s.offers.find? (·.id == id) = some o) ∧
    (∀ p, e = .move p .endTurn → EndsTurn s e) ∧
    ((∀ p k loc, e ≠ .move p (.place k loc)) → s'.pieces = s.pieces) ∧
    (¬ EndsTurn s e →
      s'.turnsTaken = s.turnsTaken ∧ s'.turnIndex = s.turnIndex ∧ s'.round = s.round ∧
      s'.rollsMade = s.rollsMade) := by
  have he := step_not_ended h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- an exit
    rintro seat id rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    obtain rfl : s' = countAction s1 seat := (Except.ok.inj hf).symm
    obtain ⟨_, _, rfl⟩ := exitBody_ok hb
    exact newEntries_nil rfl
  · -- an offer
    rintro p to give get rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hf' : checkWin (countAction s1 p) = .ok s' := hf
    obtain ⟨_, _, hs1⟩ := offerBody_ok hb
    have hx := move_no_win (s := s) hn he (by subst hs1; rfl) (by subst hs1; rfl)
      (by subst hs1; rfl) hf'
    subst hx
    exact newEntries_nil (by subst hs1; rfl)
  · -- a cancelled offer
    rintro p id rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hf' : checkWin (countAction s1 p) = .ok s' := hf
    obtain ⟨_, _, hs1⟩ := cancelBody_ok hb
    have hx := move_no_win (s := s) hn he (by subst hs1; rfl) (by subst hs1; rfl)
      (by subst hs1; rfl) hf'
    subst hx
    exact newEntries_nil (by subst hs1; rfl)
  · -- a proposed deal
    rintro seat d rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    obtain rfl : s' = countAction s1 seat := (Except.ok.inj hf).symm
    have hb' : proposeBody s seat (.deal d) = .ok s1 := hb
    obtain ⟨_, _, ⟨_, hc, _⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok hb'
    · cases hc
    · exact newEntries_nil rfl
  · -- a proposed law
    rintro seat L rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    obtain rfl : s' = countAction s1 seat := (Except.ok.inj hf).symm
    have hb' : proposeBody s seat (.law L) = .ok s1 := hb
    obtain ⟨_, _, ⟨_, _, _, _, _, rfl⟩ | ⟨_, hc, _⟩⟩ := proposeBody_ok hb'
    · exact newEntries_of rfl
    · cases hc
  · -- a signature
    rintro seat id rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    obtain rfl : s' = countAction s1 seat := (Except.ok.inj hf).symm
    have hb' : signBody s seat id = .ok s1 := hb
    obtain ⟨_, p, d, hp, hd, _, _, ⟨hall, hst⟩ | ⟨hall, rfl⟩⟩ := signBody_ok hb'
    · refine ⟨p, d, hp, hd, fun _ => ?_, fun hnot => ?_⟩
      · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok hst
        exact newEntries_of rfl
      · exact absurd ((all_contains_iff _ _ _).mp hall) hnot
    · refine ⟨p, d, hp, hd, fun hyes => ?_, fun _ => newEntries_nil rfl⟩
      have := (all_contains_iff d.signers p.signed seat).mpr hyes
      rw [this] at hall
      cases hall
  · -- a vote
    rintro seat id yes rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hf' : checkWin (countAction s1 seat) = .ok s' := hf
    have f := bodyOf_frame hb
    have hfields : s1.journal = s.journal ∧ s1.books = s.books ∧ s1.deals = s.deals := by
      have hb' : voteBody s seat id yes = .ok s1 := hb
      obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok hb'
      · exact (decideLaw_fields _ _ _).2
      · exact ⟨rfl, rfl, rfl⟩
    obtain ⟨hj, hbk, hd⟩ := hfields
    rcases checkWin_ok hf' with ⟨rfl, _⟩ | ⟨w, hw⟩
    · refine ⟨fun hend => ?_, fun _ => newEntries_nil hj⟩
      have : s.phase = .ended := f.phase.symm.trans hend
      exact absurd this he
    · obtain ⟨_, _, rfl⟩ := endGame_ok hw
      refine ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
      apply newEntries_of
      have hfun : (countAction s1 seat).refundEntries = s.refundEntries :=
        funext (refundEntries_congr hbk)
      change s1.journal ++ s1.deals.flatMap (countAction s1 seat).refundEntries = _
      rw [hj, hd, hfun]
  · -- an accepted offer
    rintro p id rfl
    obtain ⟨_, s1, hb, _⟩ := step_act h (by simp [EndsTurn])
    have hb' : acceptBody s p id = .ok s1 := hb
    obtain ⟨_, o, ho, _⟩ := acceptBody_ok hb'
    exact ⟨o, ho⟩
  · -- ending the turn
    rintro p rfl
    rcases step_view h with ⟨h1, _⟩ | ⟨_, _, _, hb, _⟩
    · exact h1
    · cases hb
  · -- the pieces
    intro hne
    rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
    · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
      simp
    · have hp := body_pieces hne hb
      rcases finish_cases hf with rfl | ⟨w, hw⟩
      · exact hp
      · obtain ⟨_, _, rfl⟩ := endGame_ok hw
        exact hp
  · -- the turn and the dice
    intro hne
    obtain ⟨_, s1, hb, hf⟩ := step_act h hne
    have f := act_frame hb hf
    exact ⟨f.turnsTaken, f.turnIndex, f.round, f.rollsMade⟩

end Charter.Proofs
