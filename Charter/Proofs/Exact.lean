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

theorem builtPointsOf_congr {s s' : State G} (hp : s'.pieces = s.pieces) (hl : s'.laws = s.laws)
    (q : Seat) : s'.builtPointsOf q = s.builtPointsOf q := by
  simp only [State.builtPointsOf, State.rules, hp, hl]

theorem pointsOf_congr {s s' : State G} (hp : s'.pieces = s.pieces) (hl : s'.laws = s.laws)
    (hb : s'.books = s.books) (q : Seat) : s'.pointsOf q = s.pointsOf q := by
  simp only [State.pointsOf, State.builtPointsOf, State.tokenPointsOf, State.balance, State.rules, hp, hl, hb]

theorem seatsAtTarget_congr {s s' : State G} (hT : s'.turnOrder = s.turnOrder)
    (hp : s'.pieces = s.pieces) (hl : s'.laws = s.laws) (hb : s'.books = s.books) :
    seatsAtTarget s' = seatsAtTarget s := by
  unfold seatsAtTarget
  rw [hT]
  apply List.filter_congr
  intro q _
  rw [pointsOf_congr hp hl hb]

theorem checkWin_of_nil {s : State G} (h : seatsAtTarget s = []) : checkWin s = .ok s := by
  unfold checkWin
  rw [h]
  rfl

/-! ## What bodies leave alone -/

theorem decideLaw_deals (s : State G) (id : Nat) (L : Law) : (decideLaw s id L).deals = s.deals := by
  unfold decideLaw
  simp only
  split <;> rfl

/-- A vote's body: it passes one law, and does what that law's `now` clauses say, or it moves nothing. -/
theorem vote_view {s s1 : State G} {seat id : Nat} {yes : Bool} (hb : voteBody s seat id yes = .ok s1) :
    (∃ L, LawPasses s (.vote seat id yes) L ∧ (∀ L', LawPasses s (.vote seat id yes) L' → L' = L) ∧
      s1 = { s.withLaw id L with
        openProposals := s.openProposals.filter (·.id != id)
        journal := s.journal ++ s.decreeEntries L }) ∨
    ((∀ L', ¬ LawPasses s (.vote seat id yes) L') ∧ s1.pieces = s.pieces ∧ s1.journal = s.journal ∧
      s1.books = s.books) := by
  obtain ⟨_, p, L, hp, hbody, _, hc⟩ := voteBody_ok hb
  have huniq : ∀ L', LawPasses s (.vote seat id yes) L' → L' = L := by
    rintro L' ⟨seat', id', p', he, hp', hb', _, _⟩
    injection he with h1 h2 _
    subst h1 h2
    rw [hp] at hp'
    injection hp' with hp'
    subst hp'
    rw [hbody] at hb'
    injection hb' with hb'
    exact hb'.symm
  rcases hc with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · simp only [isDecidingVote, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨hy, hm⟩ := hd
    subst hy
    unfold decideLaw
    simp only
    split
    · rename_i hx
      exact Or.inl ⟨L, ⟨seat, id, p, rfl, hp, hbody, hm, List.isEmpty_iff.mp hx⟩, huniq, rfl⟩
    · rename_i hx
      refine Or.inr ⟨fun L' hl => ?_, rfl, rfl, rfl⟩
      have heq := huniq L' hl
      subst heq
      obtain ⟨_, _, _, _, _, _, _, hprob⟩ := hl
      rw [hprob] at hx
      exact hx rfl
  · refine Or.inr ⟨fun L' hl => ?_, rfl, rfl, rfl⟩
    obtain ⟨seat', id', p', he, hp', _, hm, _⟩ := hl
    injection he with h1 h2 h3
    subst h1 h2 h3
    rw [hp] at hp'
    injection hp' with hp'
    subst hp'
    simp only [isDecidingVote, Bool.true_and, decide_eq_false_iff_not] at hd
    exact hd hm

/-- Only a place move changes the pieces. -/
theorem body_pieces {s s1 : State G} {e : Event} (hne : ∀ p k loc, e ≠ .move p (.place k loc))
    (hl : ∀ L, ¬ LawPasses s e L) (h : bodyOf s e = .ok s1) : s1.pieces = s.pieces := by
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
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok h
      rfl
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> rfl
  | vote seat i y =>
    have hv : voteBody s seat i y = .ok s1 := h
    rcases vote_view hv with ⟨L, hp, _⟩ | ⟨_, hk, _⟩
    · exact absurd hp (hl L)
    · exact hk
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
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok h
      rfl
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> rfl
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h
      rfl
    · rfl
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    rfl

/-! ## One event at a time -/

theorem step_act {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hne : ¬ EndsTurn s e) :
    canAct s (seatOf e) = true ∧ ∃ s1, bodyOf s e = .ok s1 ∧
      finish (countAction s1 (seatOf e)) e = .ok s' := by
  rcases step_view h with ⟨h1, _⟩ | ⟨_, hc, s1, hb, hf⟩
  · exact absurd h1 hne
  · exact ⟨hc, s1, hb, hf⟩

theorem refundEntries_congr {s s' : State G} (hb : s'.books = s.books) (d : ActiveDeal) :
    s'.refundEntries d = s.refundEntries d := by
  simp only [State.refundEntries, State.balance, hb]
  rfl

/-- A move that writes no entries itself: if the game goes on, the state is as counted, and if it ends, the
only entries are the refunds. -/
theorem move_no_entries {s s1 s' : State G} {p : Seat} (he : s.phase ≠ .ended)
    (hf : checkWin (countAction s1 p) = .ok s') (hph : s1.phase = s.phase)
    (hj : s1.journal = s.journal) (hd : s1.deals = s.deals) (hbk : s1.books = s.books) :
    NoEntriesUnlessEnded s s' ∧ (s'.phase ≠ .ended → s' = countAction s1 p) := by
  rcases checkWin_ok hf with ⟨rfl, _⟩ | ⟨w, hw⟩
  · refine ⟨⟨fun hend => ?_, fun _ => newEntries_nil hj⟩, fun _ => rfl⟩
    have : s.phase = .ended := hph.symm.trans hend
    exact absurd this he
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    refine ⟨⟨fun _ => ?_, fun hne => absurd rfl hne⟩, fun hne => absurd rfl hne⟩
    apply newEntries_of
    have hfun : (countAction s1 p).refundEntries = s.refundEntries :=
      funext (refundEntries_congr hbk)
    change s1.journal ++ s1.deals.flatMap (countAction s1 p).refundEntries = _
    rw [hj, hd, hfun]

theorem all_contains_iff (signers signed : List Seat) (seat : Seat) :
    signers.all (signed ++ [seat]).contains = true ↔ ∀ j ∈ signers, j ∈ signed ∨ j = seat := by
  simp [List.all_eq_true]


/-! ## Declarations -/

theorem nextStage_of_last {s : State G} (hl : s.isLastTurn = true) :
    nextStage s = .newRound ∨ nextStage s = .gameOver := by
  have hp : s.phase = .actions := by
    simp only [State.isLastTurn, Bool.and_eq_true, beq_iff_eq] at hl
    exact hl.1
  unfold nextStage
  rw [hp]
  simp only [hl, ↓reduceIte]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem startNextTurn_declared_last (s : State G) (roll : Nat) (hl : s.isLastTurn = true) :
    ∀ q x, (startNextTurn s roll).declared q x = 0 := by
  intro q x
  unfold startNextTurn
  rcases nextStage_of_last hl with h | h <;> (rw [h]; try rfl)

theorem startNextTurn_declared_not_last (s : State G) (roll : Nat) (hne : s.phase ≠ .ended)
    (hl : ¬ s.isLastTurn = true) : (startNextTurn s roll).declared = s.declared := by
  have hstage : nextStage s ≠ .newRound ∧ nextStage s ≠ .gameOver := by
    unfold nextStage
    cases hp : s.phase with
    | ended => exact absurd hp hne
    | actions =>
      simp only [hl]
      exact ⟨by simp, by simp⟩
    | setup =>
      simp only [setupStage]
      split
      · exact ⟨by simp, by simp⟩
      · split <;> exact ⟨by simp, by simp⟩
  unfold startNextTurn
  split
  · rfl
  · rfl
  · rfl
  · rename_i he; exact absurd he hstage.1
  · rename_i he; exact absurd he hstage.2

theorem step_endTurnNow {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') : endTurnNow s = .ok s' := by
  rcases step_view h with ⟨_, h2⟩ | ⟨hn, _⟩
  · exact h2
  · exact absurd hend hn

/-- How declared numbers can change. -/
theorem declarations_kept {s s' : State G} {e : Event}
    (h : Engine.step G s e = .ok s') : DeclarationsKept s s' e := by
  have he := step_not_ended h
  refine ⟨?_, ?_, ?_⟩
  · rintro p r n rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, hs1⟩ := declareBody_ok hb
    refine ⟨h1, by simpa [State.isTurnOf] using h2, h3, h4, fun q x => ?_⟩
    subst hs1
    rcases finish_cases hf with rfl | ⟨w, hw⟩
    · rfl
    · obtain ⟨_, _, rfl⟩ := endGame_ok hw
      rfl
  · intro hend hl q x
    obtain ⟨_, _, rfl⟩ := endTurnNow_ok (step_endTurnNow hend h)
    refine startNextTurn_declared_last _ _ ?_ q x
    exact hl
  · intro hne hnot
    by_cases hend : EndsTurn s e
    · have hl : ¬ s.isLastTurn = true := fun hl => hnot ⟨hend, hl⟩
      obtain ⟨_, _, rfl⟩ := endTurnNow_ok (step_endTurnNow hend h)
      refine startNextTurn_declared_not_last _ _ ?_ ?_
      · exact he
      · exact hl
    · obtain ⟨_, s1, hb, hf⟩ := step_act h hend
      have h1 := bodyOf_declared hb hne
      rcases finish_cases hf with rfl | ⟨w, hw⟩
      · exact h1
      · obtain ⟨_, _, rfl⟩ := endGame_ok hw
        exact h1

/-- A declaration changes exactly one number, and counts one action and one event, unless the game ends. -/
theorem declare_is_exact {s s' : State G} {p : Seat} {r : Res} {n : Nat}
    (h : Engine.step G s (.move p (.declare r n)) = .ok s') :
    NoEntriesUnlessEnded s s' ∧ (s'.phase ≠ .ended →
    s' = { s with
      declared := fun q x => if q = p ∧ x = r then n else s.declared q x
      actionsThisTurn := fun q => if q = p then s.actionsThisTurn q + 1 else s.actionsThisTurn q
      eventsApplied := s.eventsApplied + 1 }) := by
  have he := step_not_ended h
  obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  have hf' : checkWin (countAction s1 p) = .ok s' := hf
  obtain ⟨_, _, hs1⟩ := declareBody_ok hb
  subst hs1
  exact move_no_entries he hf' rfl rfl rfl rfl

/-- `every_other_event_is_exact`. -/
theorem step_is_exact {s s' : State G} {e : Event}
    (h : Engine.step G s e = .ok s') :
    (∀ seat dealId, e = .exit seat dealId → newEntries s s' = []) ∧
    (∀ p to give get, e = .move p (.offer to give get) → NoEntriesUnlessEnded s s') ∧
    (∀ p id, e = .move p (.cancel id) → NoEntriesUnlessEnded s s') ∧
    (∀ seat d, e = .propose seat (.deal d) → newEntries s s' = []) ∧
    (∀ seat L, e = .propose seat (.law L) → newEntries s s' = []) ∧
    (∀ seat id, e = .sign seat id → ∃ p d,
      s.openProposal? id = some p ∧ p.body = .deal d ∧
      ((∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
        newEntries s s' = depositEntries s.dealsStarted d) ∧
      ((¬ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) → newEntries s s' = [])) ∧
    (∀ seat id yes, e = .vote seat id yes → VoteWritesExactly s s' e) ∧
    (∀ p id, e = .move p (.accept id) → ∃ o, s.offers.find? (·.id == id) = some o) ∧
    (∀ p, e = .move p .endTurn → EndsTurn s e) ∧
    (¬ EndsTurn s e → (∀ p k loc, e ≠ .move p (.place k loc)) → (∀ L, ¬ LawPasses s e L) →
      s'.pieces = s.pieces) ∧
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
    subst hs1
    exact (move_no_entries he hf' rfl rfl rfl rfl).1
  · -- a cancelled offer
    rintro p id rfl
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hf' : checkWin (countAction s1 p) = .ok s' := hf
    obtain ⟨_, _, hs1⟩ := cancelBody_ok hb
    subst hs1
    exact (move_no_entries he hf' rfl rfl rfl rfl).1
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
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, hc, _⟩⟩ := proposeBody_ok hb'
    · exact newEntries_nil rfl
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
    have hb' : voteBody s seat id yes = .ok s1 := hb
    have hd : s1.deals = s.deals := by
      obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok hb'
      · exact decideLaw_deals _ _ _
      · rfl
    have finish : ∀ es : List Entry, s1.journal = s.journal ++ es → s1.books = (s.afterPosting es).books →
        (s'.phase = .ended → newEntries s s' = es ++ s.deals.flatMap (s.afterPosting es).refundEntries) ∧
        (s'.phase ≠ .ended → newEntries s s' = es) := by
      intro es hj hbk
      rcases checkWin_ok hf' with ⟨rfl, _⟩ | ⟨w, hw⟩
      · refine ⟨fun hend => ?_, fun _ => newEntries_of hj⟩
        have : s.phase = .ended := f.phase.symm.trans hend
        exact absurd this he
      · obtain ⟨_, _, rfl⟩ := endGame_ok hw
        refine ⟨fun _ => ?_, fun hne => absurd rfl hne⟩
        apply newEntries_of
        have hfun : (countAction s1 seat).refundEntries = (s.afterPosting es).refundEntries :=
          funext (refundEntries_congr hbk)
        change s1.journal ++ s1.deals.flatMap (countAction s1 seat).refundEntries = _
        rw [hj, hd, hfun, List.append_assoc]
    rcases vote_view hb' with ⟨L, hp, hu, hs1⟩ | ⟨hno, _, hj, hbk⟩
    · obtain ⟨h1, h2⟩ := finish (s.decreeEntries L) (by rw [hs1]) (by rw [hs1]; rfl)
      exact ⟨s.decreeEntries L, fun L' hl => by rw [hu L' hl], fun hn => absurd hp (hn L), h1, h2⟩
    · obtain ⟨h1, h2⟩ := finish [] (by simp [hj]) (by rw [hbk]; simp [State.afterPosting, Books.postAll])
      exact ⟨[], fun L' hl => absurd hl (hno L'), fun _ => rfl, h1, h2⟩
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
    intro hnot hne hnl
    rcases step_view h with ⟨hend, _⟩ | ⟨_, _, s1, hb, hf⟩
    · exact absurd hend hnot
    · have hp := body_pieces hne hnl hb
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
