import Charter.Constitution.Promises

/-!
# What each engine helper does

One lemma per engine helper. Each says: if the helper accepted, then its checks passed and the new
state is exactly this. Later proofs use these lemmas and do not unfold the engine.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## What a roll reads -/

/-- What a roll reads differs from the state only in the round. -/
theorem atRoll_eq (s : State G) : ∃ n, s.atRoll = { s with round := n } := by
  unfold State.atRoll
  split
  · exact ⟨_, rfl⟩
  · exact ⟨s.round, rfl⟩

theorem atRoll_turnOrder (s : State G) : s.atRoll.turnOrder = s.turnOrder := by
  obtain ⟨_, h⟩ := atRoll_eq s; rw [h]

theorem atRoll_pieces (s : State G) : s.atRoll.pieces = s.pieces := by
  obtain ⟨_, h⟩ := atRoll_eq s; rw [h]

theorem atRoll_books (s : State G) : s.atRoll.books = s.books := by
  obtain ⟨_, h⟩ := atRoll_eq s; rw [h]

theorem atRoll_laws (s : State G) : s.atRoll.laws = s.laws := by
  obtain ⟨_, h⟩ := atRoll_eq s; rw [h]

/-- The bank's payments do not read the round. -/
theorem baseHarvest_atRoll (s : State G) (roll : Nat) : baseHarvest s.atRoll roll = baseHarvest s roll := by
  obtain ⟨_, h⟩ := atRoll_eq s; rw [h]; rfl

/-- A valid game passes the checks on its own parts. -/
theorem valid_shape (hG : G.Valid) : G.shapeChecks = true := by
  simp only [GameDef.Valid, GameDef.checks, Bool.and_eq_true] at hG
  exact hG.1

/-- A valid game's founding laws pass at every allowed number of seats. -/
theorem valid_founding (hG : G.Valid) {n : Nat} (h1 : minSeats ≤ n) (h2 : n ≤ maxSeats) :
    G.foundingOkFrom n [] 0 G.foundingLaws = true := by
  simp only [GameDef.Valid, GameDef.checks, Bool.and_eq_true] at hG
  have := List.all_eq_true.mp hG.2 n (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · omega
  · exact h

/-! ## Books and journal -/

theorem record_ok {s s1 : State G} {es : List Entry} (h : record s es = .ok s1) :
    ∃ b, s.books.postAll es = some b ∧ s1 = { s with books := b, journal := s.journal ++ es } := by
  unfold record at h
  split at h
  · rename_i b hb
    exact ⟨b, hb, by simpa using h.symm⟩
  · cases h

theorem endGame_ok {s s' : State G} {w : Seat} (h : endGame s w = .ok s') :
    ∃ b, s.books.postAll (s.deals.flatMap s.refundEntries) = some b ∧
      s' = { s with
        books := b, journal := s.journal ++ s.deals.flatMap s.refundEntries
        phase := .ended, winner := some w, deals := [], offers := [], openProposals := [] } := by
  unfold endGame at h
  cases hr : record s (s.deals.flatMap s.refundEntries) with
  | error m => simp [hr, bind, Except.bind] at h
  | ok s1 =>
    simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨b, hb, rfl⟩ := record_ok hr
    exact ⟨b, hb, h.symm⟩

/-- `bestSeat` finds nobody only in an empty list. -/
theorem bestSeat_none {s : State G} {L : List Seat} (h : bestSeat s L = none) : L = [] := by
  have key : ∀ (f : Option Seat → Seat → Option Seat), (∀ o c, (f o c).isSome = true) →
      ∀ (L : List Seat) (o : Option Seat), o.isSome = true → (L.foldl f o).isSome = true := by
    intro f hf L
    induction L with
    | nil => simp
    | cons a t ih => intro o _; exact ih _ (hf o a)
  cases L with
  | nil => rfl
  | cons a t =>
    have hs : (bestSeat s (a :: t)).isSome = true := by
      unfold bestSeat
      rw [List.foldl_cons]
      apply key
      · intro o c
        cases o with
        | none => rfl
        | some b => simp only; split <;> rfl
      · rfl
    rw [h] at hs
    simp at hs

theorem checkWin_ok {s s' : State G} (h : checkWin s = .ok s') :
    (s' = s ∧ seatsAtTarget s = []) ∨ (∃ w, endGame s w = .ok s') := by
  unfold checkWin at h
  split at h
  · exact Or.inr ⟨_, h⟩
  · rename_i hb
    exact Or.inl ⟨by simpa using h.symm, bestSeat_none hb⟩

theorem act_ok {s s' : State G} {seat : Seat} {body : Except String (State G)}
    (h : act s seat body = .ok s') :
    canAct s seat = true ∧ ∃ s1, body = .ok s1 ∧ s' = countAction s1 seat := by
  unfold act at h
  split at h
  · rename_i hc
    cases hb : body with
    | error m => simp [hb] at h
    | ok s1 =>
      rw [hb] at h
      exact ⟨hc, s1, rfl, by simpa using h.symm⟩
  · cases h

theorem actThenCheckWin_ok {s s' : State G} {seat : Seat} {body : Except String (State G)}
    (h : actThenCheckWin s seat body = .ok s') :
    canAct s seat = true ∧ ∃ s1, body = .ok s1 ∧ checkWin (countAction s1 seat) = .ok s' := by
  unfold actThenCheckWin at h
  split at h
  · rename_i s2 hs2
    obtain ⟨hc, s1, hb, rfl⟩ := act_ok hs2
    exact ⟨hc, s1, hb, h⟩
  · cases h

/-! ## Deals -/

theorem startDeal_ok {s s1 : State G} {id : Nat} {d : Deal} (h : startDeal s id d = .ok s1) :
    s.canStartDeal = true ∧ dealProblems s d = [] ∧
    ∃ b, s.books.postAll (depositEntries s.dealsStarted d) = some b ∧
      s1 = { s with
        books := b, journal := s.journal ++ depositEntries s.dealsStarted d
        deals := s.deals ++
          [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
             startRound := s.round, builtBefore := s.builtThisRound.length }]
        dealsStarted := s.dealsStarted + 1
        openProposals := s.openProposals.filter (·.id != id) } := by
  unfold startDeal at h
  split at h
  · cases h
  rename_i hc
  split at h
  · cases h
  rename_i hp
  cases hr : record s (depositEntries s.dealsStarted d) with
  | error m => simp [hr, bind, Except.bind] at h
  | ok s2 =>
    simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨b, hb, rfl⟩ := record_ok hr
    refine ⟨by simpa using hc, by simpa using hp, b, hb, h.symm⟩

theorem signBody_ok {s s1 : State G} {seat id : Nat} (h : signBody s seat id = .ok s1) :
    s.phase = .actions ∧ ∃ p d, s.openProposal? id = some p ∧ p.body = .deal d ∧
      d.signers.contains seat = true ∧ p.signed.contains seat = false ∧
      ((d.signers.all (p.signed ++ [seat]).contains = true ∧ startDeal s id d = .ok s1) ∨
       (d.signers.all (p.signed ++ [seat]).contains = false ∧
        s1 = { s with openProposals := s.openProposals.map fun q =>
          if q.id == id then { q with signed := p.signed ++ [seat] } else q })) := by
  unfold signBody at h
  split at h
  · cases h
  rename_i hph
  split at h
  · cases h
  rename_i p hp
  split at h
  · cases h
  rename_i d hd
  split at h
  · cases h
  rename_i hs
  split at h
  · cases h
  rename_i hn
  refine ⟨by simpa using hph, p, d, hp, hd, by simpa using hs, by simpa using hn, ?_⟩
  simp only at h
  split at h
  · rename_i ha
    exact Or.inl ⟨ha, h⟩
  · rename_i ha
    exact Or.inr ⟨by simpa using ha, by simpa using h.symm⟩

theorem exitBody_ok {s s1 : State G} {seat id : Nat} (h : exitBody s seat id = .ok s1) :
    s.phase = .actions ∧ s.deals.any (fun d => d.id == id && d.deal.signers.contains seat) = true ∧
    s1 = { s with deals := s.deals.map fun d =>
      if d.id == id then { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
      else d } := by
  unfold exitBody at h
  split at h
  · cases h
  rename_i hph
  split at h
  · rename_i ha
    exact ⟨by simpa using hph, ha, by simpa using h.symm⟩
  · cases h

/-! ## Moves -/

theorem setupBody_ok {s s1 : State G} {p : Seat} {k : PieceKind} {loc : Loc}
    (h : setupBody s p k loc = .ok s1) :
    s.canSetupPlace p k loc = true ∧ s1 = { s with pieces := s.placedPieces p k loc } := by
  unfold setupBody at h
  split at h
  · rename_i hc
    exact ⟨hc, by simpa using h.symm⟩
  · cases h

theorem buildBody_ok {s s1 : State G} {p : Seat} {k : PieceKind} {loc : Loc}
    (h : buildBody s p k loc = .ok s1) :
    s.canPlace p k loc = true ∧
    ∃ b, s.books.postAll (s.costEntries p k ++
        lawEntries (s.afterPosting (s.costEntries p k)) (.build p k)) = some b ∧
      s1 = { s with
        books := b
        journal := s.journal ++ (s.costEntries p k ++
          lawEntries (s.afterPosting (s.costEntries p k)) (.build p k))
        pieces := s.placedPieces p k loc
        builtThisRound := s.builtThisRound ++ [(p, k)] } := by
  unfold buildBody at h
  split at h
  · rename_i hc
    simp only at h
    split at h
    · rename_i s2 hr
      obtain ⟨b, hb, rfl⟩ := record_ok hr
      exact ⟨hc, b, hb, by simpa using h.symm⟩
    · cases h
  · cases h

theorem placeBody_ok {s s1 : State G} {p : Seat} {k : PieceKind} {loc : Loc}
    (h : placeBody s p k loc = .ok s1) :
    (s.phase = .setup ∧ setupBody s p k loc = .ok s1) ∨
    (s.phase = .actions ∧ buildBody s p k loc = .ok s1) := by
  unfold placeBody at h
  split at h
  · rename_i hp; exact Or.inl ⟨hp, h⟩
  · rename_i hp; exact Or.inr ⟨hp, h⟩
  · cases h

theorem bankTradeBody_ok {s s1 : State G} {p : Seat} {give get : Res}
    (h : bankTradeBody s p give get = .ok s1) :
    s.phase = .actions ∧ s.isTurnOf p = true ∧ give ≠ get ∧ G.isRes give = true ∧
      G.isRes get = true ∧ record s (s.bankTradeEntries p give get) = .ok s1 := by
  unfold bankTradeBody at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  simp at h1 h2
  exact ⟨h1.1, h1.2, h2.1.1, h2.1.2, h2.2, h⟩

theorem offerBody_ok {s s1 : State G} {p : Seat} {to : Option Seat} {give get : Bundle}
    (h : offerBody s p to give get = .ok s1) :
    s.phase = .actions ∧ s.isTurnOf p = true ∧
    s1 = { s with
      offers := s.offers ++ [⟨s.nextOfferId, p, to, give, get⟩]
      nextOfferId := s.nextOfferId + 1 } := by
  unfold offerBody at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  split at h
  · cases h
  simp only at h
  simp at h1
  refine ⟨h1.1, h1.2, ?_⟩
  cases to with
  | none => simpa using h.symm
  | some q =>
    simp only at h
    split at h
    · cases h
    · simpa using h.symm

theorem acceptBody_ok {s s1 : State G} {p : Seat} {id : Nat} (h : acceptBody s p id = .ok s1) :
    s.phase = .actions ∧ ∃ o, s.offers.find? (·.id == id) = some o ∧ o.src ≠ p ∧
      (o.to = none ∨ o.to = some p) ∧ s.tradeBlocked p o.src = false ∧
      ∃ b, s.books.postAll (offerEntries o p) = some b ∧
        s1 = { s with
          books := b, journal := s.journal ++ offerEntries o p
          offers := s.offers.filter (·.id != id) } := by
  unfold acceptBody at h
  split at h
  · cases h
  rename_i hph
  split at h
  · cases h
  rename_i o ho
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · rename_i s2 hr
    obtain ⟨b, hb, rfl⟩ := record_ok hr
    refine ⟨by simpa using hph, o, ho, by simpa using h1, ?_, by simpa using h3, b, hb,
      by simpa using h.symm⟩
    simp only [Bool.not_eq_true] at h2
    cases hto : o.to with
    | none => exact Or.inl rfl
    | some q =>
      right
      simp [hto] at h2
      simp [h2]
  · cases h

theorem cancelBody_ok {s s1 : State G} {p : Seat} {id : Nat} (h : cancelBody s p id = .ok s1) :
    s.phase = .actions ∧ s.offers.any (fun o => o.id == id && o.src == p) = true ∧
    s1 = { s with offers := s.offers.filter (·.id != id) } := by
  unfold cancelBody at h
  split at h
  · cases h
  rename_i hph
  split at h
  · rename_i ha
    exact ⟨by simpa using hph, ha, by simpa using h.symm⟩
  · cases h

/-! ## Proposals and votes -/

theorem proposeBody_ok {s s1 : State G} {seat : Seat} {body : Proposal}
    (h : proposeBody s seat body = .ok s1) :
    s.phase = .actions ∧ (s.openProposals.filter (·.by_ == seat)).length < maxOpenPerSeat ∧
    ((∃ L, body = .law L ∧ lawProblems G s L = [] ∧ ∃ b,
        s.books.postAll (lawFeeEntries G seat) = some b ∧
        s1 = addProposal { s with books := b, journal := s.journal ++ lawFeeEntries G seat }
          seat (.law L)) ∨
     (∃ d, body = .deal d ∧ d.signers.contains seat = true ∧ dealProblems s d = [] ∧
        s1 = addProposal s seat (.deal d))) := by
  unfold proposeBody at h
  split at h
  · cases h
  rename_i hph
  split at h
  · cases h
  rename_i hn
  refine ⟨by simpa using hph, by omega, ?_⟩
  split at h
  · rename_i L
    unfold proposeLaw at h
    split at h
    · cases h
    rename_i hl
    split at h
    · rename_i s2 hr
      obtain ⟨b, hb, rfl⟩ := record_ok hr
      exact Or.inl ⟨L, rfl, by simpa using hl, b, hb, by simpa using h.symm⟩
    · cases h
  · rename_i d
    unfold proposeDeal at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    exact Or.inr ⟨d, rfl, by simpa using h1, by simpa using h2, by simpa using h.symm⟩

theorem voteBody_ok {s s1 : State G} {seat id : Nat} {yes : Bool}
    (h : voteBody s seat id yes = .ok s1) :
    s.phase = .actions ∧ ∃ p L, s.openProposal? id = some p ∧ p.body = .law L ∧
      (p.votes.map (·.1)).contains seat = false ∧
      ((isDecidingVote s p seat yes = true ∧ s1 = decideLaw s id L) ∨
       (isDecidingVote s p seat yes = false ∧
        s1 = { s with openProposals := s.openProposals.map fun q =>
          if q.id == id then q.withVote seat yes else q })) := by
  unfold voteBody at h
  split at h
  · cases h
  rename_i hph
  split at h
  · cases h
  rename_i p hp
  split at h
  · cases h
  rename_i L hL
  split at h
  · cases h
  rename_i hv
  refine ⟨by simpa using hph, p, L, hp, hL, by simpa using hv, ?_⟩
  split at h
  · rename_i hd
    exact Or.inl ⟨hd, by simpa using h.symm⟩
  · rename_i hd
    exact Or.inr ⟨by simpa using hd, by simpa using h.symm⟩

/-! ## The turn change -/

theorem endTurnNow_ok {s s' : State G} (h : endTurnNow s = .ok s') :
    ∃ b, s.books.postAll (turnEntries s (rollAt G s.seed s.rollsMade)) = some b ∧
      s' = startNextTurn
        { s with
          books := b
          journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade) }
        (rollAt G s.seed s.rollsMade) := by
  unfold endTurnNow at h
  simp only at h
  split at h
  · rename_i s1 hr
    obtain ⟨b, hb, rfl⟩ := record_ok hr
    exact ⟨b, hb, by simpa using h.symm⟩
  · cases h

/-! ## One view of `step`

Every accepted event is one of two things: it ends the turn, or it runs a body for a seat and counts
that action. -/

/-- The body an event runs, when it does not end the turn. -/
def bodyOf (s : State G) : Event → Except String (State G)
  | .move p m => moveBody s p m
  | .propose seat p => proposeBody s seat p
  | .vote seat id yes => voteBody s seat id yes
  | .sign seat id => signBody s seat id
  | .exit seat id => exitBody s seat id
  | .forceEndTurn => .error "ends the turn"

/-- The seat an event acts for, when it does not end the turn. -/
def seatOf : Event → Seat
  | .move p _ => p
  | .propose seat _ => seat
  | .vote seat _ _ => seat
  | .sign seat _ => seat
  | .exit seat _ => seat
  | .forceEndTurn => 0

/-- Moves and votes look for a winner after the action. Other events do not. -/
def finish (s : State G) : Event → Except String (State G)
  | .move .. => checkWin s
  | .vote .. => checkWin s
  | _ => .ok s

theorem step_not_ended {s s' : State G} {e : Event} (h : step G s e = .ok s') :
    s.phase ≠ .ended := by
  unfold step at h
  intro he
  simp [he] at h

theorem step_view {s s' : State G} {e : Event} (h : step G s e = .ok s') :
    (EndsTurn s e ∧ endTurnNow s = .ok s') ∨
    (¬ EndsTurn s e ∧ canAct s (seatOf e) = true ∧ ∃ s1, bodyOf s e = .ok s1 ∧
      finish (countAction s1 (seatOf e)) e = .ok s') := by
  have hne := step_not_ended h
  unfold step at h
  rw [ite_eq_right_of_eq_false _ _ (by simpa using hne)] at h
  cases e with
  | forceEndTurn => exact Or.inl ⟨trivial, h⟩
  | move p m =>
    cases m with
    | endTurn =>
      simp only at h
      split at h
      · rename_i ht
        refine Or.inl ⟨?_, h⟩
        simpa [EndsTurn, State.isTurnOf] using ht
      · cases h
    | place k loc =>
      obtain ⟨hc, s1, hb, hf⟩ := actThenCheckWin_ok h
      exact Or.inr ⟨fun x => x, hc, s1, hb, hf⟩
    | bankTrade a b =>
      obtain ⟨hc, s1, hb, hf⟩ := actThenCheckWin_ok h
      exact Or.inr ⟨fun x => x, hc, s1, hb, hf⟩
    | offer t a b =>
      obtain ⟨hc, s1, hb, hf⟩ := actThenCheckWin_ok h
      exact Or.inr ⟨fun x => x, hc, s1, hb, hf⟩
    | accept i =>
      obtain ⟨hc, s1, hb, hf⟩ := actThenCheckWin_ok h
      exact Or.inr ⟨fun x => x, hc, s1, hb, hf⟩
    | cancel i =>
      obtain ⟨hc, s1, hb, hf⟩ := actThenCheckWin_ok h
      exact Or.inr ⟨fun x => x, hc, s1, hb, hf⟩
  | propose seat b =>
    obtain ⟨hc, s1, hb, rfl⟩ := act_ok h
    exact Or.inr ⟨fun x => x, hc, s1, hb, rfl⟩
  | vote seat i y =>
    obtain ⟨hc, s1, hb, hf⟩ := actThenCheckWin_ok h
    exact Or.inr ⟨fun x => x, hc, s1, hb, hf⟩
  | sign seat i =>
    obtain ⟨hc, s1, hb, rfl⟩ := act_ok h
    exact Or.inr ⟨fun x => x, hc, s1, hb, rfl⟩
  | exit seat i =>
    obtain ⟨hc, s1, hb, rfl⟩ := act_ok h
    exact Or.inr ⟨fun x => x, hc, s1, hb, rfl⟩

end Charter.Proofs
