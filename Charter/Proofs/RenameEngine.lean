import Charter.Proofs.RenameDeals

/-!
# Renaming: the engine's shared helpers and its moves

Each engine helper returns a new state or rejects. The lemmas here say: the helper on the renamed
game gives the renamed result of the helper on the original game. Rejection and acceptance match.
-/

namespace Charter.Renaming

open Charter Charter.Engine

variable (σ : Renaming) {G : GameDef}

/-- Two states are equal when each field is equal. -/
theorem state_fields_eq {x y : State G}
    (h1 : x.turnOrder = y.turnOrder) (h2 : x.phase = y.phase) (h3 : x.round = y.round)
    (h4 : x.turnIndex = y.turnIndex) (h5 : x.turnsTaken = y.turnsTaken)
    (h6 : x.rollsMade = y.rollsMade) (h7 : x.lastRoll = y.lastRoll) (h8 : x.seed = y.seed)
    (h9 : x.seedCommitment = y.seedCommitment) (h10 : x.books = y.books)
    (h11 : x.journal = y.journal) (h12 : x.pieces = y.pieces) (h13 : x.laws = y.laws)
    (h14 : x.openProposals = y.openProposals) (h15 : x.nextProposalId = y.nextProposalId)
    (h16 : x.deals = y.deals) (h17 : x.dealsStarted = y.dealsStarted) (h18 : x.offers = y.offers)
    (h19 : x.nextOfferId = y.nextOfferId) (h20 : x.builtThisRound = y.builtThisRound)
    (h21 : x.actionsThisTurn = y.actionsThisTurn) (h22 : x.eventsApplied = y.eventsApplied)
    (h23 : x.winner = y.winner) (h24 : x.declared = y.declared) : x = y := by
  cases x; cases y; simp_all

/-- Prove two states equal field by field, and close the fields that hold by computation. -/
macro "state_ext" : tactic => `(tactic| (apply state_fields_eq <;> try rfl))

@[simp] theorem map_ok {α β ε} (f : α → β) (a : α) :
    Except.map f (Except.ok a : Except ε α) = .ok (f a) := rfl

@[simp] theorem map_error {α β ε} (f : α → β) (m : ε) :
    Except.map f (Except.error m : Except ε α) = .error m := rfl

/-! ## Shared helpers -/

/-- Recording renamed entries gives the renamed result. -/
theorem record_rename (s : State G) (es : List Entry) :
    record (σ.state s) (es.map σ.entry) = (record s es).map σ.state := by
  unfold record
  rw [state_books, postAll_rename]
  cases s.books.postAll es with
  | none => rfl
  | some b =>
    simp only [Option.map_some, map_ok, Except.ok.injEq]
    state_ext
    simp

theorem back_eq (p seat : Seat) : (σ.back p = seat) ↔ p = σ.to seat := by
  constructor
  · rintro rfl; exact (σ.to_back p).symm
  · rintro rfl; exact σ.back_to seat

theorem countAction_rename (s : State G) (seat : Seat) :
    countAction (σ.state s) (σ.to seat) = σ.state (countAction s seat) := by
  state_ext
  funext q
  obtain ⟨q, rfl⟩ : ∃ c, q = σ.to c := ⟨σ.back q, (σ.to_back q).symm⟩
  simp [countAction, state, σ.back_to]

theorem canAct_rename (s : State G) (seat : Seat) :
    canAct (σ.state s) (σ.to seat) = canAct s seat := by
  simp [canAct]

theorem bestSeat_rename (s : State G) (l : List Seat) :
    bestSeat (σ.state s) (l.map σ.to) = (bestSeat s l).map σ.to := by
  unfold bestSeat
  suffices h : ∀ (l : List Seat) (o : Option Seat),
      ((l.map σ.to).foldl
        (fun best c =>
          match best with
          | none => some c
          | some b => if (σ.state s).pointsOf b < (σ.state s).pointsOf c then some c else some b)
        (o.map σ.to)) =
      (l.foldl
        (fun best c =>
          match best with
          | none => some c
          | some b => if s.pointsOf b < s.pointsOf c then some c else some b)
        o).map σ.to from h l none
  intro l
  induction l with
  | nil => intro o; rfl
  | cons x t ih =>
    intro o
    simp only [List.map_cons, List.foldl_cons]
    rw [← ih]
    congr 1
    cases o with
    | none => rfl
    | some b =>
      simp only [Option.map_some, pointsOf_rename]
      split <;> rfl

theorem seatsAtTarget_rename (s : State G) :
    seatsAtTarget (σ.state s) = (seatsAtTarget s).map σ.to := by
  simp [seatsAtTarget, List.filter_map, Function.comp_def]

theorem endGame_rename (s : State G) (w : Seat) :
    endGame (σ.state s) (σ.to w) = (endGame s w).map σ.state := by
  unfold endGame
  rw [refunds_rename, record_rename]
  cases record s (s.deals.flatMap s.refundEntries) <;> rfl

theorem checkWin_rename (s : State G) :
    checkWin (σ.state s) = (checkWin s).map σ.state := by
  unfold checkWin
  rw [seatsAtTarget_rename, bestSeat_rename]
  cases bestSeat s (seatsAtTarget s) with
  | none => rfl
  | some w => exact σ.endGame_rename s w

theorem act_rename (s : State G) (seat : Seat) (body : Except String (State G)) :
    act (σ.state s) (σ.to seat) (body.map σ.state) = (act s seat body).map σ.state := by
  unfold act
  rw [canAct_rename]
  split
  · cases body with
    | error m => rfl
    | ok s1 => simp [countAction_rename]
  · rfl

theorem actThenCheckWin_rename (s : State G) (seat : Seat) (body : Except String (State G)) :
    actThenCheckWin (σ.state s) (σ.to seat) (body.map σ.state) =
      (actThenCheckWin s seat body).map σ.state := by
  unfold actThenCheckWin
  rw [act_rename]
  cases act s seat body with
  | error m => rfl
  | ok s1 => exact σ.checkWin_rename s1

/-! ## Placing a piece -/

theorem buildBody_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    buildBody (σ.state s) (σ.to p) k loc = (buildBody s p k loc).map σ.state := by
  unfold buildBody
  rw [canPlace_rename]
  split
  · have hl : lawEntries ((σ.state s).afterPosting ((s.costEntries p k).map σ.entry))
        (.build (σ.to p) k) =
        (lawEntries (s.afterPosting (s.costEntries p k)) (.build p k)).map σ.entry := by
      rw [afterPosting_rename]
      exact σ.lawEntries_rename _ (.build p k)
    simp only [costEntries_rename, hl, ← List.map_append, record_rename]
    cases record s (s.costEntries p k ++ lawEntries (s.afterPosting (s.costEntries p k))
      (.build p k)) with
    | error m => rfl
    | ok s1 =>
      simp only [map_ok, Except.ok.injEq]
      state_ext
      · simp [placedPieces_rename]
      · simp
  · rfl

theorem setupBody_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    setupBody (σ.state s) (σ.to p) k loc = (setupBody s p k loc).map σ.state := by
  unfold setupBody
  rw [canSetupPlace_rename]
  split
  · simp only [map_ok, Except.ok.injEq]
    state_ext
    simp [placedPieces_rename]
  · rfl

theorem placeBody_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    placeBody (σ.state s) (σ.to p) k loc = (placeBody s p k loc).map σ.state := by
  unfold placeBody
  rw [state_phase]
  cases s.phase with
  | setup => exact σ.setupBody_rename s p k loc
  | actions => exact σ.buildBody_rename s p k loc
  | ended => rfl

/-! ## Trading -/

theorem bankTradeBody_rename (s : State G) (p : Seat) (give get : Res) :
    bankTradeBody (σ.state s) (σ.to p) give get = (bankTradeBody s p give get).map σ.state := by
  unfold bankTradeBody
  simp only [state_phase, isTurnOf_rename]
  split
  · rfl
  · split
    · rfl
    · rw [bankTradeEntries_rename, record_rename]

theorem offerBody_rename (s : State G) (p : Seat) (to : Option Seat) (give get : Bundle) :
    offerBody (σ.state s) (σ.to p) (to.map σ.to) give get =
      (offerBody s p to give get).map σ.state := by
  unfold offerBody
  simp only [state_phase, isTurnOf_rename, affords_rename]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · have hok : ∀ (m : Option Seat), m = to.map σ.to →
            ({ σ.state s with
              offers := (σ.state s).offers ++ [⟨(σ.state s).nextOfferId, σ.to p, m, give, get⟩]
              nextOfferId := (σ.state s).nextOfferId + 1 } : State G) =
            σ.state { s with
              offers := s.offers ++ [⟨s.nextOfferId, p, to, give, get⟩]
              nextOfferId := s.nextOfferId + 1 } := by
          rintro m rfl
          state_ext
          simp [offer]
        cases to with
        | none =>
          simp only [Option.map_none, Bool.not_true, Bool.false_eq_true, ↓reduceIte, map_ok]
          exact congrArg Except.ok (hok _ rfl)
        | some q =>
          simp only [Option.map_some, state_turnOrder, contains_map_to, to_bne_to,
            tradeBlocked_rename]
          split
          · rfl
          · simp only [map_ok]
            exact congrArg Except.ok (hok _ rfl)

theorem find_offer (s : State G) (id : Nat) :
    (σ.state s).offers.find? (·.id == id) = (s.offers.find? (·.id == id)).map σ.offer := by
  simp [List.find?_map, Function.comp_def]

theorem filter_offers (s : State G) (id : Nat) :
    (s.offers.map σ.offer).filter (·.id != id) = (s.offers.filter (·.id != id)).map σ.offer := by
  simp [List.filter_map, Function.comp_def]

theorem acceptBody_rename (s : State G) (p : Seat) (id : Nat) :
    acceptBody (σ.state s) (σ.to p) id = (acceptBody s p id).map σ.state := by
  unfold acceptBody
  rw [find_offer, state_phase]
  split
  · rfl
  · cases s.offers.find? (·.id == id) with
    | none => rfl
    | some o =>
      simp only [Option.map_some, offer_src, to_beq_to, offer_to, tradeBlocked_rename,
        Option.isNone_map, map_to_beq_some, offerEntries_rename, record_rename]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · cases record s (offerEntries o p) with
            | error m => rfl
            | ok s1 =>
              simp only [map_ok, Except.ok.injEq]
              state_ext
              exact σ.filter_offers s id

theorem cancelBody_rename (s : State G) (p : Seat) (id : Nat) :
    cancelBody (σ.state s) (σ.to p) id = (cancelBody s p id).map σ.state := by
  unfold cancelBody
  simp only [state_phase, state_offers, List.any_map, Function.comp_def, offer_id, offer_src,
    to_beq_to]
  split
  · rfl
  · split
    · simp only [map_ok, Except.ok.injEq]
      state_ext
      exact σ.filter_offers s id
    · rfl

theorem declareBody_rename (s : State G) (p : Seat) (r : Res) (n : Nat) :
    declareBody (σ.state s) (σ.to p) r n = (declareBody s p r n).map σ.state := by
  unfold declareBody
  simp only [state_phase, isTurnOf_rename]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · simp only [map_ok, Except.ok.injEq]
        state_ext
        funext q x
        by_cases hq : q = σ.to p
        · subst hq
          simp [state, σ.back_to]
        · have : σ.back q ≠ p := fun h => hq (by rw [← h, σ.to_back])
          simp [state, hq, this]

theorem moveBody_rename (s : State G) (p : Seat) (m : Move) :
    moveBody (σ.state s) (σ.to p) (σ.move m) = (moveBody s p m).map σ.state := by
  cases m with
  | place k loc => exact σ.placeBody_rename s p k loc
  | bankTrade give get => exact σ.bankTradeBody_rename s p give get
  | offer to give get => exact σ.offerBody_rename s p to give get
  | accept id => exact σ.acceptBody_rename s p id
  | cancel id => exact σ.cancelBody_rename s p id
  | declare r n => exact σ.declareBody_rename s p r n
  | endTurn => rfl

end Charter.Renaming
