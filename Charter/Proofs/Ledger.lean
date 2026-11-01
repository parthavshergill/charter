import Charter.Proofs.Frame

/-!
# The books follow the journal, and the total never changes

`Core` is what is true of every state a game can reach, as far as money goes. `Core.start` shows a
new game has it, and `Core.step` shows every accepted event keeps it.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

theorem canAct_mem {s : State G} {seat : Seat} (h : canAct s seat = true) :
    seat ∈ s.turnOrder ∧ s.actionsThisTurn seat < maxActionsPerTurn := by
  simpa [canAct] using h

/-- Every offer was made by a seat in the game. -/
def OffersOk (s : State G) : Prop := ∀ o ∈ s.offers, o.src ∈ s.turnOrder

/-- `s'` is `s` with some entries posted and written down, all between accounts of the game. -/
def Posted (T : List Seat) (s s' : State G) : Prop :=
  ∃ es, s'.journal = s.journal ++ es ∧ s.books.postAll es = some s'.books ∧ ∀ x ∈ es, EntryOk T x

theorem Posted.refl {T : List Seat} {s s' : State G} (hj : s'.journal = s.journal)
    (hb : s'.books = s.books) : Posted T s s' :=
  ⟨[], by simp [hj], by simp [Books.postAll, hb], by simp⟩

theorem Posted.trans {T : List Seat} {a b c : State G} (h1 : Posted T a b) (h2 : Posted T b c) :
    Posted T a c := by
  obtain ⟨xs, hj1, hb1, hx1⟩ := h1
  obtain ⟨ys, hj2, hb2, hx2⟩ := h2
  refine ⟨xs ++ ys, by simp [hj1, hj2], ?_, ?_⟩
  · rw [postAll_append, hb1]
    exact hb2
  · intro x hx
    cases List.mem_append.mp hx with
    | inl h => exact hx1 x h
    | inr h => exact hx2 x h

/-! ## Bundles and fees -/

theorem bundleEntries_ok {T : List Seat} {a b : Account} (ha : AcctOk T a) (hb : AcctOk T b)
    (bd : Bundle) (r : Reason) : ∀ x ∈ bundleEntries a b bd r, EntryOk T x := by
  intro x hx
  simp only [bundleEntries, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact ⟨ha, hb⟩

theorem costEntries_ok {s : State G} {p : Seat} (hp : p ∈ s.turnOrder) (k : PieceKind) :
    ∀ x ∈ s.costEntries p k, EntryOk s.turnOrder x := by
  intro x hx
  simp only [State.costEntries, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact ⟨hp, trivial⟩

theorem mem_placedPieces {s : State G} {p : Seat} {k : PieceKind} {loc : Loc} {x : Piece}
    (h : x ∈ s.placedPieces p k loc) : x ∈ s.pieces ∨ x = ⟨p, k, loc⟩ := by
  simp only [State.placedPieces, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · left
    split at h
    · exact List.mem_of_mem_erase h
    · exact h
  · exact Or.inr h

theorem placedPieces_ok {s : State G} (hP : PiecesOk s) {p : Seat} (hp : p ∈ s.turnOrder)
    (k : PieceKind) (loc : Loc) : ∀ x ∈ s.placedPieces p k loc, x.owner ∈ s.turnOrder := by
  intro x hx
  rcases mem_placedPieces hx with h | rfl
  · exact hP x h
  · exact hp

/-! ## Event bodies -/

/-- What an event body needs and keeps. -/
structure BodyOk (s s1 : State G) : Prop where
  posted : Posted s.turnOrder s s1
  pieces : ∀ x ∈ s1.pieces, x.owner ∈ s.turnOrder
  offers : ∀ o ∈ s1.offers, o.src ∈ s.turnOrder
  deals : ∀ d ∈ s1.deals, DealOk s.turnOrder d

theorem startDeal_bodyOk {s s1 : State G} {id : Nat} {d : Deal} (hP : PiecesOk s) (hO : OffersOk s)
    (hD : DealsOk s) (h : startDeal s id d = .ok s1) : BodyOk s s1 := by
  obtain ⟨hc, hprob, b, hb, rfl⟩ := startDeal_ok h
  obtain ⟨h1, h2, h3, h4⟩ := dealProblems_nil hprob
  have hid : s.dealsStarted < maxDealsPerGame := by
    simp only [State.canStartDeal, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1
  refine ⟨⟨_, rfl, hb, depositEntries_ok hid h1 h2⟩, hP, hO, ?_⟩
  intro a ha
  simp only [List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact hD a ha
  · exact ⟨hid, h1, h3, h4⟩

theorem body_ok {s s1 : State G} {e : Event} (hP : PiecesOk s) (hO : OffersOk s) (hD : DealsOk s)
    (hc : canAct s (seatOf e) = true) (h : bodyOf s e = .ok s1) : BodyOk s s1 := by
  have hs := (canAct_mem hc).1
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    simp only [seatOf] at hs
    cases m with
    | endTurn => cases h
    | place k loc =>
      rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        exact ⟨Posted.refl rfl rfl, placedPieces_ok hP hs k loc, hO, hD⟩
      · obtain ⟨_, b, hb, rfl⟩ := buildBody_ok h
        refine ⟨⟨_, rfl, hb, ?_⟩, placedPieces_ok hP hs k loc, hO, hD⟩
        intro x hx
        cases List.mem_append.mp hx with
        | inl hx => exact costEntries_ok hs k x hx
        | inr hx => exact lawEntries_ok (s.afterPosting _) (t := .build p k) hs x hx
    | bankTrade a c =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok h
      obtain ⟨b, hb, rfl⟩ := record_ok hr
      refine ⟨⟨_, rfl, hb, ?_⟩, hP, hO, hD⟩
      intro x hx
      simp only [State.bankTradeEntries, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨hs, trivial⟩
      · exact ⟨trivial, hs⟩
    | offer t a c =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok h
      refine ⟨Posted.refl rfl rfl, hP, ?_, hD⟩
      intro o ho
      simp only [List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · exact hO o ho
      · exact hs
    | accept i =>
      obtain ⟨_, o, ho, _, _, _, b, hb, rfl⟩ := acceptBody_ok h
      have hsrc : o.src ∈ s.turnOrder := hO o (List.mem_of_find?_eq_some ho)
      refine ⟨⟨_, rfl, hb, ?_⟩, hP, fun x hx => hO x (List.mem_filter.mp hx).1, hD⟩
      intro x hx
      cases List.mem_append.mp hx with
      | inl hx => exact bundleEntries_ok (a := .player o.src) (b := .player p) hsrc hs _ _ x hx
      | inr hx => exact bundleEntries_ok (a := .player p) (b := .player o.src) hs hsrc _ _ x hx
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok h
      exact ⟨Posted.refl rfl rfl, hP, fun x hx => hO x (List.mem_filter.mp hx).1, hD⟩
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok h
      exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
  | propose seat b =>
    simp only [seatOf] at hs
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h
    · exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
    · exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
  | vote seat i y =>
    obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · unfold decideLaw
      simp only
      split
      · exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
      · exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
    · exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · exact startDeal_bodyOk hP hO hD h
    · exact ⟨Posted.refl rfl rfl, hP, hO, hD⟩
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    refine ⟨Posted.refl rfl rfl, hP, hO, ?_⟩
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨d, hd, rfl⟩ := ha
    have := hD d hd
    split
    · exact ⟨this.id_lt, this.signers, this.pays_src, this.pays_dst⟩
    · exact this

/-! ## The invariant -/

/-- What every reachable state satisfies, as far as money goes. -/
structure Core (s : State G) : Prop where
  seats : ∃ n, minSeats ≤ n ∧ n ≤ maxSeats ∧ s.turnOrder = List.range n
  seedFrom : ∃ serverSeed nonces, s.seed = combineSeed serverSeed nonces ∧
    s.seedCommitment = commitmentOf serverSeed
  pieces : PiecesOk s
  offers : OffersOk s
  deals : DealsOk s
  books : (genesisBooks G).postAll s.journal = some s.books
  total : ∀ r, s.total r = G.stockOf r

theorem Core.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats) :
    Core (initialState G seats serverSeed nonces) := by
  refine ⟨⟨seats, h1, h2, rfl⟩, ⟨serverSeed, nonces, rfl, rfl⟩, ?_, ?_, ?_, rfl, ?_⟩
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro r
    exact sumOver_genesis _ r

theorem Core.turnOrder_nodup {s : State G} (hc : Core s) : s.turnOrder.Nodup := by
  obtain ⟨n, _, _, h⟩ := hc.seats
  rw [h]
  exact List.nodup_range

/-- Posting keeps the journal and total facts, if the seats stay the same. -/
theorem Core.ledger {s s' : State G} (hc : Core s) (hT : s'.turnOrder = s.turnOrder)
    (hp : Posted s.turnOrder s s') :
    (genesisBooks G).postAll s'.journal = some s'.books ∧ ∀ r, s'.total r = G.stockOf r := by
  obtain ⟨es, hj, hb, hx⟩ := hp
  constructor
  · rw [hj, postAll_append, hc.books]
    exact hb
  · intro r
    have hacc : s'.accounts = s.accounts := by simp [State.accounts, hT]
    rw [total_eq_sumOver, hacc]
    have hsum := sumOver_postAll (accounts_nodup s hc.turnOrder_nodup) hb
      (fun x h => ⟨(mem_accounts s _).mpr (hx x h).1, (mem_accounts s _).mpr (hx x h).2⟩) r
    rw [hsum, ← total_eq_sumOver]
    exact hc.total r

/-- Every accepted event is posted in full between accounts of the game. -/
theorem step_posted {s s' : State G} {e : Event} (hc : Core s) (h : step G s e = .ok s') :
    Posted s.turnOrder s s' ∧ PiecesOk s' ∧ OffersOk s' ∧ DealsOk s' := by
  have hT := step_turnOrder h
  rcases step_view h with ⟨_, h⟩ | ⟨_, hact, s1, hb, hf⟩
  · obtain ⟨b, hbk, rfl⟩ := endTurnNow_ok h
    simp only [startNextTurn_turnOrder] at hT
    refine ⟨⟨_, by simp; rfl, by simpa using hbk, turnEntries_ok hc.pieces hc.deals _⟩, ?_, ?_, ?_⟩
    · intro x hx
      simp only [startNextTurn_pieces] at hx
      simpa using turnPieces_ok hc.pieces _ x hx
    · intro x hx
      simp at hx
    · intro d hd
      have hd' := startNextTurn_deals_sub _ _ hd
      simpa using hc.deals d hd'
  · have ok := body_ok hc.pieces hc.offers hc.deals hact hb
    have f := bodyOf_frame hb
    rcases finish_cases hf with rfl | ⟨w, he⟩
    · refine ⟨Posted.trans ok.posted (Posted.refl rfl rfl), ?_, ?_, ?_⟩
      · intro x hx
        simpa [countAction, f.turnOrder] using ok.pieces x hx
      · intro x hx
        simpa [countAction, f.turnOrder] using ok.offers x hx
      · intro d hd
        simpa [countAction, f.turnOrder] using ok.deals d hd
    · obtain ⟨b, hbk, rfl⟩ := endGame_ok he
      refine ⟨Posted.trans ok.posted ⟨_, rfl, hbk, ?_⟩, ?_, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_flatMap] at hx
        obtain ⟨d, hd, hx⟩ := hx
        have ht : (countAction s1 (seatOf e)).turnOrder = s.turnOrder := f.turnOrder
        have := refundEntries_ok (s := countAction s1 (seatOf e)) (d := d)
          (ht ▸ ok.deals d hd) x hx
        rwa [ht] at this
      · intro x hx
        simpa [countAction, f.turnOrder] using ok.pieces x hx
      · intro x hx
        cases hx
      · intro x hx
        cases hx

theorem Core.step {s s' : State G} {e : Event} (hc : Core s) (h : step G s e = .ok s') :
    Core s' := by
  have hT := step_turnOrder h
  obtain ⟨hp, hP, hO, hD⟩ := step_posted hc h
  obtain ⟨hbooks, htotal⟩ := hc.ledger hT hp
  refine ⟨?_, ?_, hP, hO, hD, hbooks, htotal⟩
  · rw [hT]
    exact hc.seats
  · rw [step_seed h, step_seedCommitment h]
    exact hc.seedFrom

/-- A step only adds to the end of the journal. -/
theorem step_journal_prefix {s s' : State G} {e : Event} (hc : Core s) (h : step G s e = .ok s') :
    s.journal <+: s'.journal := by
  obtain ⟨⟨es, hj, _, _⟩, _⟩ := step_posted hc h
  exact ⟨es, hj.symm⟩

end Charter.Proofs
