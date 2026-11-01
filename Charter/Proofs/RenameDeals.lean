import Charter.Proofs.RenameLaws

/-!
# Renaming: deals, trades and building rules

A deal can name seats, and renaming changes those names. These lemmas show that what a deal owes,
what it forbids and whether it can run are the same after a renaming. They then do the same for the
entries of a round's end and for the checks on placing a piece.
-/

namespace Charter.Renaming

open Charter Charter.Engine

variable (σ : Renaming) {G : GameDef}

/-! ## General facts about lists -/

theorem contains_map_of_inj {α β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (l : List α) (a : α) :
    (l.map f).contains (f a) = l.contains a := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← hf _ _ h]
  · exact fun h => ⟨a, h, rfl⟩

theorem erase_map_of_inj {α β} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (l : List α) (a : α) :
    (l.map f).erase (f a) = (l.erase a).map f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have h' : ¬ f x = f a := fun e => h (hf _ _ e)
      simp [h, h', ih]

/-! ## Payments and deals -/

@[simp] theorem pay_src (p : Pay) : (σ.pay p).src = σ.to p.src := rfl
@[simp] theorem pay_dst (p : Pay) : (σ.pay p).dst = σ.payee p.dst := rfl
@[simp] theorem pay_res (p : Pay) : (σ.pay p).res = p.res := rfl
@[simp] theorem pay_amount (p : Pay) : (σ.pay p).amount = p.amount := rfl

@[simp] theorem payee_account (x : Payee) : (σ.payee x).account = σ.account x.account := by
  cases x <;> rfl

@[simp] theorem deal_title (d : Deal) : (σ.deal d).title = d.title := rfl
@[simp] theorem deal_signers (d : Deal) : (σ.deal d).signers = d.signers.map σ.to := rfl
@[simp] theorem deal_rounds (d : Deal) : (σ.deal d).rounds = d.rounds := rfl
@[simp] theorem deal_exitNotice (d : Deal) : (σ.deal d).exitNotice = d.exitNotice := rfl
@[simp] theorem deal_deposits (d : Deal) :
    (σ.deal d).deposits = d.deposits.map (fun x => (σ.to x.1, x.2)) := rfl
@[simp] theorem deal_terms (d : Deal) : (σ.deal d).terms = d.terms.map σ.term := rfl

@[simp] theorem activeDeal_id (d : ActiveDeal) : (σ.activeDeal d).id = d.id := rfl
@[simp] theorem activeDeal_deal (d : ActiveDeal) : (σ.activeDeal d).deal = σ.deal d.deal := rfl
@[simp] theorem activeDeal_lastRound (d : ActiveDeal) :
    (σ.activeDeal d).lastRound = d.lastRound := rfl
@[simp] theorem activeDeal_startRound (d : ActiveDeal) :
    (σ.activeDeal d).startRound = d.startRound := rfl
@[simp] theorem activeDeal_builtBefore (d : ActiveDeal) :
    (σ.activeDeal d).builtBefore = d.builtBefore := rfl

theorem term_pays (t : Term) : (σ.term t).pays = t.pays.map σ.pay := by
  cases t <;> rfl

theorem allPays_rename (d : Deal) : (σ.deal d).allPays = d.allPays.map σ.pay := by
  simp [Deal.allPays, List.flatMap_map, List.map_flatMap, term_pays]

theorem owedPerRound_rename (d : Deal) (i : Seat) (r : Res) :
    (σ.deal d).owedPerRound (σ.to i) r = d.owedPerRound i r := by
  simp [Deal.owedPerRound, allPays_rename, List.filter_map, Function.comp_def]

theorem depositOf_rename (d : Deal) (i : Seat) (r : Res) :
    (σ.deal d).depositOf (σ.to i) r = d.depositOf i r := by
  simp [Deal.depositOf, List.filter_map, Function.comp_def]

theorem covered_rename (d : Deal) : (σ.deal d).covered G = d.covered G := by
  simp [Deal.covered, owedPerRound_rename, depositOf_rename, Function.comp_def]

/-! ## Whether a deal or a law can run -/

theorem payProblems_rename (s : State G) (d : Deal) (p : Pay) :
    payProblems (σ.state s) (σ.deal d) (σ.pay p) = payProblems s d p := by
  cases hp : p.dst <;> simp [payProblems, hp, payee] <;> rfl

theorem termProblems_rename (s : State G) (d : Deal) (t : Term) :
    termProblems (σ.state s) (σ.deal d) (σ.term t) = termProblems s d t := by
  cases t <;> simp [termProblems, term]

theorem dealProblems_rename (s : State G) (d : Deal) :
    dealProblems (σ.state s) (σ.deal d) = dealProblems s d := by
  have h1 : ((d.deposits.map fun x => (σ.to x.1, x.2)).all fun x =>
      (d.signers.map σ.to).contains x.1) = d.deposits.all fun x => d.signers.contains x.1 := by
    simp [List.all_map, Function.comp_def]
  have h2 : ((d.deposits.map fun x => (σ.to x.1, x.2)).all fun x => G.isRes x.2.1) =
      d.deposits.all fun x => G.isRes x.2.1 := by
    simp [List.all_map, Function.comp_def]
  have h3 : ((d.signers.map σ.to).all (s.turnOrder.map σ.to).contains) =
      d.signers.all s.turnOrder.contains := by
    rw [List.all_map]
    congr 1
    funext x
    exact σ.contains_map_to s.turnOrder x
  simp only [dealProblems, allPays_rename, List.flatMap_map, payProblems_rename, deal_terms,
    termProblems_rename, covered_rename, deal_deposits, deal_signers, h1, h2, h3, state_turnOrder,
    deal_rounds, List.length_map, nodup_map_to]
  rfl

/-- Law checks read only the rules and the laws in force, and a renaming changes neither. -/
theorem clauseProblems_rename (s : State G) (L : Law) (c : Clause) :
    clauseProblems (σ.state s) L c = clauseProblems s L c := by
  cases c <;> rfl

theorem lawProblems_rename (s : State G) (L : Law) :
    lawProblems G (σ.state s) L = lawProblems G s L := by
  have h : clauseProblems (σ.state s) L = clauseProblems s L :=
    funext (σ.clauseProblems_rename s L)
  simp only [lawProblems, h, state_laws, state_turnOrder, List.length_map]
  rfl

/-! ## Payments at a round's end -/

theorem payEntries_rename (id : Nat) (ps : List Pay) :
    State.payEntries id (ps.map σ.pay) = (State.payEntries id ps).map σ.entry := by
  simp [State.payEntries, Function.comp_def, entry, pay]

theorem contains_built (l : List (Seat × PieceKind)) (x : Seat) (k : PieceKind) :
    (l.map fun y => (σ.to y.1, y.2)).contains (σ.to x, k) = l.contains (x, k) := by
  refine contains_map_of_inj (f := fun y : Seat × PieceKind => (σ.to y.1, y.2)) ?_ l (x, k)
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simpa using h

theorem buildsSeenBy_rename (s : State G) (d : ActiveDeal) :
    (σ.state s).buildsSeenBy (σ.activeDeal d) =
      (s.buildsSeenBy d).map fun y => (σ.to y.1, y.2) := by
  simp only [State.buildsSeenBy, state_round, activeDeal_startRound, state_builtThisRound,
    activeDeal_builtBefore]
  by_cases h : (s.round == d.startRound) = true <;> simp only [h, ↓reduceIte, List.map_drop, Bool.false_eq_true]

theorem duePayments_rename (s : State G) :
    (σ.state s).duePayments = s.duePayments.map σ.entry := by
  simp only [State.duePayments, state_deals, List.flatMap_map, List.map_flatMap, activeDeal_deal,
    deal_terms, activeDeal_id]
  congr 1
  funext d
  congr 1
  funext t
  cases t with
  | everyRound ps => exact σ.payEntries_rename d.id ps
  | onBuild x k ps =>
    simp only [term, buildsSeenBy_rename, contains_built]
    split
    · exact σ.payEntries_rename d.id ps
    · rfl
  | noBuild x k spots => rfl
  | noTrade a b => rfl

theorem refundEntries_rename (s : State G) (d : ActiveDeal) :
    (σ.state s).refundEntries (σ.activeDeal d) = (s.refundEntries d).map σ.entry := by
  simp only [State.refundEntries, activeDeal_deal, deal_signers, List.flatMap_map,
    List.map_flatMap, activeDeal_id, balance_deposit, List.map_filterMap]
  congr 1
  funext i
  congr 1
  funext r
  split <;> rfl

theorem refunds_rename (s : State G) :
    (σ.state s).deals.flatMap (σ.state s).refundEntries =
      (s.deals.flatMap s.refundEntries).map σ.entry := by
  simp only [state_deals, List.flatMap_map, List.map_flatMap, refundEntries_rename]

theorem closingDeals_rename (s : State G) :
    (σ.state s).closingDeals = s.closingDeals.map σ.activeDeal := by
  simp only [State.closingDeals, state_round, state_deals, List.filter_map]
  split
  · rfl
  · simp [Function.comp_def]
    rfl

theorem roundEndLawEntries_rename (s : State G) :
    (σ.state s).roundEndLawEntries = s.roundEndLawEntries.map σ.entry := by
  simp only [State.roundEndLawEntries, duePayments_rename, afterPosting_rename]
  exact σ.lawEntries_rename _ .roundEnd

theorem roundEndEntries_rename (s : State G) :
    (σ.state s).roundEndEntries = s.roundEndEntries.map σ.entry := by
  simp only [State.roundEndEntries, duePayments_rename, roundEndLawEntries_rename,
    closingDeals_rename, List.flatMap_map, List.map_append, List.map_flatMap]
  simp only [← List.map_append, afterPosting_rename, refundEntries_rename]

theorem entriesBeforeRoll_rename (s : State G) :
    (σ.state s).entriesBeforeRoll = s.entriesBeforeRoll.map σ.entry := by
  simp only [State.entriesBeforeRoll, isLastTurn_rename, roundEndEntries_rename]
  split <;> rfl

/-! ## Trades and fees -/

theorem bundleEntries_rename (a b : Account) (x : Bundle) (r : Reason) :
    bundleEntries (σ.account a) (σ.account b) x r = (bundleEntries a b x r).map σ.entry := by
  simp [bundleEntries, Function.comp_def, entry]

@[simp] theorem offer_id (o : Offer) : (σ.offer o).id = o.id := rfl
@[simp] theorem offer_src (o : Offer) : (σ.offer o).src = σ.to o.src := rfl
@[simp] theorem offer_to (o : Offer) : (σ.offer o).to = o.to.map σ.to := rfl
@[simp] theorem offer_give (o : Offer) : (σ.offer o).give = o.give := rfl
@[simp] theorem offer_get (o : Offer) : (σ.offer o).get = o.get := rfl

theorem offerEntries_rename (o : Offer) (p : Seat) :
    offerEntries (σ.offer o) (σ.to p) = (offerEntries o p).map σ.entry := by
  simp only [offerEntries, List.map_append, offer_src, offer_give, offer_get]
  rw [← bundleEntries_rename, ← bundleEntries_rename]
  rfl

theorem bankTradeEntries_rename (s : State G) (p : Seat) (give get : Res) :
    (σ.state s).bankTradeEntries (σ.to p) give get = (s.bankTradeEntries p give get).map σ.entry :=
  rfl

theorem tradeBlocked_rename (s : State G) (a b : Seat) :
    (σ.state s).tradeBlocked (σ.to a) (σ.to b) = s.tradeBlocked a b := by
  simp only [State.tradeBlocked, state_deals, List.any_map, Function.comp_def, activeDeal_deal,
    deal_signers, deal_terms]
  congr 1
  funext d
  congr 1
  congr 1
  funext t
  cases t <;> simp [term]

/-! ## Placing a piece -/

@[simp] theorem piece_eq_piece {a b : Piece} : σ.piece a = σ.piece b ↔ a = b := by
  constructor
  · intro h
    cases a; cases b
    simpa [piece] using h
  · exact fun h => h ▸ rfl

theorem contains_piece (l : List Piece) (x : Piece) :
    (l.map σ.piece).contains (σ.piece x) = l.contains x :=
  contains_map_of_inj (fun _ _ h => σ.piece_eq_piece.1 h) l x

theorem pieceAt_isNone (s : State G) (v : Nat) :
    ((σ.state s).pieceAt v).isNone = (s.pieceAt v).isNone := by
  simp [State.pieceAt, List.find?_map, Function.comp_def]

theorem linkTaken_rename (s : State G) (l : Nat × Nat) :
    (σ.state s).linkTaken l = s.linkTaken l := by
  simp [State.linkTaken, Function.comp_def]

theorem reaches_rename (s : State G) (p : Seat) (v : Nat) :
    (σ.state s).reaches (σ.to p) v = s.reaches p v := by
  simp [State.reaches, Function.comp_def]

theorem blockedByDeal_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    (σ.state s).blockedByDeal (σ.to p) k loc = s.blockedByDeal p k loc := by
  simp only [State.blockedByDeal, state_deals, List.any_map, Function.comp_def, activeDeal_deal,
    deal_signers, contains_map_to, deal_terms]
  congr 1
  funext d
  congr 2
  funext t
  cases t <;> simp [term]

theorem placementOk_rename (s : State G) (p : Seat) (d : PieceDef) (loc : Loc) :
    (σ.state s).placementOk (σ.to p) d loc = s.placementOk p d loc := by
  have hc : ∀ k v, (σ.state s).pieces.contains ⟨σ.to p, k, .spot v⟩ =
      s.pieces.contains ⟨p, k, .spot v⟩ := fun k v => σ.contains_piece s.pieces ⟨p, k, .spot v⟩
  unfold State.placementOk
  split <;> simp only [linkTaken_rename, reaches_rename, pieceAt_isNone, hc, State.neighbours]

theorem canPlace_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    (σ.state s).canPlace (σ.to p) k loc = s.canPlace p k loc := by
  simp only [State.canPlace, state_phase, isTurnOf_rename, state_actionsThisTurn_to, state_rules]
  cases s.rules.piece? k with
  | none => rfl
  | some d => simp only [affords_rename, placementOk_rename, countOf_rename, blockedByDeal_rename]

theorem costEntries_rename (s : State G) (p : Seat) (k : PieceKind) :
    (σ.state s).costEntries (σ.to p) k = (s.costEntries p k).map σ.entry := by
  simp [State.costEntries, Function.comp_def, entry]

theorem placedPieces_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    (σ.state s).placedPieces (σ.to p) k loc = (s.placedPieces p k loc).map σ.piece := by
  have he : ∀ old v, (s.pieces.map σ.piece).erase ⟨σ.to p, old, .spot v⟩ =
      (s.pieces.erase ⟨p, old, .spot v⟩).map σ.piece := fun old v =>
    erase_map_of_inj (fun _ _ h => σ.piece_eq_piece.1 h) s.pieces ⟨p, old, .spot v⟩
  simp only [State.placedPieces, state_rules, List.map_append]
  congr 1
  split <;> simp [he]

theorem setupPlacementOk_rename (s : State G) (p : Seat) (d : PieceDef) (loc : Loc) :
    (σ.state s).setupPlacementOk (σ.to p) d loc = s.setupPlacementOk p d loc := by
  unfold State.setupPlacementOk
  split <;> simp only [pieceAt_isNone, State.neighbours, placementOk_rename]

theorem canSetupPlace_rename (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) :
    (σ.state s).canSetupPlace (σ.to p) k loc = s.canSetupPlace p k loc := by
  simp only [State.canSetupPlace, state_phase, isTurnOf_rename, state_actionsThisTurn_to,
    state_rules]
  cases s.rules.piece? k with
  | none => rfl
  | some d => simp only [setupPlacementOk_rename, countOf_rename]

end Charter.Renaming
