import Charter.Proofs.Main

/-!
# Bank trades and setup placements

A bank trade posts exactly when the seat can pay the rate and the bank can pay 1, because the two
resources differ. A setup placement moves no resources, since no deal, offer or proposal can exist
before the first round. The bank rate is at least 2 in every reachable state, because the game's own
rate and every law's rate are checked.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## The bank rate is at least 2 -/

/-- The rate this clause sets is at least 2. -/
def ClauseRateOk : Clause → Prop
  | .setBankRate n => 2 ≤ n
  | _ => True

theorem clause_rate {R : Rules} {c : Clause} (hR : 2 ≤ R.bankRate) (hc : ClauseRateOk c) :
    2 ≤ (c.applyTo R).bankRate := by
  cases c with
  | setBankRate n => exact hc
  | setCost _ _ => exact hR
  | setPoints _ _ => exact hR
  | newPiece _ => exact hR
  | setWorth _ _ => exact hR
  | onHarvest _ => exact hR
  | onBuild _ _ => exact hR
  | onRoundEnd _ => exact hR
  | onRoll _ => exact hR
  | now _ => exact hR
  | endGame => exact hR
  | repeal _ => exact hR

theorem law_rate {R : Rules} {L : Law} (hR : 2 ≤ R.bankRate)
    (hL : ∀ c ∈ L.clauses, ClauseRateOk c) : 2 ≤ (L.applyTo R).bankRate := by
  unfold Law.applyTo
  generalize L.clauses = cs at hL
  induction cs generalizing R with
  | nil => exact hR
  | cons c t ih =>
    simp only [List.foldl_cons]
    exact ih (clause_rate hR (hL c (by simp))) (fun x hx => hL x (by simp [hx]))

theorem rules_rate {laws : List (Nat × Law)} (hG : G.Valid)
    (hL : ∀ x ∈ laws, ∀ c ∈ x.2.clauses, ClauseRateOk c) : 2 ≤ (rulesFrom G laws).bankRate := by
  have h0 : 2 ≤ G.bankRate := by
    have hG := valid_shape hG
    simp only [GameDef.shapeChecks, Bool.and_eq_true, decide_eq_true_eq] at hG
    exact hG.1.2
  unfold rulesFrom
  have h0' : 2 ≤ ({ pieces := G.pieces, bankRate := G.bankRate, worth := [] } : Rules).bankRate := h0
  generalize ({ pieces := G.pieces, bankRate := G.bankRate, worth := [] } : Rules) = R at h0'
  induction laws generalizing R with
  | nil => exact h0'
  | cons x t ih =>
    simp only [List.foldl_cons]
    exact ih (fun y hy => hL y (by simp [hy])) _ (law_rate h0' (hL x (by simp)))

/-- A law with no problems sets only a rate of at least 2. -/
theorem lawProblems_rate {s : State G} {L : Law} (h : lawProblems G s L = []) :
    ∀ c ∈ L.clauses, ClauseRateOk c := by
  simp only [lawProblems, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  intro c hc
  have hp := h.2 c hc
  cases c with
  | setBankRate n =>
    simp only [clauseProblems] at hp
    exact ite_nil (c := 2 ≤ n) hp
  | setCost _ _ => trivial
  | setPoints _ _ => trivial
  | newPiece _ => trivial
  | setWorth _ _ => trivial
  | onHarvest _ => trivial
  | onBuild _ _ => trivial
  | onRoundEnd _ => trivial
  | onRoll _ => trivial
  | now _ => trivial
  | endGame => trivial
  | repeal _ => trivial

theorem founding_rates {n : Nat} (Ls : List Law) : ∀ (laws : List (Nat × Law)) (id : Nat),
    G.foundingOkFrom n laws id Ls = true →
    (∀ x ∈ laws, ∀ c ∈ x.2.clauses, ClauseRateOk c) →
    ∀ x ∈ enactAll laws id Ls, ∀ c ∈ x.2.clauses, ClauseRateOk c := by
  induction Ls with
  | nil => intro laws _ _ hf; exact hf
  | cons L t ih =>
    intro laws id h hf
    simp only [GameDef.foundingOkFrom, Bool.and_eq_true] at h
    refine ih _ _ h.2 ?_
    intro x hx
    rcases mem_enact hx with hm | rfl
    · exact hf x hm
    · exact lawProblems_rate (List.isEmpty_iff.mp h.1)

/-- Every law in force sets a bank rate of at least 2, if it sets one at all. -/
theorem laws_rate (hG : G.Valid) {s : State G} (hs : Reachable G s) :
    ∀ x ∈ s.laws, ∀ c ∈ x.2.clauses, ClauseRateOk c := by
  induction hs with
  | start seats serverSeed nonces h1 h2 _ =>
    exact founding_rates _ _ _ (valid_founding hG h1 h2) (by simp)
  | @next s s' e _ h ih =>
    by_cases hsame : s'.laws = s.laws
    · rw [hsame]
      exact ih
    · obtain ⟨id, L, hprob, hl⟩ := laws_change_valid h hsame
      intro x hx
      rw [hl] at hx
      rcases mem_enact hx with hm | rfl
      · exact ih x hm
      · exact lawProblems_rate hprob

theorem bankRate_ge (hG : G.Valid) {s : State G} (hs : Reachable G s) : 2 ≤ s.rules.bankRate :=
  rules_rate hG (laws_rate hG hs)

/-! ## Nothing is open in setup -/

/-- Only a place move or the end of a turn is accepted in setup. -/
theorem setup_event {s s' : State G} {e : Event} (hPhase : s.phase = .setup)
    (h : Engine.step G s e = .ok s') :
    EndsTurn s e ∨ ∃ p k loc, e = .move p (.place k loc) := by
  rcases step_view h with ⟨hend, _⟩ | ⟨_, _, s1, hb, _⟩
  · exact Or.inl hend
  · refine Or.inr ?_
    cases e with
    | forceEndTurn => cases hb
    | propose seat b =>
      obtain ⟨hp, _⟩ := proposeBody_ok hb
      simp [hPhase] at hp
    | vote seat i y =>
      have hb' : voteBody s seat i y = .ok s1 := hb
      obtain ⟨hp, _⟩ := voteBody_ok hb'
      simp [hPhase] at hp
    | sign seat i =>
      obtain ⟨hp, _⟩ := signBody_ok hb
      simp [hPhase] at hp
    | exit seat i =>
      obtain ⟨hp, _⟩ := exitBody_ok hb
      simp [hPhase] at hp
    | move p m =>
      cases m with
      | place k loc => exact ⟨p, k, loc, rfl⟩
      | endTurn => cases hb
      | bankTrade a b =>
        obtain ⟨hp, _⟩ := bankTradeBody_ok hb
        simp [hPhase] at hp
      | offer t a b =>
        obtain ⟨hp, _⟩ := offerBody_ok hb
        simp [hPhase] at hp
      | accept i =>
        obtain ⟨hp, _⟩ := acceptBody_ok hb
        simp [hPhase] at hp
      | cancel i =>
        obtain ⟨hp, _⟩ := cancelBody_ok hb
        simp [hPhase] at hp
      | declare r n =>
        obtain ⟨⟨hp, _⟩, _⟩ := declareBody_ok hb
        simp [hPhase] at hp

/-- The phase never goes back to setup. -/
theorem setup_only_from_setup {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hs' : s'.phase = .setup) : s.phase = .setup := by
  have he := step_not_ended h
  by_cases hend : EndsTurn s e
  · have hm := (turn_moved_on hend h).2
    cases hp : s.phase with
    | setup => rfl
    | ended => exact absurd hp he
    | actions =>
      unfold nextStage at hm
      rw [hp] at hm
      by_cases hl : s.isLastTurn = true
      · by_cases hr : G.rounds ≤ s.round <;> simp [hl, hr, hs'] at hm
      · simp [hl, hs'] at hm
  · rcases phase_by_turn_or_win h hend with hc | ⟨hc, _⟩
    · rw [← hc]; exact hs'
    · rw [hs'] at hc; cases hc

/-- No deal, offer or proposal exists in setup. -/
theorem setup_is_empty (hG : G.Valid) {s : State G} (hs : Reachable G s) (hPhase : s.phase = .setup) :
    s.deals = [] ∧ s.offers = [] ∧ s.openProposals = [] := by
  induction hs with
  | start seats serverSeed nonces _ _ _ => exact ⟨rfl, rfl, rfl⟩
  | @next s s' e hr h ih =>
    have hp := setup_only_from_setup h hPhase
    obtain ⟨hd, ho, hq⟩ := ih hp
    have hi := (hr.inv hG).ids
    have hev := setup_event hp h
    have notProp : ∀ seat b, e ≠ .propose seat b := by
      rintro seat b rfl
      rcases hev with he | ⟨_, _, _, he⟩
      · exact he
      · cases he
    have notOffer : ∀ q to give get, e ≠ .move q (.offer to give get) := by
      rintro q to give get rfl
      rcases hev with he | ⟨_, _, _, he⟩
      · exact he
      · cases he
    have notSign : ∀ seat id, e ≠ .sign seat id := by
      rintro seat id rfl
      rcases hev with he | ⟨_, _, _, he⟩
      · exact he
      · cases he
    refine ⟨?_, ?_, ?_⟩
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro d hdm
      rcases (deals_kept hi h).1 d hdm with ⟨seat, id, _, _, he, _⟩ | ⟨d0, hd0, _⟩
      · exact notSign seat id he
      · simp [hd] at hd0
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro o hom
      rcases offers_kept h o hom with h0 | ⟨to, give, get, he, _⟩
      · simp [ho] at h0
      · exact notOffer _ to give get he
    · apply List.eq_nil_iff_forall_not_mem.mpr
      intro q hqm
      rcases (proposals_kept hi h).1 q hqm with ⟨seat, he, _⟩ | ⟨p0, hp0, _⟩
      · exact notProp seat _ he
      · simp [hq] at hp0

/-! ## A bank trade -/

theorem step_bankTrade {s s' : State G} {p : Seat} {give get : Res}
    (h : Engine.step G s (.move p (.bankTrade give get)) = .ok s') :
    s.phase = .actions ∧ s.isTurnOf p = true ∧ canAct s p = true ∧ give ≠ get ∧
    G.isRes give = true ∧ G.isRes get = true ∧
    ∃ b, s.books.postAll (s.bankTradeEntries p give get) = some b ∧
      checkWin (countAction { s with
        books := b, journal := s.journal ++ s.bankTradeEntries p give get } p) = .ok s' := by
  obtain ⟨hc, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  have hb' : bankTradeBody s p give get = .ok s1 := hb
  obtain ⟨h1, h2, h3, h4, h5, hr⟩ := bankTradeBody_ok hb'
  obtain ⟨b, hbk, rfl⟩ := record_ok hr
  exact ⟨h1, h2, hc, h3, h4, h5, b, hbk, hf⟩

theorem outflow_trade_seat (s : State G) (p : Seat) {give get : Res} (hne : give ≠ get) :
    outflow (s.bankTradeEntries p give get) (.player p) give = s.rules.bankRate ∧
    outflow (s.bankTradeEntries p give get) (.player p) get = 0 ∧
    inflow (s.bankTradeEntries p give get) (.player p) give = 0 ∧
    inflow (s.bankTradeEntries p give get) (.player p) get = 1 ∧
    outflow (s.bankTradeEntries p give get) .bank get = 1 ∧
    inflow (s.bankTradeEntries p give get) .bank get = 0 := by
  simp [State.bankTradeEntries, outflow, inflow, hne, hne.symm]

theorem trade_outflow_le {s : State G} {p : Seat} {give get : Res}
    (hne : give ≠ get) (h1 : s.rules.bankRate ≤ s.balance (.player p) give)
    (h2 : 1 ≤ s.balance .bank get) (a : Account) (r : Res) :
    outflow (s.bankTradeEntries p give get) a r ≤ s.books a r := by
  simp only [State.bankTradeEntries, outflow_cons, outflow_nil]
  by_cases ha : Account.player p = a ∧ give = r
  · obtain ⟨rfl, rfl⟩ := ha
    have h1' : s.rules.bankRate ≤ s.books (.player p) give := h1
    simpa [hne.symm] using h1'
  · by_cases hb : Account.bank = a ∧ get = r
    · obtain ⟨rfl, rfl⟩ := hb
      have h2' : 1 ≤ s.books .bank get := h2
      simpa using h2'
    · simp [ha, hb]

/-- What a bank trade's entries post to. -/
theorem trade_posts_iff (s : State G) (p : Seat) {give get : Res} (hne : give ≠ get) :
    (∃ b, s.books.postAll (s.bankTradeEntries p give get) = some b) ↔
      s.rules.bankRate ≤ s.balance (.player p) give ∧ 1 ≤ s.balance .bank get := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨h1, _, _, _, h5, h6⟩ := outflow_trade_seat s p hne
    have ha := postAll_balance hb (.player p) give
    have hc := postAll_balance hb .bank get
    rw [h1] at ha
    rw [h5, h6] at hc
    obtain ⟨_, _, h3, _, _, _⟩ := outflow_trade_seat s p hne
    rw [h3] at ha
    simp only [State.balance]
    omega
  · rintro ⟨h1, h2⟩
    apply postAll_some
    · intro x hx
      simp only [State.bankTradeEntries, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
    · exact trade_outflow_le hne h1 h2

/-- A trade leaves every deposit alone, so the refunds it may cause read the same amounts. -/
theorem refundEntries_after_trade {s : State G} {p : Seat} {give get : Res} {b : Books}
    (hb : s.books.postAll (s.bankTradeEntries p give get) = some b) (t : State G)
    (ht : t.books = b) : t.refundEntries = s.refundEntries := by
  have hdep : ∀ k i r, b (.deposit k i) r = s.books (.deposit k i) r := by
    intro k i r
    have := postAll_balance hb (.deposit k i) r
    simpa [State.bankTradeEntries, outflow, inflow, List.filter_cons] using this
  funext d
  simp only [State.refundEntries, State.balance, ht, hdep]
  rfl

theorem outflow_refunds_seat (s : State G) (L : List ActiveDeal) (p : Seat) (r : Res) :
    outflow (L.flatMap s.refundEntries) (.player p) r = 0 := by
  apply outflow_eq_zero'
  intro x hx h1 _
  obtain ⟨d, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨_, k, i, h2, _⟩ := refundEntries_form hx
  rw [h1] at h2
  cases h2

theorem bank_trade_accepted (hG : G.Valid) {s : State G} (hi : IdInv s) (p : Seat) (give get : Res) :
    (∃ s', Engine.step G s (.move p (.bankTrade give get)) = .ok s') ↔
      BankTradeIsAllowed s p give get := by
  constructor
  · rintro ⟨s', h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, b, hb, _⟩ := step_bankTrade h
    obtain ⟨h7, h8⟩ := (trade_posts_iff s p h4).mp ⟨b, hb⟩
    refine ⟨h1, by simpa [State.isTurnOf] using h2, (canAct_mem h3).2, h4, h5, h6, h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hturn : s.isTurnOf p = true := by simpa [State.isTurnOf] using h2
    have hca := canAct_of (isTurnOf_mem hturn) h3
    obtain ⟨b, hb⟩ := (trade_posts_iff s p h4).mpr ⟨h7, h8⟩
    obtain ⟨s', hs', _⟩ := checkWin_some hG (countAction { s with
        books := b, journal := s.journal ++ s.bankTradeEntries p give get } p)
      hi.deal_nodup hi.signers_nodup
    have hbody : bankTradeBody s p give get = .ok { s with
        books := b, journal := s.journal ++ s.bankTradeEntries p give get } := by
      have hc1 : (!(s.phase == .actions && s.isTurnOf p)) = false := by simp [h1, hturn]
      have hc2 : (!(give != get && G.isRes give && G.isRes get)) = false := by simp [h4, h5, h6]
      unfold bankTradeBody
      simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte]
      exact record_some hb
    refine ⟨s', ?_⟩
    unfold Engine.step
    rw [ite_eq_right_of_eq_false _ _ (by simp [h1])]
    simp only [actThenCheckWin, act, hca, ↓reduceIte, moveBody, hbody]
    exact hs'

theorem bank_trade_exact {s s' : State G} {p : Seat} {give get : Res}
    (h : Engine.step G s (.move p (.bankTrade give get)) = .ok s') :
    BankTradeIsExact s s' p give get := by
  obtain ⟨hph, -, -, hne, -, -, b, hb, hf⟩ := step_bankTrade h
  obtain ⟨o1, o2, i1, i2, -, -⟩ := outflow_trade_seat s p hne
  have ha := postAll_balance hb (.player p) give
  have hc := postAll_balance hb (.player p) get
  rw [o1, i1] at ha
  rw [o2, i2] at hc
  refine ⟨?_, ?_, ?_⟩
  · rcases checkWin_ok hf with ⟨rfl, -⟩ | ⟨w, hw⟩
    · rfl
    · obtain ⟨-, -, rfl⟩ := endGame_ok hw
      rfl
  · intro hn
    rcases checkWin_ok hf with ⟨rfl, -⟩ | ⟨w, hw⟩
    · refine ⟨newEntries_of rfl, ?_, ?_, rfl⟩
      · simpa [State.balance, countAction] using ha
      · simpa [State.balance, countAction] using hc
    · obtain ⟨_, _, rfl⟩ := endGame_ok hw
      exact absurd rfl hn
  · intro hend
    rcases checkWin_ok hf with ⟨rfl, -⟩ | ⟨w, hw⟩
    · simp [countAction, hph] at hend
    · obtain ⟨b2, hb2, hs'⟩ := endGame_ok hw
      have hfun := refundEntries_after_trade hb (countAction { s with
        books := b, journal := s.journal ++ s.bankTradeEntries p give get } p) rfl
      have hbk : s'.books = b2 := by rw [hs']
      simp only [countAction] at hb2 hfun hs'
      rw [hfun] at hb2 hs'
      have ra := postAll_balance hb2 (.player p) give
      have rc := postAll_balance hb2 (.player p) get
      rw [outflow_refunds_seat] at ra rc
      have ina : inflow (s.deals.flatMap s.refundEntries) (.player p) give = refundsTo s p give := rfl
      have inc : inflow (s.deals.flatMap s.refundEntries) (.player p) get = refundsTo s p get := rfl
      rw [ina] at ra
      rw [inc] at rc
      refine ⟨newEntries_of (by rw [hs']; simp [List.append_assoc]), ?_, ?_, ?_⟩
      · simp only [State.balance, hbk]
        omega
      · simp only [State.balance, hbk]
        omega
      · generalize (bestSeat _ _).getD w = wn at hs'
        subst hs'
        exact ⟨wn, rfl⟩

/-! ## A setup placement -/

theorem step_setup {s s' : State G} {p : Seat} {k : PieceKind} {loc : Loc}
    (hPhase : s.phase = .setup) (h : Engine.step G s (.move p (.place k loc)) = .ok s') :
    s.canSetupPlace p k loc = true ∧
      checkWin (countAction { s with pieces := s.placedPieces p k loc } p) = .ok s' := by
  obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  have hb' : placeBody s p k loc = .ok s1 := hb
  rcases placeBody_ok hb' with ⟨_, h1⟩ | ⟨h2, _⟩
  · obtain ⟨hc, rfl⟩ := setupBody_ok h1
    exact ⟨hc, hf⟩
  · rw [hPhase] at h2
    cases h2

theorem setupSpot_iff (s : State G) (p : Seat) (d : PieceDef) (loc : Loc) :
    s.setupPlacementOk p d loc = true ↔ FitsInSetup s p d loc := by
  unfold State.setupPlacementOk FitsInSetup
  cases d.placement <;> cases loc <;>
    first
    | exact Iff.rfl
    | simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

theorem canSetupPlace_iff (s : State G) (hPhase : s.phase = .setup) (p : Seat) (k : PieceKind)
    (loc : Loc) : s.canSetupPlace p k loc = true ↔ SetupPlacementIsAllowed s p k loc := by
  simp only [State.canSetupPlace, hPhase, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    State.isTurnOf, SetupPlacementIsAllowed, true_and]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    split at h4
    · rename_i d hd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
      exact ⟨d, hd, h4.2, (setupSpot_iff s p d loc).mp h4.1⟩
    · cases h4
  · rintro ⟨h1, h2, h3, d, hd, h4, h5⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
    simp only [hd, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(setupSpot_iff s p d loc).mpr h5, h4⟩

theorem setup_accepted (hG : G.Valid) {s : State G} (hi : IdInv s) (hPhase : s.phase = .setup)
    (p : Seat) (k : PieceKind) (loc : Loc) :
    (∃ s', Engine.step G s (.move p (.place k loc)) = .ok s') ↔
      SetupPlacementIsAllowed s p k loc := by
  rw [← canSetupPlace_iff s hPhase]
  constructor
  · rintro ⟨s', h⟩
    exact (step_setup hPhase h).1
  · intro hc
    have hparts := (canSetupPlace_iff s hPhase p k loc).mp hc
    obtain ⟨h1, h2, _⟩ := hparts
    have hturn : s.isTurnOf p = true := by simpa [State.isTurnOf] using h1
    have hca := canAct_of (isTurnOf_mem hturn) h2
    obtain ⟨s', hs', _⟩ := checkWin_some hG (countAction { s with pieces := s.placedPieces p k loc } p)
      hi.deal_nodup hi.signers_nodup
    refine ⟨s', ?_⟩
    have hbody : setupBody s p k loc = .ok { s with pieces := s.placedPieces p k loc } := by
      unfold setupBody
      simp only [hc, ↓reduceIte]
    have hpb : placeBody s p k loc = setupBody s p k loc := by
      unfold placeBody
      rw [hPhase]
    unfold Engine.step
    rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
    simp only [actThenCheckWin, act, hca, ↓reduceIte, moveBody, hpb, hbody]
    exact hs'

theorem setup_exact (hG : G.Valid) {s s' : State G} (hs : Reachable G s) (hPhase : s.phase = .setup)
    {p : Seat} {k : PieceKind} {loc : Loc} (h : Engine.step G s (.move p (.place k loc)) = .ok s') :
    SetupPlacementIsExact s s' p k loc := by
  obtain ⟨-, hf⟩ := step_setup hPhase h
  obtain ⟨hd, ho, hq⟩ := setup_is_empty hG hs hPhase
  have hplain : (∀ old, (s.rules.piece? k).map (·.placement) ≠ some (.upgrade old)) →
      s.placedPieces p k loc = s.pieces ++ [⟨p, k, loc⟩] := by
    intro hn
    unfold State.placedPieces
    simp only
    split
    · exact absurd (by assumption) (hn _)
    · rfl
  rcases checkWin_ok hf with ⟨rfl, _⟩ | ⟨w, hw⟩
  · refine ⟨rfl, hplain, newEntries_nil rfl, rfl, fun _ => rfl, fun hend => ?_⟩
    simp [countAction, hPhase] at hend
  · obtain ⟨b, hb, hs'⟩ := endGame_ok hw
    have hbe : b = s.books := by
      simp only [countAction, hd, List.flatMap_nil, Books.postAll, Option.some.injEq] at hb
      exact hb.symm
    subst hbe
    have key : s' = { s with
        pieces := s.placedPieces p k loc
        actionsThisTurn := fun q => if q = p then s.actionsThisTurn q + 1 else s.actionsThisTurn q
        eventsApplied := s.eventsApplied + 1
        phase := .ended
        winner := s'.winner } := by
      subst hs'
      simp only [countAction, hd, ho, hq, List.flatMap_nil, List.append_nil]
    obtain ⟨wn, hwn⟩ : ∃ wn, s'.winner = some wn := ⟨_, by rw [hs']⟩
    rw [hwn] at key
    subst key
    exact ⟨rfl, hplain, newEntries_nil rfl, rfl, fun hn => absurd rfl hn, fun _ => ⟨wn, rfl⟩⟩

/-- `bank_trades_and_setup_are_exact`. -/
theorem bank_trades_and_setup_are_exact (G : GameDef) (hG : G.Valid) (s : State G)
    (hs : Reachable G s) (p : Seat) :
    2 ≤ s.rules.bankRate ∧
    (∀ give get,
      ((∃ s', Engine.step G s (.move p (.bankTrade give get)) = .ok s') ↔
        BankTradeIsAllowed s p give get) ∧
      ∀ s', Engine.step G s (.move p (.bankTrade give get)) = .ok s' →
        BankTradeIsExact s s' p give get) ∧
    (∀ k loc, s.phase = .setup →
      ((∃ s', Engine.step G s (.move p (.place k loc)) = .ok s') ↔
        SetupPlacementIsAllowed s p k loc) ∧
      ∀ s', Engine.step G s (.move p (.place k loc)) = .ok s' →
        SetupPlacementIsExact s s' p k loc) := by
  have hi := (hs.inv hG).ids
  exact ⟨bankRate_ge hG hs,
    fun give get => ⟨bank_trade_accepted hG hi p give get, fun _ h => bank_trade_exact h⟩,
    fun k loc hPhase => ⟨setup_accepted hG hi hPhase p k loc,
      fun _ h => setup_exact hG hs hPhase h⟩⟩

end Charter.Proofs
