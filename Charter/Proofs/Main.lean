import Charter.Proofs.Invariant

/-!
# The commandments, proved

Each theorem has the statement of the theorem with the same name in `Constitution.lean` or
`Constitution/Supporting.lean`, with its named parts written out in full, and with `Inv G s` in place
of `Reachable G s`. Those files use these theorems as their proofs, so the kernel checks that they
prove exactly what the constitution states.
-/

namespace Charter.Proofs

open Charter Charter.Engine

theorem I_nothing_from_nothing (G : GameDef) (_hG : G.Valid) (s : State G)
    (hs : Inv G s) (r : Res) :
    (genesisBooks G).postAll s.journal = some s.books ∧
    s.total r = G.stockOf r ∧
    ∀ e s', Engine.step G s e = .ok s' → s.journal <+: s'.journal :=
  ⟨hs.core.books, hs.core.total r, fun _ _ h => step_journal_prefix hs.core h⟩

theorem III_only_the_majority (G : GameDef) (hG : G.Valid) (s s' : State G)
    (hs : Inv G s) :
    (∀ e, Engine.step G s e = .ok s' → s'.laws ≠ s.laws →
      ∃ seat id p L,
        e = .vote seat id true ∧ s.openProposal? id = some p ∧ p.body = .law L ∧
        seat ∈ s.turnOrder ∧ (p.votes.map (·.1)).contains seat = false ∧
        (p.withVote seat true).hasMajority s.turnOrder.length ∧
        s'.laws = enact s.laws id L) ∧
    (∀ seat id p L,
      s.phase = .actions → seat ∈ s.turnOrder → s.openProposal? id = some p →
      p.body = .law L → (p.votes.map (·.1)).contains seat = false →
      s.actionsThisTurn seat < maxActionsPerTurn →
      (p.withVote seat true).hasMajority s.turnOrder.length → lawProblems G s L = [] →
      ∃ s'', Engine.step G s (.vote seat id true) = .ok s'' ∧ s''.laws = enact s.laws id L) ∧
    (∀ p ∈ s.openProposals, (p.votes.map (·.1)).Nodup ∧ p.signed.Nodup ∧
      (∀ x ∈ p.votes, x.1 ∈ s.turnOrder) ∧ ∀ i ∈ p.signed, i ∈ s.turnOrder) ∧
    ProposalIdsAreUnique s ∧
    (∀ e, Engine.step G s e = .ok s' → ProposalsKept s s' e) ∧
    (∀ seat id p L yes,
      s.phase = .actions → seat ∈ s.turnOrder → s.openProposal? id = some p →
      p.body = .law L → (p.votes.map (·.1)).contains seat = false →
      s.actionsThisTurn seat < maxActionsPerTurn →
      ∃ s'', Engine.step G s (.vote seat id yes) = .ok s'') ∧
    (∀ e, Engine.step G s e = .ok s' → SeatsStayFixed s s') ∧
    (∀ e, Engine.step G s e = .ok s' → ActionsAreCountedExactly s s' e) ∧
    (∀ e, Engine.step G s e = .ok s' → PhaseChangesOnlyByTurnOrWin s s' e) :=
  ⟨fun _ h hne => laws_change h hne,
    fun seat id p L h1 h2 h3 h4 h5 h6 h7 h8 =>
      majority_passes hG hs.ids seat id p L h1 h2 h3 h4 h5 h6 h7 h8,
    fun p hp => ⟨hs.ids.votes_nodup p hp, hs.ids.signed_nodup p hp, hs.kept.votes_seated p hp,
      hs.kept.signed_seated p hp⟩,
    hs.ids.prop_nodup,
    fun _ h => proposals_kept hs.ids h,
    fun seat id p L yes h1 h2 h3 h4 h5 h6 =>
      vote_accepted hG hs.ids seat id p L yes h1 h2 h3 h4 h5 h6,
    fun _ h => step_turnOrder h,
    fun _ h => actions_counted h,
    fun _ h => phase_by_turn_or_win h⟩

theorem IV_promises_are_paid_up_front (G : GameDef) (_hG : G.Valid) (s : State G)
    (hs : Inv G s) :
    (∀ d ∈ s.deals, ∀ i r, s.worstCase d i r ≤ s.balance (.deposit d.id i) r) ∧
    (∀ e s', Engine.step G s e = .ok s' → EndsTurn s e → s.isLastTurn = true →
      (newEntries s s').filter (·.reason == .dealPayment) = s.duePayments) ∧
    (∀ e s', Engine.step G s e = .ok s' → BuildsRecorded s s' e) :=
  ⟨hs.cover, fun _ _ h hend hl => payments_exact hend h hl, fun _ _ h => builds_recorded h⟩

theorem V_your_money_is_yours (G : GameDef) (_hG : G.Valid) (s s' : State G) (e : Event)
    (hs : Inv G s) (h : Engine.step G s e = .ok s') :
    OffersKept s s' e ∧
    AcceptedOffersAreExact s s' e ∧
    ∀ x ∈ newEntries s s',
    (∀ k i, x.dst = .deposit k i → FundsDeal s s' e x k i) ∧
    (∀ k i, x.src = .deposit k i →
      x.reason = .refund ∨
      (x.reason = .dealPayment ∧ ∃ d ∈ s.deals, d.id = k ∧ ∃ p ∈ d.deal.allPays,
        p.src = i ∧ p.res = x.res ∧ p.amount = x.amount ∧ x.dst = p.dst.account)) ∧
    (x.reason = .dealPayment →
      EndsTurn s e ∧ s.isLastTurn = true ∧ ∃ k i, x.src = .deposit k i) ∧
    (x.reason = .refund → ∃ k i, x.src = .deposit k i ∧ x.dst = .player i ∧
      (∃ d ∈ s.deals, d.id = k) ∧ ∀ d' ∈ s'.deals, d'.id ≠ k) ∧
    (∀ i, x.src = .player i →
      (x.reason = .cost ∧ ∃ k loc, e = .move i (.place k loc) ∧ x ∈ s.costEntries i k) ∨
      (x.reason = .trade ∧
        ((∃ give get, e = .move i (.bankTrade give get) ∧ x ∈ s.bankTradeEntries i give get) ∨
         (∃ p id o, e = .move p (.accept id) ∧ s.offers.find? (·.id == id) = some o ∧
           (i = o.src ∨ i = p) ∧ x ∈ offerEntries o p))) ∨
      (x.reason = .lawFee ∧ ∃ L, e = .propose i (.law L) ∧ x ∈ lawFeeEntries G i) ∨
      (∃ k, FundsDeal s s' e x k i) ∨
      (x.reason = .lawEffect ∧
        ((∃ b k loc, e = .move b (.place k loc) ∧
           x ∈ lawEntries (s.afterPosting (s.costEntries b k)) (.build b k)) ∨
         (EndsTurn s e ∧
           (x ∈ s.roundEndLawEntries ∨
            x ∈ rollEntries (s.afterPosting s.entriesBeforeRoll)
              (rollAt G s.seed s.rollsMade)))))) ∧
    MoneyLeavesBankOnlyFor s e x := by
  refine ⟨offers_kept h, accepted_offers_exact hs.noPending h, fun x hx => ?_⟩
  have hv := step_vconj hs.ids h hx
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, step_bank h hx⟩

theorem VI_every_deal_ends (G : GameDef) (_hG : G.Valid) (s : State G) (hs : Inv G s) :
    (∀ d ∈ s.deals, d.startRound ≤ s.round ∧ d.lastRound + 1 ≤ d.startRound + d.deal.rounds) ∧
    (∀ d ∈ s.deals, s.round ≤ d.lastRound) ∧
    (∀ e s', Engine.step G s e = .ok s' → DealsKept s s' e) ∧
    (∀ d ∈ s.deals, ∀ i ∈ d.deal.signers, s.phase = .actions →
      s.actionsThisTurn i < maxActionsPerTurn →
      ∃ s', Engine.step G s (.exit i d.id) = .ok s' ∧
        ∀ d' ∈ s'.deals, d'.id = d.id → d'.lastRound ≤ s.round + d.deal.exitNotice) ∧
    (∀ e s', Engine.step G s e = .ok s' → ∀ d ∈ s.deals, (∀ d' ∈ s'.deals, d'.id ≠ d.id) →
      ∀ i r, s'.balance (.deposit d.id i) r = 0) ∧
    (∀ p k loc, s.blockedByDeal p k loc = true →
      ∃ d ∈ s.deals, p ∈ d.deal.signers ∧ ∃ spots, Term.noBuild p k spots ∈ d.deal.terms) ∧
    (∀ a b, s.tradeBlocked a b = true →
      ∃ d ∈ s.deals, ∃ x y, Term.noTrade x y ∈ d.deal.terms ∧ x ∈ d.deal.signers ∧
        ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) ∧
    (∀ e s', Engine.step G s e = .ok s' → BlockedTradesAreRejected s e) := by
  refine ⟨hs.kept.deal_start, hs.ids.deal_round, fun _ _ h => deals_kept hs.ids h, ?_, ?_,
    blocked_build_has_term s, blocked_trade_has_term s, fun _ _ h => blocked_trades_rejected h⟩
  · intro d hd i hi h1 h2
    exact exit_accepted hs.core hs.ids.deal_nodup hd hi h1 h2
  · intro e s' h d hd hgone i r
    exact deal_ended_empty hs.deposits hs.core hs.ids h hd hgone i r

theorem VII_prices_are_real (G : GameDef) (hG : G.Valid) (s : State G) (hs : Inv G s)
    (p : Seat) (k : PieceKind) (loc : Loc) (hPhase : s.phase = .actions) :
    ((∃ s', Engine.step G s (.move p (.place k loc)) = .ok s') ↔ s.canPlace p k loc = true) ∧
    ∀ s', Engine.step G s (.move p (.place k loc)) = .ok s' →
      s'.pieces = s.placedPieces p k loc ∧
      ∃ refunds, newEntries s s' =
          s.costEntries p k ++ lawEntries (s.afterPosting (s.costEntries p k)) (.build p k) ++ refunds ∧
        (∀ x ∈ refunds, x.reason = .refund) ∧
        (refunds = [] ∨ s'.phase = .ended) :=
  build_is_exact hG s hs.prices hs.ids p k loc hPhase

theorem VIII_nobody_controls_the_dice (G : GameDef) (_hG : G.Valid) (s s' : State G) (e : Event)
    (hs : Inv G s) (h : Engine.step G s e = .ok s') :
    (∃ serverSeed nonces, s.seed = combineSeed serverSeed nonces ∧
      s.seedCommitment = commitmentOf serverSeed) ∧
    s'.seed = s.seed ∧ s'.seedCommitment = s.seedCommitment ∧
    ((s'.rollsMade = s.rollsMade ∧ s'.lastRoll = s.lastRoll) ∨
     (s'.rollsMade = s.rollsMade + 1 ∧ s'.lastRoll = some (rollAt G s.seed s.rollsMade))) ∧
    ((EndsTurn s e ∧ (nextStage s).rolls = true) ↔ s'.rollsMade = s.rollsMade + 1) :=
  ⟨hs.core.seedFrom, step_seed h, step_seedCommitment h, step_rolls h, rolled_iff h⟩

theorem IX_cannot_stall_always_ends (G : GameDef) (hG : G.Valid) (s : State G)
    (hs : Inv G s) :
    (s.phase ≠ .ended → s.currentSeat.isSome = true) ∧
    (s.phase ≠ .ended →
      (∃ s', Engine.step G s .forceEndTurn = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1) ∧
      ∀ p, s.currentSeat = some p →
        ∃ s', Engine.step G s (.move p .endTurn) = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1) ∧
    (s.phase = .ended → ∀ e, (Engine.step G s e).toOption = none) ∧
    s.turnsTaken ≤ maxTurns G s.turnOrder.length ∧
    (s.turnsTaken = maxTurns G s.turnOrder.length → s.phase = .ended) ∧
    s.eventsApplied ≤ maxEvents G s.turnOrder.length ∧
    (∀ e s', Engine.step G s e = .ok s' → EveryEventIsCounted s s') ∧
    (∀ e s', Engine.step G s e = .ok s' → ActionLimitIsEnforced s e) ∧
    (∀ e s', Engine.step G s e = .ok s' → EndsTurn s e → TurnMovedOn s s') := by
  refine ⟨fun he => currentSeat_isSome hs.seat he, cannot_stall hG hs.cover hs.ids, ?_,
    hs.turns.turns_le, hs.turns.ended_at_max, events_le hs.events hs.turns,
    fun _ _ h => every_event_counted h, fun _ _ h => action_limit_enforced h,
    fun _ _ h hend => turn_moved_on hend h⟩
  intro he e
  simp [Engine.step, he, Except.toOption]

theorem the_winner_earned_it (G : GameDef) (_hG : G.Valid) (s : State G) (hs : Inv G s) :
    (∀ w, s.winner = some w →
      s.phase = .ended ∧ w ∈ s.turnOrder ∧
      (∀ p ∈ s.turnOrder, s.pointsOf p ≤ s.pointsOf w) ∧
      (G.targetPoints ≤ s.pointsOf w ∨ s.turnsTaken = maxTurns G s.turnOrder.length)) ∧
    (s.phase = .ended → s.winner.isSome = true) ∧
    ((∃ p ∈ s.turnOrder, G.targetPoints ≤ s.pointsOf p) → s.phase = .ended) :=
  ⟨hs.winner.won, hs.winner.isSome, fun ⟨_, hp, ht⟩ => target_ends_game hs.noPending hp ht⟩

theorem limits_hold (G : GameDef) (_hG : G.Valid) (s : State G) (hs : Inv G s) :
    s.laws.length ≤ maxLawsInForce ∧
    (∀ x ∈ s.laws, x.2.size ≤ maxLawSize) ∧
    (∀ seat, (s.openProposals.filter (·.by_ == seat)).length ≤ maxOpenPerSeat) ∧
    s.deals.length ≤ maxActiveDeals ∧
    (∀ x ∈ s.laws, x.2.plannedEntries s.turnOrder.length ≤ maxPlannedEntries) ∧
    plannedTotal s.laws s.turnOrder.length ≤ maxPlannedTotal ∧
    readsTotal s.laws s.turnOrder.length ≤ maxReadsTotal :=
  ⟨hs.limits.laws_len, hs.limits.laws_size, hs.limits.open_len, hs.limits.deals_len,
    hs.planned.each, hs.planned.total, hs.planned.reads⟩

theorem every_other_event_is_exact (G : GameDef) (_hG : G.Valid) (s s' : State G) (e : Event)
    (hs : Inv G s) (h : Engine.step G s e = .ok s') :
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
      s'.rollsMade = s.rollsMade) ∧
    (∀ p r n, e = .move p (.declare r n) →
      s' = { s with
        declared := fun q x => if q = p ∧ x = r then n else s.declared q x
        actionsThisTurn := fun q => if q = p then s.actionsThisTurn q + 1 else s.actionsThisTurn q
        eventsApplied := s.eventsApplied + 1 }) ∧
    DeclarationsKept s s' e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := step_is_exact hs.noPending h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    fun _ _ _ he => declare_is_exact hs.noPending (he ▸ h), declarations_kept hs.noPending h⟩

/-- Every reachable state has the properties the other proofs rely on. -/
theorem _root_.Charter.Reachable.inv {G : GameDef} (hG : G.Valid) {s : State G} (hs : Reachable G s) :
    Inv G s := by
  induction hs with
  | start seats serverSeed nonces h1 h2 _ => exact Inv.start hG seats serverSeed nonces h1 h2
  | next e _ h ih => exact Inv.step hG ih h

theorem X_what_you_vote_on_is_what_runs (G : GameDef) (_hG : G.Valid) :
    (∀ s, Reachable G s ↔ ∃ seats serverSeed nonces events,
      minSeats ≤ seats ∧ seats ≤ maxSeats ∧ Engine.replay G seats serverSeed nonces events = .ok s) ∧
    (∀ (s s₁ s₂ : State G) seat id L roll e,
      Reachable G s → Engine.step G s (.vote seat id true) = .ok s₁ → s₁.laws = enact s.laws id L →
      EndsTurn s₁ e → Engine.step G s₁ e = .ok s₂ → s₂.lastRoll = some roll →
      newEntries s₁ s₂ = Engine.predictNextTurn G (s.withLaw id L) roll) ∧
    (∀ (s s' : State G) e,
      Reachable G s → Engine.step G s e = .ok s' → EndsTurn s e → s.isLastTurn = true →
      (s.duePayments ++ lawEntries (s.afterPosting s.duePayments) .roundEnd) <+:
        newEntries s s') ∧
    (∀ (s s' : State G) e,
      Reachable G s → Engine.step G s e = .ok s' → EndsTurn s e → s'.rollsMade = s.rollsMade + 1 →
      (s.isLastTurn = false →
        newEntries s s' = rollEntries s (rollAt G s.seed s.rollsMade)) ∧
      (s.isLastTurn = true →
        newEntries s s' = s.roundEndEntries ++
          rollEntries (s.afterPosting s.roundEndEntries) (rollAt G s.seed s.rollsMade)) ∧
      s.nextRoller = s'.currentSeat) ∧
    (∀ (s s' : State G) e,
      Reachable G s → Engine.step G s e = .ok s' → EndsTurn s e → s'.rollsMade = s.rollsMade →
      newEntries s s' = s.entriesBeforeRoll) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    constructor
    · intro hs
      induction hs with
      | start seats serverSeed nonces h1 h2 h3 =>
        exact ⟨seats, serverSeed, nonces, [], h1, h2, replay_of h1 h2 h3 rfl⟩
      | next e _ h ih =>
        obtain ⟨seats, serverSeed, nonces, events, h1, h2, h3⟩ := ih
        exact ⟨seats, serverSeed, nonces, events ++ [e], h1, h2, replay_snoc h3 h⟩
    · rintro ⟨seats, serverSeed, nonces, events, h1, h2, h3⟩
      obtain ⟨_, _, hn, hf⟩ := replay_ok h3
      exact foldlM_step_induct (P := Reachable G) (fun _ e _ hs h => .next e hs h)
        events _ s (.start seats serverSeed nonces h1 h2 hn) hf
  · intro s s₁ s₂ seat id L roll e _ h1 hl hend h2 hr
    exact preview_exact h1 hl hend h2 hr
  · intro s s' e _ h hend hl
    exact round_end_prefix h hend hl
  · intro s s' e _ h hend hc
    exact roll_entries h hend hc
  · intro s s' e _ h hend hc
    exact no_roll_entries h hend hc

end Charter.Proofs
