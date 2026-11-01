import Charter.Proofs.Kept
import Charter.Proofs.Prices
import Charter.Proofs.Winner

/-!
# The rest of the promises

Money leaving the bank or the treasury, the limits on planned entries, any seat's vote, the dice
rolling exactly when a turn starts, and a turn moving on to the stage `nextStage` names.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## Money leaving the bank or the treasury -/

theorem bank_vacuous {s : State G} {e : Event} {x : Entry} (h1 : x.src ≠ .bank)
    (h2 : x.src ≠ .treasury) : MoneyLeavesBankOnlyFor s e x := by
  intro h
  rcases h with h | h
  · exact (h1 h).elim
  · exact (h2 h).elim

theorem bank_of_player {s : State G} {e : Event} {x : Entry} {i : Seat} (h : x.src = .player i) :
    MoneyLeavesBankOnlyFor s e x :=
  bank_vacuous (by rw [h]; simp) (by rw [h]; simp)

theorem bank_of_deposit {s : State G} {e : Event} {x : Entry} {k i : Nat}
    (h : x.src = .deposit k i) : MoneyLeavesBankOnlyFor s e x :=
  bank_vacuous (by rw [h]; simp) (by rw [h]; simp)

/-- Every entry of an event body that takes from the bank or the treasury is allowed. -/
theorem body_bank {s s1 : State G} {e : Event} (hb : bodyOf s e = .ok s1) :
    ∃ es, s1.journal = s.journal ++ es ∧ ∀ x ∈ es, MoneyLeavesBankOnlyFor s e x := by
  cases e with
  | forceEndTurn => cases hb
  | move p m =>
    cases m with
    | endTurn => cases hb
    | place k loc =>
      rcases placeBody_ok hb with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        exact ⟨[], by simp, by simp⟩
      · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
        refine ⟨_, rfl, ?_⟩
        intro x hx
        cases List.mem_append.mp hx with
        | inl hc =>
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
          exact bank_of_player rfl
        | inr hl =>
          exact fun _ => Or.inr (Or.inr ⟨(lawEntries_form _ _ x hl).1, Or.inl ⟨p, k, loc, rfl, hl⟩⟩)
    | bankTrade a c =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok hb
      obtain ⟨_, _, rfl⟩ := record_ok hr
      refine ⟨_, rfl, ?_⟩
      intro x hx _
      have hreason : x.reason = .trade := by
        simp only [State.bankTradeEntries, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      exact Or.inr (Or.inl ⟨hreason, p, a, c, rfl, hx⟩)
    | offer t a c =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok hb
      exact ⟨[], by simp, by simp⟩
    | accept id =>
      obtain ⟨_, o, _, _, _, _, _, _, rfl⟩ := acceptBody_ok hb
      refine ⟨_, rfl, ?_⟩
      intro x hx
      cases List.mem_append.mp hx with
      | inl h => exact bank_of_player (mem_bundleEntries h).1
      | inr h => exact bank_of_player (mem_bundleEntries h).1
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok hb
      exact ⟨[], by simp, by simp⟩
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok hb
      exact ⟨[], by simp, by simp⟩
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok hb
    · exact ⟨[], by simp [addProposal], by simp⟩
    · exact ⟨[], by simp [addProposal], by simp⟩
  | vote seat i y =>
    have hv : voteBody s seat i y = .ok s1 := hb
    rcases vote_view hv with ⟨L, hp, _, hs1⟩ | ⟨_, _, hj, _⟩
    · refine ⟨s.decreeEntries L, by rw [hs1], ?_⟩
      intro x hx
      have hf : LawForm x := settle_form (fun z hz => lawPlan_form s .now L z hz) x hx
      exact fun _ => Or.inr (Or.inr ⟨hf.1, Or.inr (Or.inr ⟨L, hp, hx⟩)⟩)
    · exact ⟨[], by simp [hj], by simp⟩
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, hst⟩ | ⟨_, rfl⟩⟩ := signBody_ok hb
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok hst
      refine ⟨_, rfl, ?_⟩
      intro x hx
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
      exact bank_of_player rfl
    · exact ⟨[], by simp, by simp⟩
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok hb
    exact ⟨[], by simp, by simp⟩

theorem step_bank {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') {x : Entry}
    (hx : x ∈ newEntries s s') : MoneyLeavesBankOnlyFor s e x := by
  rcases step_view h with ⟨hend, h2⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨b, _, hs⟩ := endTurnNow_ok h2
    have hne : newEntries s s' = turnEntries s (rollAt G s.seed s.rollsMade) :=
      newEntries_of (by rw [hs]; simp)
    rw [hne] at hx
    rcases mem_turnEntries hx with ⟨_, hx⟩ | hx
    · rcases mem_roundEndEntries hx with h3 | h3 | ⟨d, _, h3⟩
      · obtain ⟨_, d, _, p, _, h4, _⟩ := duePayments_form h3
        exact bank_of_deposit h4
      · exact fun _ => Or.inr (Or.inr ⟨(lawEntries_form _ _ x h3).1, Or.inr (Or.inl ⟨hend, Or.inl h3⟩)⟩)
      · obtain ⟨_, j, _, h4, _⟩ := refundEntries_form h3
        exact bank_of_deposit h4
    · rcases rollEntries_cases hx with h3 | h3
      · rcases harvestEntries_cases h3 with h4 | h4
        · rw [baseHarvest_atRoll] at h4
          exact fun _ => Or.inl ⟨(baseHarvest_form h4).2.1, hend,
            List.mem_append_left _ h4⟩
        · exact fun _ => Or.inr (Or.inr ⟨h4.1, Or.inr (Or.inl ⟨hend, Or.inr hx⟩)⟩)
      · exact fun _ => Or.inr (Or.inr ⟨h3.1, Or.inr (Or.inl ⟨hend, Or.inr hx⟩)⟩)
  · obtain ⟨es, hj, hes⟩ := body_bank hb
    rcases finish_cases hf with rfl | ⟨w, hw⟩
    · have : newEntries s (countAction s1 (seatOf e)) = es := newEntries_of hj
      rw [this] at hx
      exact hes x hx
    · obtain ⟨bk, _, hs2⟩ := endGame_ok hw
      have : newEntries s s' = es ++ (countAction s1 (seatOf e)).deals.flatMap
          (countAction s1 (seatOf e)).refundEntries :=
        newEntries_of (by rw [hs2]; simp [countAction, hj])
      rw [this] at hx
      cases List.mem_append.mp hx with
      | inl h3 => exact hes x h3
      | inr h3 =>
        obtain ⟨d, _, h4⟩ := List.mem_flatMap.mp h3
        obtain ⟨_, j, _, h5, _⟩ := refundEntries_form h4
        exact bank_of_deposit h5

/-! ## Any seat in the game can vote -/

theorem vote_accepted (hG : G.Valid) {s : State G} (hi : IdInv s) (seat id : Nat) (p : OpenProposal)
    (L : Law) (yes : Bool) (hPhase : s.phase = .actions) (hSeat : seat ∈ s.turnOrder)
    (hp : s.openProposal? id = some p) (hL : p.body = .law L)
    (hv : (p.votes.map (·.1)).contains seat = false)
    (hA : s.actionsThisTurn seat < maxActionsPerTurn) :
    ∃ s'', Engine.step G s (.vote seat id yes) = .ok s'' := by
  have h1p : (s.phase != .actions) = false := by simp [hPhase]
  have hbody : ∃ s1, voteBody s seat id yes = .ok s1 ∧ s1.deals = s.deals := by
    cases hd : isDecidingVote s p seat yes with
    | true =>
      refine ⟨decideLaw s id L, ?_, (decideLaw_counters s id L).2.2.1⟩
      unfold voteBody
      simp only [h1p, hp, hL, hv, hd]
      rfl
    | false =>
      refine ⟨{ s with openProposals := s.openProposals.map fun q =>
        if q.id == id then q.withVote seat yes else q }, ?_, rfl⟩
      unfold voteBody
      simp only [h1p, hp, hL, hv, hd]
      rfl
  obtain ⟨s1, hb, hd⟩ := hbody
  obtain ⟨s'', h1, _⟩ := checkWin_some hG (countAction s1 seat)
    (by rw [countAction_deals, hd]; exact hi.deal_nodup)
    (by
      intro d hd'
      rw [countAction_deals, hd] at hd'
      exact hi.signers_nodup d hd')
  refine ⟨s'', ?_⟩
  unfold Engine.step
  rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
  simp only [actThenCheckWin, act, canAct_of hSeat hA, ↓reduceIte, hb]
  exact h1

/-! ## A changed law list comes from a valid law -/

theorem laws_change_valid {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hsame : s'.laws ≠ s.laws) :
    ∃ id L, lawProblems G s L = [] ∧ s'.laws = enact s.laws id L := by
  obtain ⟨seat, id, p, L, rfl, _, _, _, _, _, hl⟩ := laws_change h hsame
  obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  have hb' : voteBody s seat id true = .ok s1 := hb
  have hl1 : s'.laws = s1.laws := (finish_laws hf).trans rfl
  obtain ⟨_, p', L', _, _, _, ⟨_, hs1⟩ | ⟨_, hs1⟩⟩ := voteBody_ok hb'
  · by_cases hx : (lawProblems G s L').isEmpty = true
    · refine ⟨id, L', List.isEmpty_iff.mp hx, ?_⟩
      rw [hl1, hs1]
      unfold decideLaw
      simp only [hx, ↓reduceIte]
      rfl
    · exfalso
      apply hsame
      have hf : (lawProblems G s L').isEmpty = false := by simpa using hx
      rw [hl1, hs1]
      unfold decideLaw
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
  · exact absurd (by rw [hl1, hs1]) hsame

/-! ## Planned entries -/

/-- No law asks for too many entries, and neither do all the laws together. -/
structure PlannedInv (s : State G) : Prop where
  each : ∀ x ∈ s.laws, x.2.plannedEntries s.turnOrder.length ≤ maxPlannedEntries
  total : plannedTotal s.laws s.turnOrder.length ≤ maxPlannedTotal
  reads : readsTotal s.laws s.turnOrder.length ≤ maxReadsTotal

theorem readsTotal_enact (laws : List (Nat × Law)) (id : Nat) (L : Law) (n : Nat) :
    readsTotal (enact laws id L) n = readsTotal (enact laws 0 L) n := by
  simp only [enact, readsTotal, List.map_append, List.sum_append]
  split <;> simp

theorem lawProblems_reads {s : State G} {L : Law} (h : lawProblems G s L = []) :
    readsTotal (enact s.laws 0 L) s.turnOrder.length ≤ maxReadsTotal := by
  by_cases hc : readsTotal (enact s.laws 0 L) s.turnOrder.length ≤ maxReadsTotal
  · exact hc
  · simp [lawProblems, hc] at h

theorem plannedTotal_enact (laws : List (Nat × Law)) (id : Nat) (L : Law) (n : Nat) :
    plannedTotal (enact laws id L) n = plannedTotal (enact laws 0 L) n := by
  simp only [enact, plannedTotal, List.map_append, List.sum_append]
  split <;> simp

theorem lawProblems_planned {s : State G} {L : Law} (h : lawProblems G s L = []) :
    L.plannedEntries s.turnOrder.length ≤ maxPlannedEntries ∧
    plannedTotal (enact s.laws 0 L) s.turnOrder.length ≤ maxPlannedTotal := by
  constructor
  · by_cases hc : L.plannedEntries s.turnOrder.length ≤ maxPlannedEntries
    · exact hc
    · simp [lawProblems, hc] at h
  · by_cases hc : plannedTotal (enact s.laws 0 L) s.turnOrder.length ≤ maxPlannedTotal
    · exact hc
    · simp [lawProblems, hc] at h

theorem PlannedInv.step {s s' : State G} {e : Event} (hp : PlannedInv s)
    (h : Engine.step G s e = .ok s') : PlannedInv s' := by
  have hT := step_turnOrder h
  by_cases hsame : s'.laws = s.laws
  · refine ⟨?_, ?_, ?_⟩
    · rw [hT, hsame]
      exact hp.each
    · rw [hT, hsame]
      exact hp.total
    · rw [hT, hsame]
      exact hp.reads
  · obtain ⟨id, L, hprob, hl⟩ := laws_change_valid h hsame
    obtain ⟨h1, h2⟩ := lawProblems_planned hprob
    refine ⟨?_, ?_, ?_⟩
    · rw [hT, hl]
      intro x hx
      rcases mem_enact hx with hm | rfl
      · exact hp.each x hm
      · exact h1
    · rw [hT, hl, plannedTotal_enact]
      exact h2
    · rw [hT, hl, readsTotal_enact]
      exact lawProblems_reads hprob

/-! ## A new game's founding laws -/

/-- What the founding laws in force satisfy, at this many seats. -/
structure FoundingFacts (G : GameDef) (n : Nat) (laws : List (Nat × Law)) : Prop where
  len : laws.length ≤ maxLawsInForce
  size : ∀ x ∈ laws, x.2.size ≤ maxLawSize
  each : ∀ x ∈ laws, x.2.plannedEntries n ≤ maxPlannedEntries
  total : plannedTotal laws n ≤ maxPlannedTotal
  reads : readsTotal laws n ≤ maxReadsTotal
  prices : ∀ x ∈ laws, ∀ c ∈ x.2.clauses, ClausePriceOk G c

theorem FoundingFacts.enact {n : Nat} {laws : List (Nat × Law)} {L : Law} (hf : FoundingFacts G n laws)
    (hp : lawProblems G ({ initialState G n 0 [] with laws := laws } : State G) L = []) (id : Nat) :
    FoundingFacts G n (Charter.enact laws id L) := by
  have hn := lawProblems_nil hp
  have hl := lawProblems_planned hp
  have hc := lawProblems_price hp
  have hr := lawProblems_reads hp
  simp only [initialState, List.length_range] at hn hl hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [enact_length]
    exact hn.2
  · intro x hx
    rcases mem_enact hx with hm | rfl
    · exact hf.size x hm
    · exact hn.1
  · intro x hx
    rcases mem_enact hx with hm | rfl
    · exact hf.each x hm
    · exact hl.1
  · rw [plannedTotal_enact]
    exact hl.2
  · rw [readsTotal_enact]
    exact hr
  · intro x hx
    rcases mem_enact hx with hm | rfl
    · exact hf.prices x hm
    · exact hc

theorem foundingFacts_all {n : Nat} (Ls : List Law) : ∀ (laws : List (Nat × Law)) (id : Nat),
    G.foundingOkFrom n laws id Ls = true → FoundingFacts G n laws →
    FoundingFacts G n (enactAll laws id Ls) := by
  induction Ls with
  | nil => intro laws _ _ hf; exact hf
  | cons L t ih =>
    intro laws id h hf
    simp only [GameDef.foundingOkFrom, Bool.and_eq_true] at h
    exact ih _ _ h.2 (hf.enact (List.isEmpty_iff.mp h.1) id)

theorem startingLaws_facts (hG : G.Valid) {n : Nat} (h1 : minSeats ≤ n) (h2 : n ≤ maxSeats) :
    FoundingFacts G n G.startingLaws :=
  foundingFacts_all _ _ _ (valid_founding hG h1 h2)
    ⟨by simp [maxLawsInForce], by simp, by simp, by simp [plannedTotal, maxPlannedTotal],
      by simp [readsTotal, maxReadsTotal], by simp⟩

theorem Limits.start (hG : G.Valid) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats) :
    Limits (initialState G seats serverSeed nonces) :=
  have hf := startingLaws_facts hG h1 h2
  ⟨hf.len, hf.size, by simp [initialState, maxOpenPerSeat], by simp [initialState, maxActiveDeals]⟩

theorem LawPrices.start (hG : G.Valid) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats) :
    LawPrices G (initialState G seats serverSeed nonces) :=
  (startingLaws_facts hG h1 h2).prices

theorem PlannedInv.start (hG : G.Valid) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats) :
    PlannedInv (initialState G seats serverSeed nonces) := by
  have hf := startingLaws_facts hG h1 h2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [initialState, List.length_range]
  · exact hf.each
  · exact hf.total
  · exact hf.reads

/-! ## The dice -/

/-- The dice roll exactly when a turn ends and an action turn comes next. -/
theorem rolled_iff {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    (EndsTurn s e ∧ (nextStage s).rolls = true) ↔ s'.rollsMade = s.rollsMade + 1 := by
  constructor
  · rintro ⟨hend, hr⟩
    obtain ⟨b, _, hs⟩ := step_endsTurn hend h
    rw [hs]
    exact (startNextTurn_rolled (s := { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade), pieces := s.turnPieces (rollAt G s.seed s.rollsMade) })
      hr _).1
  · intro hc
    by_cases hend : EndsTurn s e
    · exact ⟨hend, rolls_of_counter hend h hc⟩
    · obtain ⟨_, _, hb, hf⟩ := step_act h hend
      have := (act_frame hb hf).rollsMade
      omega

/-! ## A turn moves on -/

theorem turn_moved_on {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') : TurnMovedOn s s' := by
  obtain ⟨b, _, hs⟩ := step_endsTurn hend h
  rw [hs]
  exact startNextTurn_moved ({ s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade), pieces := s.turnPieces (rollAt G s.seed s.rollsMade) } : State G) _

/-! ## Seats, action counts and the phase -/

theorem actions_counted {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    ActionsAreCountedExactly s s' e := by
  refine ⟨?_, ?_⟩
  · intro hend q
    obtain ⟨b, _, hs⟩ := step_endsTurn hend h
    rw [hs, startNextTurn_actionsThisTurn]
  · intro hn
    obtain ⟨_, _, hb, hf⟩ := step_act h hn
    have f := (act_frame hb hf).actionsThisTurn
    have key : ∀ q, s'.actionsThisTurn q =
        if q = seatOf e then s.actionsThisTurn q + 1 else s.actionsThisTurn q := by
      intro q
      rw [f]
    cases e with
    | forceEndTurn => exact (hn trivial).elim
    | move p m => exact ⟨p, rfl, key⟩
    | propose p b => exact ⟨p, rfl, key⟩
    | vote p a c => exact ⟨p, rfl, key⟩
    | sign p a => exact ⟨p, rfl, key⟩
    | exit p a => exact ⟨p, rfl, key⟩

theorem phase_by_turn_or_win {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    PhaseChangesOnlyByTurnOrWin s s' e := by
  intro hn
  obtain ⟨_, s1, hb, hf⟩ := step_act h hn
  rcases finish_winner hf with rfl | ⟨w, hbest, hend⟩
  · exact Or.inl (bodyOf_frame hb).phase
  · obtain ⟨hw, _⟩ := bestSeat_spec hbest
    obtain ⟨_, hbk, hs2⟩ := endGame_ok hend
    have hT : s'.turnOrder = (countAction s1 (seatOf e)).turnOrder := by rw [hs2]
    refine Or.inr ⟨by rw [hs2], ?_⟩
    unfold winCandidates at hw
    split at hw
    · rename_i hl
      obtain ⟨x, hx, hc⟩ := List.any_eq_true.mp hl
      exact Or.inr ⟨x, by rw [hs2]; exact hx, hc⟩
    · obtain ⟨hm, ht⟩ := List.mem_filter.mp hw
      have ht2 : G.targetPoints ≤ (countAction s1 (seatOf e)).pointsOf w := by simpa using ht
      refine Or.inl ⟨w, by rw [hT]; exact hm, ?_⟩
      have hmono : (countAction s1 (seatOf e)).pointsOf w ≤ s'.pointsOf w :=
        pointsOf_mono (by rw [hs2]) (by rw [hs2]) (fun r => by
          rw [hs2]
          exact postAll_seat_mono refunds_no_seat_src hbk w r)
      omega

/-- After a move or a vote, a seat at the target has ended the game. -/
theorem looks_for_winner {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hl : LooksForWinner e) (hat : ∃ p ∈ s'.turnOrder, G.targetPoints ≤ s'.pointsOf p) :
    s'.phase = .ended := by
  have hfin : ∃ t, checkWin t = .ok s' := by
    rcases step_view h with ⟨hend, hnow⟩ | ⟨_, _, s1, _, hf⟩
    · cases e with
      | move p m =>
        cases m with
        | endTurn => exact hl.elim
        | _ => exact hend.elim
      | vote a b c => exact hend.elim
      | _ => exact hl.elim
    · cases e with
      | move p m => exact ⟨_, hf⟩
      | vote a b c => exact ⟨_, hf⟩
      | _ => exact hl.elim
  obtain ⟨t, hct⟩ := hfin
  obtain ⟨p, hp, ht⟩ := hat
  rcases checkWin_ok hct with ⟨rfl, hnil⟩ | ⟨w, hw⟩
  · unfold winCandidates at hnil
    split at hnil
    · rw [hnil] at hp
      cases hp
    · have : p ∈ seatsAtTarget s' := List.mem_filter.mpr ⟨hp, by simpa using ht⟩
      rw [hnil] at this
      simp at this
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    rfl

/-! ## Accepted offers -/

/-- Accepting an offer writes exactly the offer's entries, and then any refunds if the game ends. -/
theorem accepted_offers_exact {s s' : State G} {e : Event}
    (h : Engine.step G s e = .ok s') : AcceptedOffersAreExact s s' e := by
  rintro p id o rfl ho
  have he := step_not_ended h
  obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  have hf' : checkWin (countAction s1 p) = .ok s' := hf
  have hb' : acceptBody s p id = .ok s1 := hb
  obtain ⟨_, o', ho', h1, h2, _, _, _, hs1⟩ := acceptBody_ok hb'
  rw [ho] at ho'
  injection ho' with ho'
  subst ho'
  refine ⟨fun e => h1 e.symm, h2, ?_⟩
  rcases checkWin_ok hf' with ⟨rfl, _⟩ | ⟨w, hw⟩
  · refine ⟨[], ?_, by simp, Or.inl rfl⟩
    rw [List.append_nil]
    apply newEntries_of
    rw [hs1]
    rfl
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    refine ⟨(countAction s1 p).deals.flatMap (countAction s1 p).refundEntries, ?_, ?_, Or.inr rfl⟩
    · apply newEntries_of
      have hj : (countAction s1 p).journal = s.journal ++ offerEntries o p := by rw [hs1]; rfl
      change (countAction s1 p).journal ++ _ = _
      rw [hj, List.append_assoc]
    · intro x hx
      obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hx
      exact (refundEntries_form hd).1


/-! ## A running game has a current seat -/

/-- Until the game ends, the turn index points at a seat. -/
def CurrentSeatInv (s : State G) : Prop := s.phase ≠ .ended → s.turnIndex < s.turnOrder.length

theorem CurrentSeatInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64)
    (nonces : List UInt64) (h1 : minSeats ≤ seats) :
    CurrentSeatInv (initialState G seats serverSeed nonces) := by
  intro _
  have : 2 ≤ seats := h1
  simp [initialState]
  omega

theorem setupStage_index {n d i : Nat} (h : setupStage n d = .setupTurn i) : i < n := by
  unfold setupStage at h
  split at h
  · injection h with h
    omega
  · split at h
    · injection h with h
      omega
    · cases h

theorem CurrentSeatInv.startNextTurn {t : State G} (ht : CurrentSeatInv t) (he : t.phase ≠ .ended)
    (hn : 0 < t.turnOrder.length) (roll : Nat) : CurrentSeatInv (startNextTurn t roll) := by
  intro hne
  rw [startNextTurn_turnOrder]
  have hi := ht he
  rcases nextStage_cases he with ⟨hp, ⟨i, hs, _⟩ | ⟨hs, _⟩⟩ |
    ⟨_, ⟨h1, hs⟩ | ⟨_, _, hs⟩ | ⟨_, _, hs⟩⟩
  · have hx : (Engine.startNextTurn t roll).turnIndex = i := by
      unfold Engine.startNextTurn; rw [hs]
    have hstage : setupStage t.turnOrder.length (t.turnsTaken + 1) = .setupTurn i := by
      unfold nextStage at hs
      rw [hp] at hs
      exact hs
    rw [hx]
    exact setupStage_index hstage
  · rw [(startNextTurn_firstRound hs).2.2]
    exact hn
  · rw [(startNextTurn_sameRound hs).2.2]
    omega
  · rw [(startNextTurn_newRound hs).2.2]
    exact hn
  · exact absurd (startNextTurn_gameOver hs) hne

theorem CurrentSeatInv.step {s s' : State G} {e : Event} (ht : CurrentSeatInv s)
    (hn : 0 < s.turnOrder.length) (h : Engine.step G s e = .ok s') : CurrentSeatInv s' := by
  have he := step_not_ended h
  rcases step_view h with ⟨_, h2⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨b, _, hs⟩ := endTurnNow_ok h2
    rw [hs]
    exact CurrentSeatInv.startNextTurn
      (t := { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade), pieces := s.turnPieces (rollAt G s.seed s.rollsMade) })
      ht he hn _
  · have f := act_frame hb hf
    intro _
    rw [f.turnOrder, f.turnIndex]
    exact ht he

theorem currentSeat_isSome {s : State G} (ht : CurrentSeatInv s) (he : s.phase ≠ .ended) :
    s.currentSeat.isSome = true := by
  simp [State.currentSeat, ht he]

/-! ## Events are counted and limited -/

theorem every_event_counted {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    EveryEventIsCounted s s' := by
  rcases step_view h with ⟨_, h2⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨_, _, hs⟩ := endTurnNow_ok h2
    rw [EveryEventIsCounted, hs, startNextTurn_eventsApplied]
  · exact (act_frame hb hf).eventsApplied

theorem action_limit_enforced {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    ActionLimitIsEnforced s e := by
  intro hn
  obtain ⟨hc, _⟩ := step_act h hn
  have hlim := (canAct_mem hc).2
  cases e with
  | forceEndTurn => exact (hn trivial).elim
  | move p m => exact ⟨p, rfl, hlim⟩
  | propose p b => exact ⟨p, rfl, hlim⟩
  | vote p a c => exact ⟨p, rfl, hlim⟩
  | sign p a => exact ⟨p, rfl, hlim⟩
  | exit p a => exact ⟨p, rfl, hlim⟩

/-- A seat at its limit has every event except a turn end rejected. -/
theorem rejected_at_limit {s : State G} {e : Event} {p : Seat}
    (hl : maxActionsPerTurn ≤ s.actionsThisTurn p) (hp : senderOf e = some p) (hn : ¬ EndsTurn s e) :
    (Engine.step G s e).toOption = none := by
  cases hs : Engine.step G s e with
  | error m => rfl
  | ok s' =>
    obtain ⟨q, hq, hlt⟩ := action_limit_enforced hs hn
    rw [hp] at hq
    injection hq with hq
    subst hq
    omega

/-! ## An embargo stops a trade -/

theorem offerBody_blocked {s s1 : State G} {p q : Seat} {give get : Bundle}
    (h : offerBody s p (some q) give get = .ok s1) : s.tradeBlocked p q = false := by
  cases hb : s.tradeBlocked p q with
  | false => rfl
  | true =>
    exfalso
    unfold offerBody at h
    simp only [hb, Bool.not_true, Bool.and_false, Bool.not_false, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h

theorem blocked_trades_rejected {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    BlockedTradesAreRejected s e := by
  refine ⟨?_, ?_⟩
  · rintro p id o rfl ho
    obtain ⟨_, s1, hb, _⟩ := step_act h (by simp [EndsTurn])
    have hb' : acceptBody s p id = .ok s1 := hb
    obtain ⟨_, o', ho', _, _, hbl, _⟩ := acceptBody_ok hb'
    rw [ho] at ho'
    injection ho' with ho'
    subst ho'
    exact hbl
  · rintro p q give get rfl
    obtain ⟨_, s1, hb, _⟩ := step_act h (by simp [EndsTurn])
    exact offerBody_blocked hb

/-- Accepting an offer across an embargo is rejected. -/
theorem blocked_accept_rejected {s : State G} {p : Seat} {id : Nat} {o : Offer}
    (ho : s.offers.find? (·.id == id) = some o) (hb : s.tradeBlocked p o.src = true) :
    (Engine.step G s (.move p (.accept id))).toOption = none := by
  cases hs : Engine.step G s (.move p (.accept id)) with
  | error m => rfl
  | ok s' =>
    have := (blocked_trades_rejected hs).1 p id o rfl ho
    rw [hb] at this
    cases this

/-- Addressing an offer across an embargo is rejected. -/
theorem blocked_offer_rejected {s : State G} {p q : Seat} {give get : Bundle}
    (hb : s.tradeBlocked p q = true) :
    (Engine.step G s (.move p (.offer (some q) give get))).toOption = none := by
  cases hs : Engine.step G s (.move p (.offer (some q) give get)) with
  | error m => rfl
  | ok s' =>
    have := (blocked_trades_rejected hs).2 p q give get rfl
    rw [hb] at this
    cases this

/-! ## Reaching the target ends the game -/

end Charter.Proofs
