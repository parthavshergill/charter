import Charter.Proofs.Ledger

/-!
# Ids are unique, and running deals are within their term

Each running deal and each open proposal has its own id. A vote or a signature therefore changes
exactly one proposal. No seat votes or signs twice on a proposal. A running deal has not passed its
last round and cannot run longer than agreed.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## How a body can change the deals and the open proposals -/

theorem decideLaw_counters (s : State G) (id : Nat) (L : Law) :
    (decideLaw s id L).openProposals = s.openProposals.filter (·.id != id) ∧
    (decideLaw s id L).nextProposalId = s.nextProposalId ∧
    (decideLaw s id L).deals = s.deals ∧ (decideLaw s id L).dealsStarted = s.dealsStarted := by
  unfold decideLaw
  simp only
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The three ways a body can change the running deals. -/
theorem body_deals_cases {s s1 : State G} {e : Event} (h : bodyOf s e = .ok s1) :
    (s1.deals = s.deals ∧ s1.dealsStarted = s.dealsStarted) ∨
    (∃ seat id, e = .exit seat id ∧ s1.dealsStarted = s.dealsStarted ∧
      s1.deals = s.deals.map fun d =>
        if d.id == id then { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
        else d) ∨
    (∃ seat id d, e = .sign seat id ∧ startDeal s id d = .ok s1) := by
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    left
    cases m with
    | endTurn => cases h
    | place k loc =>
      rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        exact ⟨rfl, rfl⟩
      · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
        exact ⟨rfl, rfl⟩
    | bankTrade a b =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok h
      obtain ⟨_, _, rfl⟩ := record_ok hr
      exact ⟨rfl, rfl⟩
    | offer t a b =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok h
      exact ⟨rfl, rfl⟩
    | accept i =>
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok h
      exact ⟨rfl, rfl⟩
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok h
      exact ⟨rfl, rfl⟩
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok h
      exact ⟨rfl, rfl⟩
  | propose seat b =>
    left
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h <;> exact ⟨rfl, rfl⟩
  | vote seat i y =>
    left
    obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · exact (decideLaw_counters _ _ _).2.2
    · exact ⟨rfl, rfl⟩
  | sign seat i =>
    obtain ⟨_, _, d, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · exact Or.inr (Or.inr ⟨seat, i, d, rfl, h⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    exact Or.inr (Or.inl ⟨seat, i, rfl, rfl, rfl⟩)

/-- The ways a body can change the open proposals. -/
theorem body_open_cases {s s1 : State G} {e : Event} (h : bodyOf s e = .ok s1) :
    (s1.openProposals = s.openProposals ∧ s1.nextProposalId = s.nextProposalId) ∨
    (∃ q : OpenProposal, s1.openProposals = s.openProposals ++ [q] ∧ q.id = s.nextProposalId ∧
      q.votes = [] ∧ q.signed = [] ∧ s1.nextProposalId = s.nextProposalId + 1) ∨
    (∃ id, s1.openProposals = s.openProposals.filter (·.id != id) ∧
      s1.nextProposalId = s.nextProposalId) ∨
    (∃ seat id yes p, s.openProposal? id = some p ∧ (p.votes.map (·.1)).contains seat = false ∧
      s1.nextProposalId = s.nextProposalId ∧
      s1.openProposals = s.openProposals.map fun q =>
        if q.id == id then q.withVote seat yes else q) ∨
    (∃ seat id p, s.openProposal? id = some p ∧ p.signed.contains seat = false ∧
      s1.nextProposalId = s.nextProposalId ∧
      s1.openProposals = s.openProposals.map fun q =>
        if q.id == id then { q with signed := p.signed ++ [seat] } else q) := by
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    left
    cases m with
    | endTurn => cases h
    | place k loc =>
      rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        exact ⟨rfl, rfl⟩
      · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
        exact ⟨rfl, rfl⟩
    | bankTrade a b =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok h
      obtain ⟨_, _, rfl⟩ := record_ok hr
      exact ⟨rfl, rfl⟩
    | offer t a b =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok h
      exact ⟨rfl, rfl⟩
    | accept i =>
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok h
      exact ⟨rfl, rfl⟩
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok h
      exact ⟨rfl, rfl⟩
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok h
      exact ⟨rfl, rfl⟩
  | propose seat b =>
    right; left
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok h
    · exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  | vote seat i y =>
    obtain ⟨_, p, _, hp, _, hv, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · have hc := decideLaw_counters s i ‹_›
      exact Or.inr (Or.inr (Or.inl ⟨i, hc.1, hc.2.1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨seat, i, y, p, hp, hv, rfl, rfl⟩)))
  | sign seat i =>
    obtain ⟨_, p, d, hp, _, _, hn, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h
      exact Or.inr (Or.inr (Or.inl ⟨i, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨seat, i, p, hp, hn, rfl, rfl⟩)))
  | exit seat i =>
    left
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    exact ⟨rfl, rfl⟩

/-! ## The turn change and these fields -/

section startNextTurn
variable (s : State G) (roll : Nat)

@[simp] theorem startNextTurn_dealsStarted :
    (startNextTurn s roll).dealsStarted = s.dealsStarted := by
  unfold startNextTurn; split <;> rfl
@[simp] theorem startNextTurn_nextProposalId :
    (startNextTurn s roll).nextProposalId = s.nextProposalId := by
  unfold startNextTurn; split <;> rfl

theorem startNextTurn_openProposals_sublist' :
    (startNextTurn s roll).openProposals.Sublist s.openProposals := by
  unfold startNextTurn
  split
  · exact List.Sublist.refl _
  · exact List.filter_sublist
  · exact List.filter_sublist
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem startNextTurn_deals_sublist' :
    (startNextTurn s roll).deals.Sublist s.deals := by
  unfold startNextTurn
  split
  · exact List.Sublist.refl _
  · exact List.Sublist.refl _
  · exact List.Sublist.refl _
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem startNextTurn_round_ge : s.round ≤ (startNextTurn s roll).round := by
  unfold startNextTurn
  split <;> simp [beginActionTurn]

/-- A deal that survives a turn change has not passed its last round in the new round. -/
theorem startNextTurn_deal_round (h : ∀ d ∈ s.deals, s.round ≤ d.lastRound) {d : ActiveDeal}
    (hd : d ∈ (startNextTurn s roll).deals) : (startNextTurn s roll).round ≤ d.lastRound := by
  revert hd
  unfold startNextTurn
  split
  · exact h d
  · exact h d
  · exact h d
  · intro hd
    have := List.mem_filter.mp hd
    have h2 : s.round < d.lastRound := by simpa using this.2
    exact h2
  · intro hd
    cases hd

end startNextTurn

/-! ## Finding by id -/

theorem openProposal_mem {s : State G} {id : Nat} {p : OpenProposal}
    (h : s.openProposal? id = some p) : p ∈ s.openProposals ∧ p.id = id := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

/-- On a list of proposals with distinct ids, an id names one proposal. -/
theorem eq_of_id_eq {α : Type} {β : Type} (f : α → β) {L : List α} (h : (L.map f).Nodup)
    {a b : α} (ha : a ∈ L) (hb : b ∈ L) (he : f a = f b) : a = b := by
  induction L with
  | nil => cases ha
  | cons x t ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    cases List.mem_cons.mp ha with
    | inl h1 =>
      cases List.mem_cons.mp hb with
      | inl h2 => rw [h1, h2]
      | inr h2 =>
        subst h1
        exact absurd he.symm (h.1 b h2)
    | inr h1 =>
      cases List.mem_cons.mp hb with
      | inl h2 =>
        subst h2
        exact absurd he (h.1 a h1)
      | inr h2 => exact ih h.2 h1 h2

/-! ## The invariant -/

/-- Unique ids, no double votes or signatures, and deals within their term. -/
structure IdInv (s : State G) : Prop where
  deal_lt : ∀ d ∈ s.deals, d.id < s.dealsStarted
  deal_nodup : (s.deals.map (·.id)).Nodup
  signers_nodup : ∀ d ∈ s.deals, d.deal.signers.Nodup
  prop_lt : ∀ q ∈ s.openProposals, q.id < s.nextProposalId
  prop_nodup : (s.openProposals.map (·.id)).Nodup
  votes_nodup : ∀ p ∈ s.openProposals, (p.votes.map (·.1)).Nodup
  signed_nodup : ∀ p ∈ s.openProposals, p.signed.Nodup
  deal_round : ∀ d ∈ s.deals, s.round ≤ d.lastRound
  deal_term : ∀ d ∈ s.deals, d.lastRound + 1 ≤ s.round + d.deal.rounds

theorem IdInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    IdInv (initialState G seats serverSeed nonces) := by
  constructor <;> simp [initialState]

/-- A deal with no problems has signers listed once and runs for at least one round. -/
theorem dealProblems_shape {s : State G} {d : Deal} (h : dealProblems s d = []) :
    d.signers.Nodup ∧ 1 ≤ d.rounds := by
  simp only [dealProblems, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, _⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  constructor
  · by_cases hc : d.signers.Nodup
    · exact hc
    · simp [hc] at h2
  · by_cases hc : 1 ≤ d.rounds
    · exact hc
    · simp [hc] at h4

theorem map_id_map_eq (L : List OpenProposal) (f : OpenProposal → OpenProposal)
    (hf : ∀ q, (f q).id = q.id) : (L.map f).map (·.id) = L.map (·.id) := by
  simp [List.map_map, Function.comp_def, hf]

/-- The turn change keeps these facts. -/
theorem IdInv.startNextTurn {s : State G} (hi : IdInv s) (roll : Nat) :
    IdInv (startNextTurn s roll) := by
  have hdsub : ∀ d ∈ (Engine.startNextTurn s roll).deals, d ∈ s.deals := fun d hd =>
    (startNextTurn_deals_sublist' s roll).subset hd
  have hpsub : ∀ q ∈ (Engine.startNextTurn s roll).openProposals, q ∈ s.openProposals := fun q hq =>
    (startNextTurn_openProposals_sublist' s roll).subset hq
  refine ⟨?_, ?_, fun d hd => hi.signers_nodup d (hdsub d hd), ?_, ?_,
    fun p hp => hi.votes_nodup p (hpsub p hp), fun p hp => hi.signed_nodup p (hpsub p hp),
    fun d hd => startNextTurn_deal_round s roll hi.deal_round hd, ?_⟩
  · intro d hd
    simpa using hi.deal_lt d (hdsub d hd)
  · exact ((startNextTurn_deals_sublist' s roll).map _).nodup hi.deal_nodup
  · intro q hq
    simpa using hi.prop_lt q (hpsub q hq)
  · exact ((startNextTurn_openProposals_sublist' s roll).map _).nodup hi.prop_nodup
  · intro d hd
    have := hi.deal_term d (hdsub d hd)
    have h2 := startNextTurn_round_ge s roll
    omega

theorem IdInv.body {s s1 : State G} {e : Event} (hi : IdInv s) (h : bodyOf s e = .ok s1) :
    IdInv s1 := by
  have f := bodyOf_frame h
  -- First the deal facts.
  have hdeals : (∀ d ∈ s1.deals, d.id < s1.dealsStarted) ∧ (s1.deals.map (·.id)).Nodup ∧
      (∀ d ∈ s1.deals, d.deal.signers.Nodup) ∧ (∀ d ∈ s1.deals, s1.round ≤ d.lastRound) ∧
      (∀ d ∈ s1.deals, d.lastRound + 1 ≤ s1.round + d.deal.rounds) := by
    rw [f.round]
    rcases body_deals_cases h with ⟨hd, hc⟩ | ⟨_, id, _, hc, hd⟩ | ⟨_, id, d, _, hst⟩
    · rw [hd, hc]
      exact ⟨hi.deal_lt, hi.deal_nodup, hi.signers_nodup, hi.deal_round, hi.deal_term⟩
    · rw [hd, hc]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp ha
        split
        · exact hi.deal_lt d hd'
        · exact hi.deal_lt d hd'
      · have : (s.deals.map fun d =>
            if d.id == id then { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
            else d).map (·.id) = s.deals.map (·.id) := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro d _
          simp only [Function.comp_def]
          split <;> rfl
        rw [this]
        exact hi.deal_nodup
      · intro a ha
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp ha
        split
        · exact hi.signers_nodup d hd'
        · exact hi.signers_nodup d hd'
      · intro a ha
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp ha
        have := hi.deal_round d hd'
        split
        · simp only [Nat.min_def]; split <;> omega
        · exact this
      · intro a ha
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp ha
        have := hi.deal_term d hd'
        split
        · simp only [Nat.min_def]; split <;> omega
        · exact this
    · obtain ⟨_, hprob, _, _, rfl⟩ := startDeal_ok hst
      obtain ⟨hnd, hr⟩ := dealProblems_shape hprob
      simp only
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha =>
          have := hi.deal_lt a ha
          omega
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          simp
      · rw [List.map_append, List.nodup_append]
        refine ⟨hi.deal_nodup, by simp, ?_⟩
        intro a ha b hb he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        have := hi.deal_lt x hx
        omega
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha => exact hi.signers_nodup a ha
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          exact hnd
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha => exact hi.deal_round a ha
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          simp only
          omega
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha => exact hi.deal_term a ha
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          simp only
          omega
  -- Then the proposal facts.
  have hprops : (∀ q ∈ s1.openProposals, q.id < s1.nextProposalId) ∧
      (s1.openProposals.map (·.id)).Nodup ∧
      (∀ p ∈ s1.openProposals, (p.votes.map (·.1)).Nodup) ∧
      (∀ p ∈ s1.openProposals, p.signed.Nodup) := by
    rcases body_open_cases h with ⟨ho, hn⟩ | ⟨q, ho, hq, hv, hsg, hn⟩ | ⟨id, ho, hn⟩ |
      ⟨seat, id, yes, p, hp, hnv, hn, ho⟩ | ⟨seat, id, p, hp, hnv, hn, ho⟩
    · rw [ho, hn]
      exact ⟨hi.prop_lt, hi.prop_nodup, hi.votes_nodup, hi.signed_nodup⟩
    · rw [ho, hn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha =>
          have := hi.prop_lt a ha
          omega
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          omega
      · rw [List.map_append, List.nodup_append]
        refine ⟨hi.prop_nodup, by simp, ?_⟩
        intro a ha b hb he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        have := hi.prop_lt x hx
        omega
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha => exact hi.votes_nodup a ha
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          simp [hv]
      · intro a ha
        cases List.mem_append.mp ha with
        | inl ha => exact hi.signed_nodup a ha
        | inr ha =>
          simp only [List.mem_singleton] at ha
          subst ha
          simp [hsg]
    · rw [ho, hn]
      have hsub : (s.openProposals.filter (·.id != id)).Sublist s.openProposals :=
        List.filter_sublist
      exact ⟨fun q hq => hi.prop_lt q (hsub.subset hq), (hsub.map _).nodup hi.prop_nodup,
        fun q hq => hi.votes_nodup q (hsub.subset hq), fun q hq => hi.signed_nodup q (hsub.subset hq)⟩
    · obtain ⟨hpm, hpid⟩ := openProposal_mem hp
      rw [ho, hn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        split
        · exact hi.prop_lt q hq
        · exact hi.prop_lt q hq
      · rw [map_id_map_eq]
        · exact hi.prop_nodup
        · intro q
          split <;> rfl
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        split
        · rename_i hid
          have hqp : q = p :=
            eq_of_id_eq (·.id) hi.prop_nodup hq hpm (by simpa [hpid] using hid)
          subst hqp
          simp only [OpenProposal.withVote, List.map_append, List.map_cons, List.map_nil]
          rw [List.nodup_append]
          refine ⟨hi.votes_nodup q hq, by simp, ?_⟩
          intro x hx y hy hxy
          simp only [List.mem_singleton] at hy
          simp only [List.contains_eq_mem, decide_eq_false_iff_not] at hnv
          exact hnv (by rw [hxy, hy] at hx; exact hx)
        · exact hi.votes_nodup q hq
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        split
        · exact hi.signed_nodup q hq
        · exact hi.signed_nodup q hq
    · obtain ⟨hpm, hpid⟩ := openProposal_mem hp
      rw [ho, hn]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        split
        · exact hi.prop_lt q hq
        · exact hi.prop_lt q hq
      · rw [map_id_map_eq]
        · exact hi.prop_nodup
        · intro q
          split <;> rfl
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        split
        · exact hi.votes_nodup q hq
        · exact hi.votes_nodup q hq
      · intro a ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        split
        · simp only
          rw [List.nodup_append]
          refine ⟨hi.signed_nodup p hpm, by simp, ?_⟩
          intro x hx y hy hxy
          simp only [List.mem_singleton] at hy
          simp only [List.contains_eq_mem, decide_eq_false_iff_not] at hnv
          exact hnv (by rw [hxy, hy] at hx; exact hx)
        · exact hi.signed_nodup q hq
  exact ⟨hdeals.1, hdeals.2.1, hdeals.2.2.1, hprops.1, hprops.2.1, hprops.2.2.1, hprops.2.2.2,
    hdeals.2.2.2.1, hdeals.2.2.2.2⟩

theorem IdInv.step {s s' : State G} {e : Event} (hi : IdInv s) (h : Engine.step G s e = .ok s') :
    IdInv s' := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨b, _, rfl⟩ := endTurnNow_ok h
    exact IdInv.startNextTurn (s := { s with books := b, journal := _ })
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7, hi.8, hi.9⟩ _
  · have h1 := hi.body hb
    rcases finish_cases hf with rfl | ⟨w, he⟩
    · exact ⟨h1.1, h1.2, h1.3, h1.4, h1.5, h1.6, h1.7, h1.8, h1.9⟩
    · obtain ⟨_, _, rfl⟩ := endGame_ok he
      constructor <;> simp

end Charter.Proofs
