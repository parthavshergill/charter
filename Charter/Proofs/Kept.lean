import Charter.Proofs.Deals
import Charter.Proofs.Accepted

/-!
# Open business changes only as the event says

Open proposals, running deals, offers and this round's list of builds. Each step keeps them, or
changes them exactly as `ProposalsKept`, `DealsKept`, `OffersKept` and `BuildsRecorded` say.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## The turn change, stage by stage -/

section startNextTurn
variable (s : State G) (roll : Nat)

@[simp] theorem startNextTurn_nextOfferId :
    (startNextTurn s roll).nextOfferId = s.nextOfferId := by
  unfold startNextTurn; split <;> rfl

/-- When the dice roll, the new seat's own proposals expire, and no others. -/
theorem startNextTurn_open_rolls (h : (nextStage s).rolls = true) :
    (startNextTurn s roll).openProposals =
      s.openProposals.filter fun p => some p.by_ != (startNextTurn s roll).currentSeat := by
  unfold startNextTurn
  split
  · rename_i he; rw [he] at h; cases h
  · rfl
  · rfl
  · rfl
  · rename_i he; rw [he] at h; cases h

theorem startNextTurn_open_setup {i : Nat} (h : nextStage s = .setupTurn i) :
    (startNextTurn s roll).openProposals = s.openProposals := by
  unfold startNextTurn; rw [h]

theorem startNextTurn_open_gameOver (h : nextStage s = .gameOver) :
    (startNextTurn s roll).openProposals = [] := by
  unfold startNextTurn; rw [h]

theorem startNextTurn_deals_gameOver (h : nextStage s = .gameOver) :
    (startNextTurn s roll).deals = [] := by
  unfold startNextTurn; rw [h]

/-- A turn change keeps every deal unless the round ends. -/
theorem startNextTurn_deals_keep (h : nextStage s ≠ .newRound) (h2 : nextStage s ≠ .gameOver) :
    (startNextTurn s roll).deals = s.deals := by
  unfold startNextTurn
  split
  · rfl
  · rfl
  · rfl
  · rename_i he; exact absurd he h
  · rename_i he; exact absurd he h2

theorem startNextTurn_deals_newRound (h : nextStage s = .newRound) :
    (startNextTurn s roll).deals = s.deals.filter fun d => decide (s.round < d.lastRound) := by
  unfold startNextTurn; rw [h]; rfl

/-- If a running game ends at a turn change, the stage was `gameOver`. -/
theorem startNextTurn_ended (he : s.phase ≠ .ended) (h : (startNextTurn s roll).phase = .ended) :
    nextStage s = .gameOver := by
  cases hs : nextStage s with
  | gameOver => rfl
  | setupTurn i =>
    rw [(startNextTurn_setupTurn hs).1] at h
    exact absurd h he
  | firstRound =>
    rw [(startNextTurn_firstRound hs).1] at h
    cases h
  | sameRound i =>
    rw [(startNextTurn_sameRound hs).1] at h
    cases h
  | newRound =>
    rw [(startNextTurn_newRound hs).1] at h
    cases h

theorem startNextTurn_built_keep (h : nextStage s ≠ .newRound) :
    (startNextTurn s roll).builtThisRound = s.builtThisRound := by
  unfold startNextTurn
  split
  · rfl
  · rfl
  · rfl
  · rename_i he; exact absurd he h
  · rfl

theorem startNextTurn_built_newRound (h : nextStage s = .newRound) :
    (startNextTurn s roll).builtThisRound = [] := by
  unfold startNextTurn; rw [h]; rfl

end startNextTurn

/-- `nextStage` does not read the books or the journal. -/
theorem nextStage_books (s : State G) (b : Books) (j : List Entry) :
    nextStage ({ s with books := b, journal := j } : State G) = nextStage s := rfl

/-- The turn moves on to the stage `nextStage` names. -/
theorem startNextTurn_moved (s : State G) (roll : Nat) : TurnMovedOn s (startNextTurn s roll) := by
  refine ⟨startNextTurn_turnsTaken _ _, ?_⟩
  split
  · rename_i i hs
    have h := startNextTurn_setupTurn (roll := roll) hs
    refine ⟨?_, ?_, h.2⟩
    · rw [h.1]
      cases hp : s.phase with
      | setup => rfl
      | actions =>
        unfold nextStage at hs
        rw [hp] at hs
        simp only at hs
        split at hs
        · split at hs <;> cases hs
        · cases hs
      | ended =>
        unfold nextStage at hs
        rw [hp] at hs
        cases hs
    · unfold startNextTurn; rw [hs]
  · rename_i hs
    have h := startNextTurn_firstRound (roll := roll) hs
    exact ⟨h.1, h.2.2, h.2.1⟩
  · rename_i i hs
    have h := startNextTurn_sameRound (roll := roll) hs
    exact ⟨h.1, h.2.2, h.2.1⟩
  · rename_i hs
    have h := startNextTurn_newRound (roll := roll) hs
    exact ⟨h.1, h.2.2, h.2.1⟩
  · rename_i hs
    exact startNextTurn_gameOver hs

/-! ## Helpers about the event -/

theorem proposalAfter_endsTurn {s : State G} {e : Event} (h : EndsTurn s e) (p : OpenProposal) :
    proposalAfter e p = p := by
  cases e with
  | vote a b c => cases h
  | sign a b => cases h
  | propose a b => rfl
  | exit a b => rfl
  | forceEndTurn => rfl
  | move a m => rfl

theorem dealAfter_endsTurn {s : State G} {e : Event} (h : EndsTurn s e) (d : ActiveDeal) :
    dealAfter s e d = d := by
  cases e with
  | exit a b => cases h
  | vote a b c => rfl
  | sign a b => rfl
  | propose a b => rfl
  | forceEndTurn => rfl
  | move a m => rfl

/-- If the game did not end, a step that does not end the turn leaves `s'` as the counted body. -/
theorem act_not_ended {s1 s' : State G} {e : Event} {seat : Seat}
    (hf : finish (countAction s1 seat) e = .ok s') (hne : s'.phase ≠ .ended) :
    s' = countAction s1 seat := by
  rcases finish_cases hf with h | ⟨w, hw⟩
  · exact h
  · obtain ⟨_, _, h3⟩ := endGame_ok hw
    exact absurd (by rw [h3]) hne

/-- If a step that does not end the turn ends the game, it closes everything. -/
theorem act_ended {s s1 s' : State G} {e : Event} {seat : Seat} (hb : bodyOf s e = .ok s1)
    (he : s.phase ≠ .ended) (hf : finish (countAction s1 seat) e = .ok s')
    (hp : s'.phase = .ended) : s'.openProposals = [] ∧ s'.deals = [] ∧ s'.offers = [] := by
  rcases finish_cases hf with rfl | ⟨w, hw⟩
  · exact absurd ((bodyOf_frame hb).phase.symm.trans hp) he
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    exact ⟨rfl, rfl, rfl⟩

/-! ## Proposals -/

/-- The first two ways `ProposalCloses` can happen. Neither ends a turn. -/
def BodyCloses (s : State G) (e : Event) (p : OpenProposal) : Prop :=
  (∃ seat L, e = .vote seat p.id true ∧ p.body = .law L ∧
    (p.withVote seat true).hasMajority s.turnOrder.length) ∨
  (∃ seat d, e = .sign seat p.id ∧ p.body = .deal d ∧ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat)

/-- What `ProposalsKept` says about an event body. -/
structure BodyKept (s s1 : State G) (e : Event) : Prop where
  fresh : ∀ q ∈ s1.openProposals,
    (∃ seat, e = .propose seat q.body ∧ q.id = s.nextProposalId ∧ q.by_ = seat ∧
      q.votes = [] ∧ q.signed = []) ∨
    ∃ p ∈ s.openProposals, q = proposalAfter e p
  closes : ∀ p ∈ s.openProposals, BodyCloses s e p → ∀ q ∈ s1.openProposals, q.id ≠ p.id
  keeps : ∀ p ∈ s.openProposals, ¬ BodyCloses s e p → proposalAfter e p ∈ s1.openProposals

/-- A body that leaves the open list alone, for an event that is not a vote or signature. -/
theorem bodyKept_same {s s1 : State G} {e : Event} (ho : s1.openProposals = s.openProposals)
    (hc : ∀ p, ¬ BodyCloses s e p) (ha : ∀ p, proposalAfter e p = p) : BodyKept s s1 e := by
  refine ⟨?_, fun p _ h => absurd h (hc p), ?_⟩
  · intro q hq
    rw [ho] at hq
    exact Or.inr ⟨q, hq, (ha q).symm⟩
  · intro p hp _
    rw [ha, ho]
    exact hp

theorem openProposal_eq {s : State G} (hi : IdInv s) {id : Nat} {p q : OpenProposal}
    (hp : s.openProposal? id = some p) (hq : q ∈ s.openProposals) (he : q.id = id) : q = p :=
  eq_of_id_eq (·.id) hi.prop_nodup hq (openProposal_mem hp).1 (he.trans (openProposal_mem hp).2.symm)

/-- A step that closes a proposal by id leaves the others as they were. -/
theorem bodyKept_filter {s s1 : State G} {e : Event} {id : Nat}
    (ho : s1.openProposals = s.openProposals.filter (·.id != id))
    (hafter : ∀ p, p.id ≠ id → proposalAfter e p = p)
    (hclosesId : ∀ p, BodyCloses s e p → p.id = id)
    (hcloses : ∀ p ∈ s.openProposals, p.id = id → BodyCloses s e p) : BodyKept s s1 e := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [ho] at hq
    obtain ⟨h1, h2⟩ := List.mem_filter.mp hq
    refine Or.inr ⟨q, h1, (hafter q ?_).symm⟩
    simpa using h2
  · intro p _ hc q hq he
    rw [ho] at hq
    have h2 := (List.mem_filter.mp hq).2
    have : q.id ≠ id := by simpa using h2
    exact this (he.trans (hclosesId p hc))
  · intro p hp hnc
    have hne : p.id ≠ id := fun he => hnc (hcloses p hp he)
    rw [hafter p hne, ho]
    exact List.mem_filter.mpr ⟨hp, by simpa using hne⟩

/-- A step that changes one proposal in place removes none. -/
theorem bodyKept_map {s s1 : State G} {e : Event}
    {f : OpenProposal → OpenProposal}
    (ho : s1.openProposals = s.openProposals.map f)
    (hf : ∀ p ∈ s.openProposals, f p = proposalAfter e p)
    (hc : ∀ p ∈ s.openProposals, ¬ BodyCloses s e p) : BodyKept s s1 e := by
  refine ⟨?_, fun p hp h => absurd h (hc p hp), ?_⟩
  · intro q hq
    rw [ho] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact Or.inr ⟨p, hp, hf p hp⟩
  · intro p hp _
    rw [ho, ← hf p hp]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-- A move leaves the open proposals alone. -/
theorem move_open {s s1 : State G} {p : Seat} {m : Move} (hb : bodyOf s (.move p m) = .ok s1) :
    s1.openProposals = s.openProposals := by
  cases m with
  | endTurn => cases hb
  | place k loc =>
    rcases placeBody_ok hb with ⟨_, h⟩ | ⟨_, h⟩
    · obtain ⟨_, rfl⟩ := setupBody_ok h
      rfl
    · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
      rfl
  | bankTrade a b =>
    obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok hb
    obtain ⟨_, _, rfl⟩ := record_ok hr
    rfl
  | offer t a b =>
    obtain ⟨_, _, rfl⟩ := offerBody_ok hb
    rfl
  | accept i =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok hb
    rfl
  | cancel i =>
    obtain ⟨_, _, rfl⟩ := cancelBody_ok hb
    rfl
  | declare r n =>
    obtain ⟨_, _, rfl⟩ := declareBody_ok hb
    rfl

theorem body_kept {s s1 : State G} {e : Event} (hi : IdInv s) (hb : bodyOf s e = .ok s1) :
    BodyKept s s1 e := by
  have nocl : ∀ (hv : ∀ a b c, e ≠ .vote a b c) (hg : ∀ a b, e ≠ .sign a b) (p : OpenProposal),
      ¬ BodyCloses s e p := by
    intro hv hg p hc
    rcases hc with ⟨a, _, h, _⟩ | ⟨a, _, h, _⟩
    · exact hv _ _ _ h
    · exact hg _ _ h
  cases e with
  | forceEndTurn => cases hb
  | move p m =>
    exact bodyKept_same (move_open hb) (nocl (by simp) (by simp)) (fun _ => rfl)
  | exit a c =>
    obtain ⟨_, _, hs1⟩ := exitBody_ok hb
    exact bodyKept_same (by rw [hs1]) (nocl (by simp) (by simp)) (fun _ => rfl)
  | propose seat b =>
    have hb' : proposeBody s seat b = .ok s1 := hb
    have hopen : s1.openProposals = s.openProposals ++
        [{ id := s.nextProposalId, by_ := seat, body := b, votes := [], signed := [] }] := by
      obtain ⟨_, _, ⟨_, rfl, _, rfl⟩ | ⟨_, rfl, _, _, rfl⟩⟩ := proposeBody_ok hb' <;> rfl
    have hcl := nocl (by simp) (by simp)
    refine ⟨?_, fun p _ h => absurd h (hcl p), ?_⟩
    · intro q hq
      rw [hopen] at hq
      cases List.mem_append.mp hq with
      | inl h => exact Or.inr ⟨q, h, rfl⟩
      | inr h =>
        simp only [List.mem_singleton] at h
        subst h
        exact Or.inl ⟨seat, rfl, rfl, rfl, rfl, rfl⟩
    · intro p hp _
      rw [hopen]
      exact List.mem_append_left _ hp
  | vote seat id yes =>
    have hb' : voteBody s seat id yes = .ok s1 := hb
    obtain ⟨_, p0, L, hp0, hL, _, ⟨hd, hs1⟩ | ⟨hd, hs1⟩⟩ := voteBody_ok hb'
    · have hd' := hd
      simp only [isDecidingVote, Bool.and_eq_true, decide_eq_true_eq] at hd'
      obtain ⟨hyes, hm⟩ := hd'
      apply bodyKept_filter (id := id)
      · rw [hs1]
        exact (decideLaw_counters s id L).1
      · intro p hne
        have : ¬ id = p.id := fun h => hne h.symm
        simp [proposalAfter, this]
      · intro p hc
        rcases hc with ⟨a, _, h, _⟩ | ⟨a, _, h, _⟩
        · injection h with _ h2 _
          exact h2.symm
        · cases h
      · intro p hp he
        have hpp := openProposal_eq hi hp0 hp he
        subst hpp
        exact Or.inl ⟨seat, L, by rw [hyes, he], hL, hm⟩
    · apply bodyKept_map (f := fun q => if q.id == id then q.withVote seat yes else q)
      · rw [hs1]
      · intro p _
        by_cases hid : p.id = id
        · simp [proposalAfter, hid]
        · have : ¬ id = p.id := fun h => hid h.symm
          simp [proposalAfter, hid, this]
      · intro p hp hc
        rcases hc with ⟨a, _, h, _, hm⟩ | ⟨a, _, h, _⟩
        · injection h with h1 h2 h3
          rw [← h1] at hm
          have hpp := openProposal_eq hi hp0 hp h2.symm
          subst hpp
          rw [h3] at hd
          have : isDecidingVote s p seat true = true := by
            simp only [isDecidingVote, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨trivial, hm⟩
          rw [this] at hd
          cases hd
        · cases h
  | sign seat id =>
    have hb' : signBody s seat id = .ok s1 := hb
    obtain ⟨_, p0, d0, hp0, hd0, _, _, ⟨hall, hst⟩ | ⟨hall, hs1⟩⟩ := signBody_ok hb'
    · obtain ⟨_, _, _, _, hs1⟩ := startDeal_ok hst
      apply bodyKept_filter (id := id)
      · rw [hs1]
      · intro p hne
        have : ¬ id = p.id := fun h => hne h.symm
        simp [proposalAfter, this]
      · intro p hc
        rcases hc with ⟨a, _, h, _⟩ | ⟨a, _, h, _⟩
        · cases h
        · injection h with _ h2
          exact h2.symm
      · intro p hp he
        have hpp := openProposal_eq hi hp0 hp he
        subst hpp
        exact Or.inr ⟨seat, d0, by rw [he], hd0, (all_contains_iff _ _ _).mp hall⟩
    · apply bodyKept_map (f := fun q =>
        if q.id == id then { q with signed := p0.signed ++ [seat] } else q)
      · rw [hs1]
      · intro p hp
        by_cases hid : p.id = id
        · have hpp := openProposal_eq hi hp0 hp hid
          subst hpp
          simp [proposalAfter, hid]
        · have : ¬ id = p.id := fun h => hid h.symm
          simp [proposalAfter, hid, this]
      · intro p hp hc
        rcases hc with ⟨a, _, h, _⟩ | ⟨a, d, h, hd, hall2⟩
        · cases h
        · injection h with h1 h2
          subst h1
          have hpp := openProposal_eq hi hp0 hp h2.symm
          subst hpp
          rw [hd0] at hd
          injection hd with hd
          subst hd
          have := (all_contains_iff _ _ _).mpr hall2
          rw [this] at hall
          cases hall

/-- `ProposalsKept` for a turn change. `t` is `s` with its entries recorded. -/
theorem proposals_kept_turn {s t : State G} {e : Event} (hi : IdInv s) (hend : EndsTurn s e)
    (ho : t.openProposals = s.openProposals) (hst : nextStage t = nextStage s)
    (hph : t.phase = s.phase) (he : s.phase ≠ .ended) (roll : Nat) :
    ProposalsKept s (startNextTurn t roll) e := by
  have noBody : ∀ p, ¬ BodyCloses s e p := by
    intro p hc
    rcases hc with ⟨a, _, h, _⟩ | ⟨a, _, h, _⟩
    · subst h; exact hend
    · subst h; exact hend
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hq' : q ∈ s.openProposals := by
      rw [← ho]
      exact List.Sublist.subset (startNextTurn_openProposals_sublist' t roll) hq
    exact Or.inr ⟨q, hq', (proposalAfter_endsTurn hend q).symm⟩
  · intro p hp hne
    rw [proposalAfter_endsTurn hend p]
    cases hr : (nextStage s).rolls with
    | true =>
      have hopen := startNextTurn_open_rolls t roll (by rw [hst]; exact hr)
      constructor
      · intro hc q hq hid
        rw [hopen] at hq
        obtain ⟨h1, h2⟩ := List.mem_filter.mp hq
        have hqp : q = p := eq_of_id_eq (·.id) hi.prop_nodup (ho ▸ h1) hp hid
        subst hqp
        rcases hc with hc | hc | ⟨_, _, hcur⟩
        · exact noBody q (Or.inl hc)
        · exact noBody q (Or.inr hc)
        · simp [hcur] at h2
      · intro hnc
        rw [hopen]
        refine List.mem_filter.mpr ⟨ho ▸ hp, ?_⟩
        by_cases hcur : (startNextTurn t roll).currentSeat = some p.by_
        · exact (hnc (Or.inr (Or.inr ⟨hend, hr, hcur⟩))).elim
        · simp only [bne_iff_ne, ne_eq]
          exact fun h => hcur h.symm
    | false =>
      have hopen : (startNextTurn t roll).openProposals = t.openProposals := by
        cases hs : nextStage t with
        | setupTurn i => exact startNextTurn_open_setup t roll hs
        | gameOver => exact absurd (startNextTurn_gameOver hs) hne
        | firstRound => rw [hst] at hs; rw [hs] at hr; cases hr
        | sameRound i => rw [hst] at hs; rw [hs] at hr; cases hr
        | newRound => rw [hst] at hs; rw [hs] at hr; cases hr
      constructor
      · intro hc
        rcases hc with hc | hc | ⟨_, hr2, _⟩
        · exact (noBody p (Or.inl hc)).elim
        · exact (noBody p (Or.inr hc)).elim
        · rw [hr] at hr2
          cases hr2
      · intro _
        rw [hopen, ho]
        exact hp
  · intro hp
    exact startNextTurn_open_gameOver t roll (startNextTurn_ended t roll (by rw [hph]; exact he) hp)

theorem proposals_kept {s s' : State G} {e : Event} (hi : IdInv s)
    (h : Engine.step G s e = .ok s') : ProposalsKept s s' e := by
  have he := step_not_ended h
  rcases step_view h with ⟨hend, h2⟩ | ⟨hnot, _, s1, hb, hf⟩
  · obtain ⟨b, _, hs⟩ := endTurnNow_ok h2
    rw [hs]
    refine proposals_kept_turn hi hend ?_ ?_ ?_ he _ <;> rfl
  · by_cases hp : s'.phase = .ended
    · obtain ⟨hopen, _, _⟩ := act_ended hb he hf hp
      refine ⟨?_, fun _ _ hne => absurd hp hne, fun _ => hopen⟩
      intro q hq
      rw [hopen] at hq
      cases hq
    · have hs := act_not_ended hf hp
      have k := body_kept hi hb
      have hopen : s'.openProposals = s1.openProposals := by rw [hs]; rfl
      have toBody : ∀ p, ProposalCloses s s' e p → BodyCloses s e p := by
        intro p hc
        rcases hc with hc | hc | ⟨hend, _, _⟩
        · exact Or.inl hc
        · exact Or.inr hc
        · exact absurd hend hnot
      refine ⟨?_, ?_, fun hx => absurd hx hp⟩
      · rw [hopen]
        exact k.fresh
      · intro p hpm _
        rw [hopen]
        refine ⟨fun hc => k.closes p hpm (toBody p hc), fun hnc => k.keeps p hpm ?_⟩
        intro hc
        rcases hc with hc | hc
        · exact hnc (Or.inl hc)
        · exact hnc (Or.inr (Or.inl hc))

/-! ## Deals -/

/-- What an exit does to one deal, when the seat signed the deal with that id. -/
theorem exit_map_eq {s : State G} (hi : IdInv s) {seat id : Nat}
    (hany : s.deals.any (fun d => d.id == id && d.deal.signers.contains seat) = true)
    {d : ActiveDeal} (hd : d ∈ s.deals) :
    (if d.id == id then { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
      else d) = dealAfter s (.exit seat id) d := by
  obtain ⟨dw, hdw, hw⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hw
  by_cases hid : d.id = id
  · have hdd : d = dw := eq_of_id_eq (·.id) hi.deal_nodup hd hdw (hid.trans hw.1.symm)
    subst hdd
    have hsig : seat ∈ d.deal.signers := by simpa using hw.2
    simp [dealAfter, hid, hsig]
  · have : ¬ id = d.id := fun h => hid h.symm
    simp [dealAfter, hid, this]

/-- What a body does to the running deals. -/
theorem body_deals_kept {s s1 : State G} {e : Event} (hi : IdInv s) (hb : bodyOf s e = .ok s1) :
    (∀ d' ∈ s1.deals,
      (∃ seat id p d, e = .sign seat id ∧ s.openProposal? id = some p ∧ p.body = .deal d ∧
        seat ∈ d.signers ∧ (∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) ∧
        d' = { id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
               startRound := s.round, builtBefore := s.builtThisRound.length }) ∨
      ∃ d ∈ s.deals, d' = dealAfter s e d) ∧
    (∀ d ∈ s.deals, dealAfter s e d ∈ s1.deals) := by
  have same : s1.deals = s.deals → (∀ d, dealAfter s e d = d) →
      (∀ d' ∈ s1.deals,
        (∃ seat id p d, e = .sign seat id ∧ s.openProposal? id = some p ∧ p.body = .deal d ∧
          seat ∈ d.signers ∧ (∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) ∧
          d' = { id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
                 startRound := s.round, builtBefore := s.builtThisRound.length }) ∨
        ∃ d ∈ s.deals, d' = dealAfter s e d) ∧
      (∀ d ∈ s.deals, dealAfter s e d ∈ s1.deals) := by
    intro h1 h2
    refine ⟨?_, ?_⟩
    · intro d' hd'
      rw [h1] at hd'
      exact Or.inr ⟨d', hd', (h2 d').symm⟩
    · intro d hd
      rw [h1, h2]
      exact hd
  cases e with
  | forceEndTurn => cases hb
  | exit seat id =>
    have hb' : exitBody s seat id = .ok s1 := hb
    obtain ⟨_, hany, hs1⟩ := exitBody_ok hb'
    subst hs1
    refine ⟨?_, ?_⟩
    · intro d' hd'
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd'
      exact Or.inr ⟨d0, hd0, exit_map_eq hi hany hd0⟩
    · intro d hd
      exact List.mem_map.mpr ⟨d, hd, exit_map_eq hi hany hd⟩
  | sign seat id =>
    have hb' : signBody s seat id = .ok s1 := hb
    obtain ⟨_, p0, d0, hp0, hd0, hsg, _, ⟨hall, hst⟩ | ⟨_, hs1⟩⟩ := signBody_ok hb'
    · obtain ⟨_, _, _, _, hs1⟩ := startDeal_ok hst
      refine ⟨?_, ?_⟩
      · intro d' hd'
        rw [hs1] at hd'
        cases List.mem_append.mp hd' with
        | inl h => exact Or.inr ⟨d', h, rfl⟩
        | inr h =>
          simp only [List.mem_singleton] at h
          exact Or.inl ⟨seat, id, p0, d0, rfl, hp0, hd0, by simpa using hsg,
            (all_contains_iff _ _ _).mp hall, h⟩
      · intro d hd
        rw [hs1]
        exact List.mem_append_left _ hd
    · exact same (by rw [hs1]) (fun _ => rfl)
  | move p m =>
    rcases body_deals_cases hb with ⟨hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, _, hc, _⟩
    · exact same hc (fun _ => rfl)
    · cases hc
    · cases hc
  | propose a b =>
    rcases body_deals_cases hb with ⟨hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, _, hc, _⟩
    · exact same hc (fun _ => rfl)
    · cases hc
    · cases hc
  | vote a b c =>
    rcases body_deals_cases hb with ⟨hc, _⟩ | ⟨_, _, hc, _⟩ | ⟨_, _, _, hc, _⟩
    · exact same hc (fun _ => rfl)
    · cases hc
    · cases hc

theorem deals_kept_turn {s t : State G} {e : Event} (hi : IdInv s) (hend : EndsTurn s e)
    (hd : t.deals = s.deals) (hst : nextStage t = nextStage s) (hph : t.phase = s.phase)
    (hround : t.round = s.round) (hlast : t.isLastTurn = s.isLastTurn)
    (he : s.phase ≠ .ended) (roll : Nat) : DealsKept s (startNextTurn t roll) e := by
  have hcl : t.closingDeals = s.closingDeals := by
    simp only [State.closingDeals, hd, hround]
  refine ⟨?_, ?_, ?_⟩
  · intro d' hd'
    have hd2 : d' ∈ s.deals := by
      rw [← hd]
      exact List.Sublist.subset (startNextTurn_deals_sublist' t roll) hd'
    exact Or.inr ⟨d', hd2, (dealAfter_endsTurn hend d').symm⟩
  · intro d hdm hne
    rw [dealAfter_endsTurn hend d]
    constructor
    · rintro ⟨_, hl, hc⟩
      exact closing_gone (s := t) (by rw [hlast]; exact hl) (by rw [hd]; exact hi.deal_nodup)
        (by rw [hcl]; exact hc) roll
    · intro hnc
      have keep : nextStage s ≠ .newRound → d ∈ (startNextTurn t roll).deals := by
        intro hn
        have hgo : nextStage t ≠ .gameOver := fun hg => hne (startNextTurn_gameOver hg)
        rw [startNextTurn_deals_keep t roll (by rw [hst]; exact hn) hgo, hd]
        exact hdm
      rcases nextStage_cases he with ⟨_, ⟨i, hs, _⟩ | ⟨hs, _⟩⟩ |
        ⟨hp, ⟨_, hs⟩ | ⟨h1, h2, hs⟩ | ⟨_, _, hs⟩⟩
      · exact keep (by rw [hs]; simp)
      · exact keep (by rw [hs]; simp)
      · exact keep (by rw [hs]; simp)
      · have hl : s.isLastTurn = true := by simp [State.isLastTurn, hp, h1]
        have hnotcl : d ∉ s.closingDeals := fun hc => hnc ⟨hend, hl, hc⟩
        have hlt : s.round < d.lastRound := by
          by_cases hx : d.lastRound ≤ s.round
          · refine (hnotcl ?_).elim
            unfold State.closingDeals
            have hr2 : ¬ G.rounds ≤ s.round := by omega
            simp only [hr2, ↓reduceIte]
            exact List.mem_filter.mpr ⟨hdm, by simpa using hx⟩
          · omega
        rw [startNextTurn_deals_newRound t roll (by rw [hst]; exact hs)]
        exact List.mem_filter.mpr ⟨by rw [hd]; exact hdm, by simpa [hround] using hlt⟩
      · exact absurd (startNextTurn_gameOver (by rw [hst]; exact hs)) hne
  · intro hp
    exact startNextTurn_deals_gameOver t roll (startNextTurn_ended t roll (by rw [hph]; exact he) hp)

theorem deals_kept {s s' : State G} {e : Event} (hi : IdInv s)
    (h : Engine.step G s e = .ok s') : DealsKept s s' e := by
  have he := step_not_ended h
  rcases step_view h with ⟨hend, h2⟩ | ⟨hnot, _, s1, hb, hf⟩
  · obtain ⟨b, _, hs⟩ := endTurnNow_ok h2
    rw [hs]
    refine deals_kept_turn hi hend ?_ ?_ ?_ ?_ ?_ he _ <;> rfl
  · by_cases hp : s'.phase = .ended
    · obtain ⟨_, hd, _⟩ := act_ended hb he hf hp
      refine ⟨?_, fun _ _ hne => absurd hp hne, fun _ => hd⟩
      intro q hq
      rw [hd] at hq
      cases hq
    · have hs := act_not_ended hf hp
      obtain ⟨k1, k2⟩ := body_deals_kept hi hb
      have hd : s'.deals = s1.deals := by rw [hs]; rfl
      refine ⟨?_, ?_, fun hx => absurd hx hp⟩
      · rw [hd]
        exact k1
      · intro d hdm _
        rw [hd]
        exact ⟨fun hc => absurd hc.1 hnot, fun _ => k2 d hdm⟩

/-! ## Offers -/

theorem offers_kept {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    OffersKept s s' e := by
  have he := step_not_ended h
  intro o ho
  rcases step_view h with ⟨_, h2⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨_, _, hs⟩ := endTurnNow_ok h2
    rw [hs, startNextTurn_offers] at ho
    cases ho
  · have ho1 : o ∈ s1.offers := by
      rcases finish_cases hf with rfl | ⟨w, hw⟩
      · exact ho
      · obtain ⟨_, _, hs⟩ := endGame_ok hw
        rw [hs] at ho
        cases ho
    cases e with
    | forceEndTurn => cases hb
    | move p m =>
      cases m with
      | endTurn => cases hb
      | place k loc =>
        rcases placeBody_ok hb with ⟨_, h3⟩ | ⟨_, h3⟩
        · obtain ⟨_, rfl⟩ := setupBody_ok h3
          exact Or.inl ho1
        · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h3
          exact Or.inl ho1
      | bankTrade a c =>
        obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok hb
        obtain ⟨_, _, rfl⟩ := record_ok hr
        exact Or.inl ho1
      | offer t a c =>
        obtain ⟨_, _, rfl⟩ := offerBody_ok hb
        cases List.mem_append.mp ho1 with
        | inl h3 => exact Or.inl h3
        | inr h3 =>
          simp only [List.mem_singleton] at h3
          subst h3
          exact Or.inr ⟨t, a, c, rfl, rfl⟩
      | accept i =>
        obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok hb
        exact Or.inl (List.mem_filter.mp ho1).1
      | cancel i =>
        obtain ⟨_, _, rfl⟩ := cancelBody_ok hb
        exact Or.inl (List.mem_filter.mp ho1).1
      | declare r n =>
        obtain ⟨_, _, rfl⟩ := declareBody_ok hb
        exact Or.inl ho1
    | propose seat b =>
      obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok hb <;> exact Or.inl ho1
    | vote seat i y =>
      obtain ⟨_, _, _, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok hb
      · have hx : (decideLaw s i ‹_›).offers = s.offers := by
          unfold decideLaw
          simp only
          split <;> rfl
        rw [hx] at ho1
        exact Or.inl ho1
      · exact Or.inl ho1
    | sign seat i =>
      obtain ⟨_, _, _, _, _, _, _, ⟨_, h3⟩ | ⟨_, rfl⟩⟩ := signBody_ok hb
      · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h3
        exact Or.inl ho1
      · exact Or.inl ho1
    | exit seat i =>
      obtain ⟨_, _, rfl⟩ := exitBody_ok hb
      exact Or.inl ho1

/-! ## This round's builds -/

/-- Only a build in the actions phase adds to the list of builds. -/
theorem body_built {s s1 : State G} {e : Event} (hb : bodyOf s e = .ok s1)
    (hne : s.phase = .actions → ∀ p k loc, e ≠ .move p (.place k loc)) :
    s1.builtThisRound = s.builtThisRound := by
  cases e with
  | forceEndTurn => cases hb
  | move p m =>
    cases m with
    | endTurn => cases hb
    | place k loc =>
      rcases placeBody_ok hb with ⟨_, h3⟩ | ⟨h1, _⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h3
        rfl
      · exact absurd rfl (hne h1 p k loc)
    | bankTrade a c =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok hb
      obtain ⟨_, _, rfl⟩ := record_ok hr
      rfl
    | offer t a c =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok hb
      rfl
    | accept i =>
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok hb
      rfl
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok hb
      rfl
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok hb
      rfl
  | propose seat b =>
    obtain ⟨_, _, ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok hb <;> rfl
  | vote seat i y =>
    obtain ⟨_, _, L, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok hb
    · unfold decideLaw
      simp only
      split <;> rfl
    · rfl
  | sign seat i =>
    obtain ⟨_, _, _, _, _, _, _, ⟨_, h3⟩ | ⟨_, rfl⟩⟩ := signBody_ok hb
    · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok h3
      rfl
    · rfl
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok hb
    rfl

/-- `finish` keeps the list of builds. -/
theorem finish_built {t s' : State G} {e : Event} (hf : finish t e = .ok s') :
    s'.builtThisRound = t.builtThisRound := by
  rcases finish_cases hf with rfl | ⟨w, hw⟩
  · rfl
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    rfl

theorem builds_recorded {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    BuildsRecorded s s' e := by
  refine ⟨?_, ?_, ?_⟩
  · rintro p k loc rfl hp
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hb' : placeBody s p k loc = .ok s1 := hb
    rcases placeBody_ok hb' with ⟨h1, _⟩ | ⟨_, h3⟩
    · rw [hp] at h1
      cases h1
    · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h3
      rw [finish_built hf]
      rfl
  · intro hend hs
    obtain ⟨b, _, hs2⟩ := step_endsTurn hend h
    rw [hs2]
    exact startNextTurn_built_newRound _ _ hs
  · intro hne hn
    rcases step_view h with ⟨hend, h2⟩ | ⟨_, _, s1, hb, hf⟩
    · obtain ⟨b, _, hs2⟩ := endTurnNow_ok h2
      rw [hs2]
      exact startNextTurn_built_keep _ _ (hn hend)
    · rw [finish_built hf]
      change s1.builtThisRound = _
      exact body_built hb hne

/-! ## More invariants -/

/-- Seats on open proposals are in the game, and deals keep to the term agreed when they started. -/
structure KeptInv (s : State G) : Prop where
  votes_seated : ∀ p ∈ s.openProposals, ∀ x ∈ p.votes, x.1 ∈ s.turnOrder
  signed_seated : ∀ p ∈ s.openProposals, ∀ i ∈ p.signed, i ∈ s.turnOrder
  deal_start : ∀ d ∈ s.deals, d.startRound ≤ s.round ∧ d.lastRound + 1 ≤ d.startRound + d.deal.rounds

theorem KeptInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    KeptInv (initialState G seats serverSeed nonces) := by
  constructor <;> simp [initialState]

theorem step_round_le {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    s.round ≤ s'.round := by
  rcases step_view h with ⟨_, h2⟩ | ⟨_, _, _, hb, hf⟩
  · obtain ⟨b, _, hs⟩ := endTurnNow_ok h2
    rw [hs]
    exact startNextTurn_round_ge
      ({ s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade) } : State G) _
  · exact Nat.le_of_eq (act_frame hb hf).round.symm

theorem KeptInv.step {s s' : State G} {e : Event} (hk : KeptInv s) (hi : IdInv s)
    (h : Engine.step G s e = .ok s') : KeptInv s' := by
  have hT := step_turnOrder h
  have hP := proposals_kept hi h
  have hD := deals_kept hi h
  have hi' := hi.step h
  have hr := step_round_le h
  refine ⟨?_, ?_, ?_⟩
  · intro q hq x hx
    rw [hT]
    rcases hP.1 q hq with ⟨_, _, _, _, hv, _⟩ | ⟨p, hp, rfl⟩
    · rw [hv] at hx
      cases hx
    · cases e with
      | vote seat id yes =>
        simp only [proposalAfter] at hx
        split at hx
        · simp only [OpenProposal.withVote, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hk.votes_seated p hp x hx
          · obtain ⟨hc, _⟩ := step_act h (by simp [EndsTurn])
            exact (canAct_mem hc).1
        · exact hk.votes_seated p hp x hx
      | sign a b =>
        simp only [proposalAfter] at hx
        split at hx
        · exact hk.votes_seated p hp x hx
        · exact hk.votes_seated p hp x hx
      | move a m => exact hk.votes_seated p hp x hx
      | propose a b => exact hk.votes_seated p hp x hx
      | exit a b => exact hk.votes_seated p hp x hx
      | forceEndTurn => exact hk.votes_seated p hp x hx
  · intro q hq i hx
    rw [hT]
    rcases hP.1 q hq with ⟨_, _, _, _, _, hv⟩ | ⟨p, hp, rfl⟩
    · rw [hv] at hx
      cases hx
    · cases e with
      | sign seat id =>
        simp only [proposalAfter] at hx
        split at hx
        · simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hk.signed_seated p hp i hx
          · obtain ⟨hc, _⟩ := step_act h (by simp [EndsTurn])
            exact (canAct_mem hc).1
        · exact hk.signed_seated p hp i hx
      | vote a b c =>
        simp only [proposalAfter] at hx
        split at hx
        · exact hk.signed_seated p hp i hx
        · exact hk.signed_seated p hp i hx
      | move a m => exact hk.signed_seated p hp i hx
      | propose a b => exact hk.signed_seated p hp i hx
      | exit a b => exact hk.signed_seated p hp i hx
      | forceEndTurn => exact hk.signed_seated p hp i hx
  · intro d hd
    rcases hD.1 d hd with ⟨seat, id, p, dl, rfl, _, _, _, _, rfl⟩ | ⟨d0, hd0, rfl⟩
    · have hterm := hi'.deal_term _ hd
      have hrf : s'.round = s.round := by
        obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
        exact (act_frame hb hf).round
      rw [hrf] at hterm ⊢
      exact ⟨Nat.le_refl _, hterm⟩
    · obtain ⟨h1, h2⟩ := hk.deal_start d0 hd0
      cases e with
      | exit seat id =>
        simp only [dealAfter]
        split
        · refine ⟨by simp only; omega, ?_⟩
          simp only [Nat.min_def]
          split <;> omega
        · exact ⟨by omega, h2⟩
      | move a m => exact ⟨by simp only [dealAfter]; omega, h2⟩
      | propose a b => exact ⟨by simp only [dealAfter]; omega, h2⟩
      | vote a b c => exact ⟨by simp only [dealAfter]; omega, h2⟩
      | sign a b => exact ⟨by simp only [dealAfter]; omega, h2⟩
      | forceEndTurn => exact ⟨by simp only [dealAfter]; omega, h2⟩

end Charter.Proofs
