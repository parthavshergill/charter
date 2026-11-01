import Charter.Proofs.Cover

/-!
# Every event keeps deposits covering what deals can owe

A law, a trade or a build cannot touch a deposit, by commandment V. A round's end takes at most one
round's payments and leaves one round fewer to pay. A new deal starts with enough, because
`dealProblems` checks it.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## A new deal is covered -/

/-- In a deal with no problems, only signers pay, and only in real resources. -/
theorem dealProblems_pays {s : State G} {d : Deal} (h : dealProblems s d = []) :
    ∀ p ∈ d.allPays, p.src ∈ d.signers ∧ G.isRes p.res = true := by
  simp only [dealProblems, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, h7⟩, _⟩, _⟩ := h
  intro p hp
  have := h7 p hp
  simp only [payProblems, List.append_eq_nil_iff] at this
  obtain ⟨⟨h1, h2⟩, _⟩ := this
  constructor
  · by_cases hc : p.src ∈ d.signers
    · exact hc
    · simp [hc] at h1
  · by_cases hc : G.isRes p.res = true
    · exact hc
    · simp [hc] at h2

theorem dealProblems_covered {s : State G} {d : Deal} (h : dealProblems s d = []) :
    d.covered G = true := by
  simp only [dealProblems, List.append_eq_nil_iff] at h
  by_cases hc : d.covered G = true
  · exact hc
  · simp [hc] at h

/-- A deal with no problems sets aside enough for all its rounds. -/
theorem new_deal_covered {s : State G} {d : Deal} (h : dealProblems s d = []) (i : Seat) (r : Res) :
    d.rounds * d.owedPerRound i r ≤ d.depositOf i r := by
  by_cases hz : d.owedPerRound i r = 0
  · rw [hz, Nat.mul_zero]
    exact Nat.zero_le _
  · have hex : ∃ p ∈ d.allPays, p.src = i ∧ p.res = r := by
      by_cases hc : ∃ p ∈ d.allPays, p.src = i ∧ p.res = r
      · exact hc
      · refine absurd ?_ hz
        have : d.allPays.filter (fun p => p.src == i && p.res == r) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro p hp
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact fun he => hc ⟨p, hp, he.1, he.2⟩
        simp [Deal.owedPerRound, this]
    obtain ⟨p, hp, rfl, rfl⟩ := hex
    obtain ⟨h1, h2⟩ := dealProblems_pays h p hp
    obtain ⟨q, hq, hn⟩ := List.any_eq_true.mp h2
    have hcov := dealProblems_covered h
    simp only [Deal.covered, List.all_eq_true, decide_eq_true_eq] at hcov
    have := hcov p.src h1 q hq
    have hn' : q.name = p.res := by simpa using hn
    rwa [hn'] at this

theorem depositEntries_inflow (id : Nat) (d : Deal) (i : Seat) (r : Res) :
    inflow (depositEntries id d) (.deposit id i) r = d.depositOf i r := by
  unfold depositEntries Deal.depositOf
  generalize d.deposits = L
  induction L with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, inflow_cons, ih, List.filter_cons, Bool.and_eq_true, beq_iff_eq,
      Account.deposit.injEq, true_and]
    split <;> simp

theorem depositEntries_outflow (id k : Nat) (d : Deal) (i : Seat) (r : Res) :
    outflow (depositEntries id d) (.deposit k i) r = 0 := by
  apply outflow_eq_zero'
  intro x hx h1 _
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  cases h1

/-! ## The turn change and the round -/

/-- A deal that survives a round's end has a round left to pay, and the round moves on. -/
theorem last_turn_survivor {s : State G} (hl : s.isLastTurn = true) (roll : Nat) {d : ActiveDeal}
    (hd : d ∈ (startNextTurn s roll).deals) :
    (startNextTurn s roll).round = s.round + 1 ∧ s.round < d.lastRound := by
  have hp := isLastTurn_phase hl
  have hs : nextStage s = if G.rounds ≤ s.round then .gameOver else .newRound := by
    unfold nextStage
    rw [hp]
    simp [hl]
  by_cases hr : G.rounds ≤ s.round
  · simp only [hr, ↓reduceIte] at hs
    unfold startNextTurn at hd
    rw [hs] at hd
    cases hd
  · simp only [hr, ↓reduceIte] at hs
    have hround := (startNextTurn_newRound (roll := roll) hs).2.1
    unfold startNextTurn at hd
    rw [hs] at hd
    have := (List.mem_filter.mp hd).2
    exact ⟨hround, by simpa using this⟩

/-- Only the last turn of a round moves the round on. -/
theorem startNextTurn_round_notLast {s : State G} (hl : s.isLastTurn = false)
    (he : s.phase ≠ .ended) (roll : Nat) : (startNextTurn s roll).round = s.round := by
  rcases nextStage_cases he with ⟨_, ⟨i, hs, _⟩ | ⟨hs, _⟩⟩ | ⟨hp, ⟨_, hs⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _⟩⟩
  · exact (startNextTurn_setupTurn hs).2
  · exact (startNextTurn_firstRound hs).2.1
  · exact (startNextTurn_sameRound hs).2.1
  · simp [State.isLastTurn, hp, h1] at hl
  · simp [State.isLastTurn, hp, h1] at hl

/-! ## The invariant step -/

theorem worstCase_congr {s s' : State G} (hr : s'.round = s.round) (d : ActiveDeal) (i : Seat)
    (r : Res) : s'.worstCase d i r = s.worstCase d i r := by
  simp only [State.worstCase, State.roundsLeft, hr]

theorem Cover.endTurn {s s' : State G} {e : Event} (hc : Cover s) (hi : IdInv s)
    (hend : EndsTurn s e) (he : s.phase ≠ .ended) (h : Engine.step G s e = .ok s') : Cover s' := by
  obtain ⟨b, hb, hs⟩ := step_endsTurn hend h
  subst hs
  intro d hd i r
  have hd0 : d ∈ s.deals := List.Sublist.subset (startNextTurn_deals_sublist'
    ({ s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade) } : State G) _) hd
  have hbal := postAll_balance hb (.deposit d.id i) r
  have hcov := hc d hd0 i r
  simp only [State.balance] at hcov ⊢
  simp only [startNextTurn_books]
  cases hl : s.isLastTurn with
  | true =>
    obtain ⟨H, hT, hH⟩ := turnEntries_last hl (rollAt G s.seed s.rollsMade)
    obtain ⟨hround, hlt⟩ := last_turn_survivor (s := { s with books := b, journal := _ }) hl _ hd
    dsimp only at hround hlt
    have hzero1 : outflow s.roundEndLawEntries (.deposit d.id i) r = 0 := by
      apply outflow_eq_zero'
      intro x hx h1 _
      exact (lawEntries_form _ _ x hx).2.1 _ _ h1
    have hzero2 : outflow (s.closingDeals.flatMap
        (s.afterPosting (s.duePayments ++ s.roundEndLawEntries)).refundEntries)
        (.deposit d.id i) r = 0 := by
      apply outflow_eq_zero'
      intro x hx h1 _
      obtain ⟨d2, hd2, hx⟩ := List.mem_flatMap.mp hx
      obtain ⟨_, j, _, h3, _⟩ := refundEntries_form hx
      rw [h3] at h1
      injection h1 with h4 _
      exact closing_gone (s := { s with books := b, journal := _ }) hl hi.deal_nodup hd2 _ d hd h4.symm
    have hzero3 : outflow H (.deposit d.id i) r = 0 := by
      apply outflow_eq_zero'
      intro x hx h1 _
      exact (harvestEntries_form (hH x hx)).1 _ _ h1
    rw [hT, outflow_append, outflow_append, outflow_append, hzero1, hzero2, hzero3] at hbal
    have hle := due_outflow_le_owed hi.deal_nodup hd0 i r
    simp only [State.worstCase, State.roundsLeft] at hcov ⊢
    rw [hround]
    obtain ⟨k, hk⟩ : ∃ k, d.lastRound = s.round + k + 1 := ⟨d.lastRound - s.round - 1, by omega⟩
    have e1 : d.lastRound + 1 - (s.round + 1) = k + 1 := by omega
    have e2 : d.lastRound + 1 - s.round = k + 2 := by omega
    rw [e1]
    rw [e2] at hcov
    simp only [Nat.add_mul, Nat.one_mul] at hcov ⊢
    rw [show 2 * d.deal.owedPerRound i r = d.deal.owedPerRound i r + d.deal.owedPerRound i r by omega] at hcov
    omega
  | false =>
    have hround := startNextTurn_round_notLast (G := G)
      (s := { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade) })
      hl he (rollAt G s.seed s.rollsMade)
    dsimp only at hround
    have hz : outflow (turnEntries s (rollAt G s.seed s.rollsMade)) (.deposit d.id i) r = 0 := by
      apply outflow_eq_zero'
      intro x hx h1 _
      rcases mem_turnEntries hx with ⟨hl2, _⟩ | hx
      · rw [hl] at hl2
        cases hl2
      · exact (harvestEntries_form hx).1 _ _ h1
    rw [worstCase_congr hround]
    change s.worstCase d i r ≤ _ at hcov
    omega

theorem Cover.act {s s' : State G} {e : Event} (hc : Cover s) (hcore : Core s) (hi : IdInv s)
    (hend : ¬ EndsTurn s e) (h : Engine.step G s e = .ok s') : Cover s' := by
  obtain ⟨_, s1, hb, hf⟩ := step_act h hend
  obtain ⟨⟨es, hj, hbk, _⟩, _⟩ := step_posted hcore h
  have hne : newEntries s s' = es := newEntries_of hj
  have fa := act_frame hb hf
  intro d hd i r
  have hz : outflow es (.deposit d.id i) r = 0 := by
    apply outflow_eq_zero'
    intro x hx h1 _
    have hv := step_vconj hi h (x := x) (by rw [hne]; exact hx)
    rcases hv.2.1 _ _ h1 with hr | hr
    · obtain ⟨k, j, h3, _, _, h6⟩ := hv.2.2.2.1 hr
      rw [h1] at h3
      injection h3 with h4 _
      exact h6 d hd h4
    · exact hend (hv.2.2.1 hr.1).1
  have hbal := postAll_balance hbk (.deposit d.id i) r
  rw [hz] at hbal
  simp only [State.balance]
  rw [worstCase_congr fa.round]
  -- `s'` is `s1` with its action counted, because `d` is still running.
  have hds1 : s'.deals = s1.deals ∧ s'.books = s1.books := by
    rcases finish_cases hf with rfl | ⟨w, hw⟩
    · exact ⟨rfl, rfl⟩
    · obtain ⟨_, _, rfl⟩ := endGame_ok hw
      cases hd
  rw [hds1.1] at hd
  rcases body_deals_cases hb with ⟨hd2, _⟩ | ⟨_, id, _, _, hd2⟩ | ⟨seat, id, dl, hsign, hst⟩
  · rw [hd2] at hd
    have := hc d hd i r
    simp only [State.balance] at this
    omega
  · rw [hd2] at hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    have hid : (if d0.id == id then
        { d0 with lastRound := Nat.min d0.lastRound (s.round + d0.deal.exitNotice) } else d0).id = d0.id := by
      split <;> rfl
    have hdeal : (if d0.id == id then
        { d0 with lastRound := Nat.min d0.lastRound (s.round + d0.deal.exitNotice) } else d0).deal = d0.deal := by
      split <;> rfl
    have hlast : (if d0.id == id then
        { d0 with lastRound := Nat.min d0.lastRound (s.round + d0.deal.exitNotice) } else d0).lastRound ≤ d0.lastRound := by
      split
      · simp only [Nat.min_def]; split <;> omega
      · exact Nat.le_refl _
    rw [hid] at hbal ⊢
    have := hc d0 hd0 i r
    simp only [State.balance, State.worstCase, State.roundsLeft] at this ⊢
    rw [hdeal]
    have hle := Nat.mul_le_mul_right (d0.deal.owedPerRound i r)
      (show (if d0.id == id then
        { d0 with lastRound := Nat.min d0.lastRound (s.round + d0.deal.exitNotice) } else d0).lastRound + 1 - s.round ≤
        d0.lastRound + 1 - s.round by omega)
    omega
  · obtain ⟨_, hprob, b0, hb0, hs1⟩ := startDeal_ok hst
    rw [hs1] at hd
    cases List.mem_append.mp hd with
    | inl hold =>
      have := hc d hold i r
      simp only [State.balance] at this
      omega
    | inr hnew =>
      simp only [List.mem_singleton] at hnew
      subst hnew
      have hs'b : s'.books = b0 := by rw [hds1.2, hs1]
      have hbal2 := postAll_balance hb0 (.deposit s.dealsStarted i) r
      rw [depositEntries_outflow, depositEntries_inflow] at hbal2
      obtain ⟨_, hrounds⟩ := dealProblems_shape hprob
      have hcov := new_deal_covered hprob i r
      simp only [State.worstCase, State.roundsLeft]
      have e1 : s.round + dl.rounds - 1 + 1 - s.round = dl.rounds := by omega
      rw [e1, hs'b]
      simp only at *
      omega

theorem Cover.step {s s' : State G} {e : Event} (hc : Cover s) (hcore : Core s) (hi : IdInv s)
    (h : Engine.step G s e = .ok s') : Cover s' := by
  by_cases hend : EndsTurn s e
  · exact Cover.endTurn hc hi hend (step_not_ended h) h
  · exact Cover.act hc hcore hi hend h

end Charter.Proofs
