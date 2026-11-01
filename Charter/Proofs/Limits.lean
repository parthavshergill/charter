import Charter.Proofs.Ledger

/-!
# The fixed limits

Laws in force and their size, open proposals per seat, and running deals stay within their limits.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-- The limits of `limits_hold`. -/
structure Limits (s : State G) : Prop where
  laws_len : s.laws.length ≤ maxLawsInForce
  laws_size : ∀ x ∈ s.laws, x.2.size ≤ maxLawSize
  open_len : ∀ seat, (s.openProposals.filter (·.by_ == seat)).length ≤ maxOpenPerSeat
  deals_len : s.deals.length ≤ maxActiveDeals

theorem lawProblems_nil {s : State G} {L : Law} (h : lawProblems G s L = []) :
    L.size ≤ maxLawSize ∧ (enact s.laws 0 L).length ≤ maxLawsInForce := by
  constructor
  · by_cases hc : L.size ≤ maxLawSize
    · exact hc
    · simp [lawProblems, hc] at h
  · by_cases hc : (enact s.laws 0 L).length ≤ maxLawsInForce
    · exact hc
    · simp [lawProblems, hc] at h

theorem enact_length (laws : List (Nat × Law)) (id : Nat) (L : Law) :
    (enact laws id L).length = (enact laws 0 L).length := by
  simp [enact]

theorem mem_enact {laws : List (Nat × Law)} {id : Nat} {L : Law} {x : Nat × Law}
    (h : x ∈ enact laws id L) : x ∈ laws ∨ x = (id, L) := by
  simp only [enact, List.mem_append, List.mem_filter, List.mem_singleton] at h
  exact h.imp (·.1) (fun x => x)

/-- Changing proposals without changing who made them keeps each seat's count. -/
theorem filter_by_map_length (L : List OpenProposal) (f : OpenProposal → OpenProposal)
    (hf : ∀ q, (f q).by_ = q.by_) (seat : Seat) :
    ((L.map f).filter (·.by_ == seat)).length = (L.filter (·.by_ == seat)).length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.filter_cons, hf]
    split <;> simp [ih]

theorem filter_by_sublist_le {L M : List OpenProposal} (h : L.Sublist M) (seat : Seat) :
    (L.filter (·.by_ == seat)).length ≤ (M.filter (·.by_ == seat)).length :=
  (h.filter _).length_le

theorem startNextTurn_openProposals_sublist (s : State G) (roll : Nat) :
    (startNextTurn s roll).openProposals.Sublist s.openProposals := by
  unfold startNextTurn
  split
  · exact List.Sublist.refl _
  · exact List.filter_sublist
  · exact List.filter_sublist
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem startNextTurn_deals_sublist (s : State G) (roll : Nat) :
    (startNextTurn s roll).deals.Sublist s.deals := by
  unfold startNextTurn
  split
  · exact List.Sublist.refl _
  · exact List.Sublist.refl _
  · exact List.Sublist.refl _
  · exact List.filter_sublist
  · exact List.nil_sublist _

theorem Limits.body {s s1 : State G} {e : Event} (hl : Limits s) (h : bodyOf s e = .ok s1) :
    Limits s1 := by
  cases e with
  | forceEndTurn => cases h
  | move p m =>
    cases m with
    | endTurn => cases h
    | place k loc =>
      rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
      · obtain ⟨_, rfl⟩ := setupBody_ok h
        exact ⟨hl.1, hl.2, hl.3, hl.4⟩
      · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
        exact ⟨hl.1, hl.2, hl.3, hl.4⟩
    | bankTrade a b =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok h
      obtain ⟨_, _, rfl⟩ := record_ok hr
      exact ⟨hl.1, hl.2, hl.3, hl.4⟩
    | offer t a b =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok h
      exact ⟨hl.1, hl.2, hl.3, hl.4⟩
    | accept i =>
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := acceptBody_ok h
      exact ⟨hl.1, hl.2, hl.3, hl.4⟩
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok h
      exact ⟨hl.1, hl.2, hl.3, hl.4⟩
  | propose seat b =>
    obtain ⟨_, hn, hc⟩ := proposeBody_ok h
    have hopen : ∀ (q : OpenProposal), q.by_ = seat → ∀ q0,
        ((s.openProposals ++ [q]).filter (·.by_ == q0)).length ≤ maxOpenPerSeat := by
      intro q hq q0
      simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
      have := hl.3 q0
      by_cases hs : seat = q0
      · subst hs
        simp only [hq, beq_self_eq_true, ite_true, List.length_cons, List.length_nil]
        omega
      · have : (q.by_ == q0) = false := by simp [hq, hs]
        simp only [this]
        simpa using hl.3 q0
    rcases hc with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
    · exact ⟨hl.1, hl.2, hopen _ rfl, hl.4⟩
    · exact ⟨hl.1, hl.2, hopen _ rfl, hl.4⟩
  | vote seat i y =>
    obtain ⟨_, p, L, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok h
    · have hf : ∀ q0, ((s.openProposals.filter (·.id != i)).filter (·.by_ == q0)).length
          ≤ maxOpenPerSeat := fun q0 => Nat.le_trans (filter_by_sublist_le List.filter_sublist q0) (hl.3 q0)
      unfold decideLaw
      simp only
      split
      · rename_i hpb
        have hnil := lawProblems_nil (by simpa using hpb)
        refine ⟨?_, ?_, hf, hl.4⟩
        · simp only
          rw [enact_length]
          exact hnil.2
        · intro x hx
          rcases mem_enact hx with hx | rfl
          · exact hl.2 x hx
          · exact hnil.1
      · exact ⟨hl.1, hl.2, hf, hl.4⟩
    · refine ⟨hl.1, hl.2, ?_, hl.4⟩
      intro q0
      simp only
      rw [filter_by_map_length]
      · exact hl.3 q0
      · intro q
        split <;> rfl
  | sign seat i =>
    obtain ⟨_, p, d, _, _, _, _, ⟨_, h⟩ | ⟨_, rfl⟩⟩ := signBody_ok h
    · obtain ⟨hc, _, _, _, rfl⟩ := startDeal_ok h
      have hd : s.deals.length < maxActiveDeals := by
        simp only [State.canStartDeal, Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.2
      refine ⟨hl.1, hl.2, ?_, ?_⟩
      · exact fun q0 => Nat.le_trans (filter_by_sublist_le List.filter_sublist q0) (hl.3 q0)
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    · refine ⟨hl.1, hl.2, ?_, hl.4⟩
      intro q0
      simp only
      rw [filter_by_map_length]
      · exact hl.3 q0
      · intro q
        split <;> rfl
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok h
    exact ⟨hl.1, hl.2, hl.3, by simpa using hl.4⟩

theorem Limits.step {s s' : State G} {e : Event} (hl : Limits s) (h : Engine.step G s e = .ok s') :
    Limits s' := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    refine ⟨by simpa using hl.1, by simpa using hl.2, ?_, ?_⟩
    · exact fun q0 => Nat.le_trans (filter_by_sublist_le (startNextTurn_openProposals_sublist _ _) q0)
        (hl.3 q0)
    · exact Nat.le_trans (startNextTurn_deals_sublist _ _).length_le hl.4
  · have h1 := hl.body hb
    rcases finish_cases hf with rfl | ⟨w, he⟩
    · exact ⟨h1.1, h1.2, h1.3, h1.4⟩
    · obtain ⟨_, _, rfl⟩ := endGame_ok he
      exact ⟨h1.1, h1.2, by simp [maxOpenPerSeat], by simp [maxActiveDeals]⟩

end Charter.Proofs
