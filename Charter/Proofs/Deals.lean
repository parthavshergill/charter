import Charter.Proofs.Replay

/-!
# Every deal ends

When a deal ends, its deposits are empty. Only a signer's real resources can ever be in a deposit,
and refunds move all of those.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## More about posting -/

theorem postAll_append_some {b b' : Books} {xs ys : List Entry}
    (h : b.postAll (xs ++ ys) = some b') : ∃ b1, b.postAll xs = some b1 ∧ b1.postAll ys = some b' := by
  rw [postAll_append] at h
  cases hx : b.postAll xs with
  | none => simp [hx] at h
  | some b1 =>
    rw [hx] at h
    exact ⟨b1, rfl, by simpa using h⟩

theorem inflow_eq_zero' {es : List Entry} {a : Account} {r : Res}
    (h : ∀ x ∈ es, x.dst = a → x.res = r → False) : inflow es a r = 0 := by
  induction es with
  | nil => rfl
  | cons x t ih =>
    rw [inflow_cons, ih (fun y hy => h y (by simp [hy]))]
    split
    · rename_i hc
      exact (h x (by simp) hc.1 hc.2).elim
    · rfl

theorem amount_le_outflow {es : List Entry} {x : Entry} (hx : x ∈ es) :
    x.amount ≤ outflow es x.src x.res := by
  induction es with
  | nil => cases hx
  | cons y t ih =>
    rw [outflow_cons]
    cases List.mem_cons.mp hx with
    | inl h =>
      subst h
      simp
    | inr h =>
      have := ih h
      omega

/-! ## Refunds empty a deposit -/

/-- After refunds for a list of deals, the deposits of those deals hold nothing. -/
theorem refund_empties {t : State G} {L : List ActiveDeal} {d : ActiveDeal} (hd : d ∈ L) {i : Seat}
    (hi : i ∈ d.deal.signers) {q : ResourceDef} (hq : q ∈ G.resources) {b : Books}
    (hb : t.books.postAll (L.flatMap t.refundEntries) = some b) :
    b (.deposit d.id i) q.name = 0 := by
  have hbal := postAll_balance hb (.deposit d.id i) q.name
  have hin : inflow (L.flatMap t.refundEntries) (.deposit d.id i) q.name = 0 := by
    apply inflow_eq_zero'
    intro x hx h1 _
    obtain ⟨d2, _, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨_, j, _, _, h3⟩ := refundEntries_form hx
    rw [h3] at h1
    cases h1
  rw [hin] at hbal
  by_cases hz : t.books (.deposit d.id i) q.name = 0
  · omega
  · have hmem : ({ src := .deposit d.id i, dst := .player i, res := q.name
                   amount := t.balance (.deposit d.id i) q.name, reason := .refund } : Entry) ∈
        L.flatMap t.refundEntries := by
      refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
      refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
      refine List.mem_filterMap.mpr ⟨q, hq, ?_⟩
      have hz' : ¬ t.balance (.deposit d.id i) q.name = 0 := hz
      simp [hz']
    have := amount_le_outflow hmem
    change t.books (.deposit d.id i) q.name ≤ outflow _ (.deposit d.id i) q.name at this
    omega

/-! ## Where a running deal comes from -/

theorem step_dealsStarted_le {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    s.dealsStarted ≤ s'.dealsStarted := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    simp
  · have hs1 : s.dealsStarted ≤ s1.dealsStarted := by
      rcases body_deals_cases hb with ⟨_, hc⟩ | ⟨_, _, _, hc, _⟩ | ⟨_, _, _, _, hst⟩
      · omega
      · omega
      · obtain ⟨_, _, _, _, rfl⟩ := startDeal_ok hst
        simp
    rcases finish_cases hf with rfl | ⟨w, hw⟩
    · exact hs1
    · obtain ⟨_, _, rfl⟩ := endGame_ok hw
      exact hs1

/-- A running deal was running before, with the same id and terms, or this event started it. -/
theorem deal_origin {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') {d : ActiveDeal}
    (hd : d ∈ s'.deals) :
    (∃ d0 ∈ s.deals, d0.id = d.id ∧ d0.deal = d.deal) ∨
    (d.id = s.dealsStarted ∧ dealProblems s d.deal = [] ∧ ∃ b,
      s.books.postAll (depositEntries s.dealsStarted d.deal) = some b ∧ s'.books = b) := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨b, _, hs⟩ := endTurnNow_ok h
    subst hs
    have hd0 := startNextTurn_deals_sub _ _ hd
    exact Or.inl ⟨d, hd0, rfl, rfl⟩
  · have hds1 : d ∈ s1.deals ∧ s'.books = s1.books := by
      rcases finish_cases hf with rfl | ⟨w, hw⟩
      · exact ⟨hd, rfl⟩
      · obtain ⟨_, _, rfl⟩ := endGame_ok hw
        cases hd
    obtain ⟨hd1, hbooks⟩ := hds1
    rcases body_deals_cases hb with ⟨hc, _⟩ | ⟨_, _, _, _, hc⟩ | ⟨_, _, dl, _, hst⟩
    · rw [hc] at hd1
      exact Or.inl ⟨d, hd1, rfl, rfl⟩
    · rw [hc] at hd1
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd1
      refine Or.inl ⟨d0, hd0, ?_, ?_⟩ <;> (split <;> rfl)
    · obtain ⟨_, hprob, b0, hb0, hs1⟩ := startDeal_ok hst
      rw [hs1] at hd1 hbooks
      cases List.mem_append.mp hd1 with
      | inl hold => exact Or.inl ⟨d, hold, rfl, rfl⟩
      | inr hnew =>
        simp only [List.mem_singleton] at hnew
        subst hnew
        exact Or.inr ⟨rfl, hprob, b0, hb0, hbooks⟩

/-! ## The invariant -/

/-- A deposit holds something only if its deal has started, and then only a signer's real resource. -/
structure DepositInv (G : GameDef) (s : State G) : Prop where
  fresh : ∀ k i r, s.dealsStarted ≤ k → s.books (.deposit k i) r = 0
  shape : ∀ d ∈ s.deals, ∀ i r, (i ∉ d.deal.signers ∨ G.isRes r ≠ true) →
    s.books (.deposit d.id i) r = 0

theorem DepositInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    DepositInv G (initialState G seats serverSeed nonces) :=
  ⟨fun _ _ _ _ => rfl, fun _ hd => by cases hd⟩

/-- Money enters a deposit only when that deal starts. -/
theorem step_deposit_le {s s' : State G} {e : Event} (hc : Core s) (hi : IdInv s)
    (h : Engine.step G s e = .ok s') {k : Nat} (i : Seat) (r : Res)
    (hk : k ≠ s.dealsStarted ∨ ∀ a ∈ s'.deals, a.id ≠ k) :
    s'.books (.deposit k i) r ≤ s.books (.deposit k i) r := by
  obtain ⟨⟨es, hj, hbk, _⟩, _⟩ := step_posted hc h
  have hne : newEntries s s' = es := newEntries_of hj
  have hin : inflow es (.deposit k i) r = 0 := by
    apply inflow_eq_zero'
    intro x hx h1 _
    have hv := step_vconj hi h (x := x) (by rw [hne]; exact hx)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hk2, ⟨a, ha, hid, _⟩, _⟩ := hv.1 _ _ h1
    rcases hk with hk | hk
    · exact hk hk2
    · exact hk a ha hid
  have := postAll_balance hbk (.deposit k i) r
  omega

/-- A check that adds no problem passed. -/
theorem ite_nil {c : Prop} [Decidable c] {m : String}
    (h : (if c then [] else [m]) = ([] : List String)) : c := by
  by_cases hc : c
  · exact hc
  · simp [hc] at h

theorem depositOf_zero {s : State G} {d : Deal} (h : dealProblems s d = []) {i : Seat} {r : Res}
    (hc : i ∉ d.signers ∨ G.isRes r ≠ true) : d.depositOf i r = 0 := by
  simp only [dealProblems, List.append_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h5⟩, h6⟩, _⟩, _⟩, _⟩ := h
  have h5' : ∀ x ∈ d.deposits, d.signers.contains x.1 = true :=
    List.all_eq_true.mp (ite_nil h5)
  have h6' : ∀ x ∈ d.deposits, G.isRes x.2.1 = true :=
    List.all_eq_true.mp (ite_nil h6)
  have : d.deposits.filter (fun x => x.1 == i && x.2.1 == r) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    intro h1 h2
    rcases hc with hc | hc
    · have := h5' x hx
      rw [h1] at this
      exact hc (by simpa using this)
    · have := h6' x hx
      rw [h2] at this
      exact hc this
  simp [Deal.depositOf, this]

theorem DepositInv.step {s s' : State G} {e : Event} (hdep : DepositInv G s) (hc : Core s)
    (hi : IdInv s) (h : Engine.step G s e = .ok s') : DepositInv G s' := by
  have hi' := hi.step h
  have hmono := step_dealsStarted_le h
  constructor
  · intro k i r hk
    have hle := step_deposit_le hc hi h (k := k) i r
      (Or.inr fun a ha he => by
        have := hi'.deal_lt a ha
        omega)
    have := hdep.fresh k i r (by omega)
    omega
  · intro d hd i r hcase
    rcases deal_origin h hd with ⟨d0, hd0, hid, hdeal⟩ | ⟨hid, hprob, b, hb, hbooks⟩
    · have hlt := hi.deal_lt d0 hd0
      have hle := step_deposit_le hc hi h (k := d.id) i r (Or.inl (by omega))
      have := hdep.shape d0 hd0 i r (by rw [hdeal]; exact hcase)
      rw [hid] at this
      omega
    · have hbal := postAll_balance hb (.deposit s.dealsStarted i) r
      rw [depositEntries_outflow, depositEntries_inflow, depositOf_zero hprob hcase,
        hdep.fresh _ i r (Nat.le_refl _)] at hbal
      rw [hid, hbooks]
      omega

/-! ## A deal that ends -/

/-- A deal that a turn change removes is one of the deals closing at a round's end. -/
theorem gone_is_closing {s : State G} (he : s.phase ≠ .ended) (roll : Nat) {d : ActiveDeal}
    (hd : d ∈ s.deals) (hgone : ∀ d' ∈ (startNextTurn s roll).deals, d'.id ≠ d.id) :
    s.isLastTurn = true ∧ d ∈ s.closingDeals := by
  have kept : ∀ i, (nextStage s = .setupTurn i ∨ nextStage s = .firstRound ∨
      nextStage s = .sameRound i) → False := by
    intro i hs
    have hmem : d ∈ (startNextTurn s roll).deals := by
      unfold startNextTurn
      rcases hs with hs | hs | hs <;> rw [hs] <;> exact hd
    exact hgone d hmem rfl
  rcases nextStage_cases he with ⟨_, ⟨i, hs, _⟩ | ⟨hs, _⟩⟩ | ⟨hp, ⟨_, hs⟩ | ⟨h1, h2, hs⟩ | ⟨h1, h2, hs⟩⟩
  · exact (kept i (Or.inl hs)).elim
  · exact (kept 0 (Or.inr (Or.inl hs))).elim
  · exact (kept _ (Or.inr (Or.inr hs))).elim
  · refine ⟨by simp [State.isLastTurn, hp, h1], ?_⟩
    unfold State.closingDeals
    rw [ite_eq_right_of_eq_false _ _ (by simp; omega)]
    refine List.mem_filter.mpr ⟨hd, ?_⟩
    by_cases hlt : s.round < d.lastRound
    · refine (hgone d ?_ rfl).elim
      unfold startNextTurn
      rw [hs]
      exact List.mem_filter.mpr ⟨hd, by simpa using hlt⟩
    · simp only [decide_eq_true_eq]
      omega
  · refine ⟨by simp [State.isLastTurn, hp, h1], ?_⟩
    unfold State.closingDeals
    simp only [h2, ↓reduceIte]
    exact hd

/-- Commandment VI(c): when a deal ends, its deposits are empty. -/
theorem deal_ended_empty {s : State G} (hdep : DepositInv G s) (hc : Core s) (hi : IdInv s)
    {s' : State G} {e : Event} (h : Engine.step G s e = .ok s') {d : ActiveDeal} (hd : d ∈ s.deals)
    (hgone : ∀ d' ∈ s'.deals, d'.id ≠ d.id) (i : Seat) (r : Res) :
    s'.books (.deposit d.id i) r = 0 := by
  have hne : d.id ≠ s.dealsStarted := by
    have := hi.deal_lt d hd
    omega
  by_cases hcase : i ∉ d.deal.signers ∨ G.isRes r ≠ true
  · have h1 := step_deposit_le hc hi h (k := d.id) i r (Or.inl hne)
    have h2 := hdep.shape d hd i r hcase
    omega
  have hsig : i ∈ d.deal.signers := by
    by_cases hx : i ∈ d.deal.signers
    · exact hx
    · exact (hcase (Or.inl hx)).elim
  have hres : G.isRes r = true := by
    by_cases hx : G.isRes r = true
    · exact hx
    · exact (hcase (Or.inr hx)).elim
  obtain ⟨q, hq, hqn⟩ := List.any_eq_true.mp hres
  have hqn' : q.name = r := by simpa using hqn
  subst hqn'
  have hph := step_not_ended h
  rcases step_view h with ⟨hend, h2⟩ | ⟨hnot, _, s1, hb, hf⟩
  · obtain ⟨b, hbk, hs⟩ := endTurnNow_ok h2
    subst hs
    obtain ⟨hl, hcl⟩ := gone_is_closing (s := { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade) })
      hph _ hd hgone
    change s.isLastTurn = true at hl
    change d ∈ s.closingDeals at hcl
    obtain ⟨H, hT, hH⟩ := turnEntries_last hl (rollAt G s.seed s.rollsMade)
    rw [hT, ← List.append_assoc] at hbk
    obtain ⟨b1, h1, h2'⟩ := postAll_append_some hbk
    obtain ⟨b2, h3, h4⟩ := postAll_append_some h2'
    have hbook : (s.afterPosting (s.duePayments ++ s.roundEndLawEntries)).books = b1 :=
      afterPosting_books h1
    have hzero := refund_empties (t := s.afterPosting (s.duePayments ++ s.roundEndLawEntries))
      hcl hsig hq (b := b2) (by rw [hbook]; exact h3)
    have hbal := postAll_balance h4 (.deposit d.id i) q.name
    have hout : outflow H (.deposit d.id i) q.name = 0 := by
      apply outflow_eq_zero'
      intro x hx h5 _
      exact (rollEntries_form (hH x hx)).1 _ _ h5
    have hin : inflow H (.deposit d.id i) q.name = 0 := by
      apply inflow_eq_zero'
      intro x hx h5 _
      exact (rollEntries_form (hH x hx)).2.1 _ _ h5
    rw [hout, hin, hzero] at hbal
    simpa using hbal
  · rcases finish_cases' hf with rfl | ⟨hns, hnx, w, hw⟩
    · exfalso
      have hmem : ∃ d' ∈ s1.deals, d'.id = d.id := by
        rcases body_deals_cases hb with ⟨hc2, _⟩ | ⟨_, _, _, _, hc2⟩ | ⟨_, _, _, _, hst⟩
        · exact ⟨d, by rw [hc2]; exact hd, rfl⟩
        · rw [hc2]
          refine ⟨_, List.mem_map.mpr ⟨d, hd, rfl⟩, ?_⟩
          split <;> rfl
        · obtain ⟨_, _, _, _, hs1⟩ := startDeal_ok hst
          rw [hs1]
          exact ⟨d, List.mem_append_left _ hd, rfl⟩
      obtain ⟨d', hm, hid⟩ := hmem
      exact hgone d' hm hid
    · have hd1 : s1.deals = s.deals := by
        rcases body_deals_cases hb with ⟨hc2, _⟩ | ⟨a, c, hc2, _, _⟩ | ⟨a, c, _, hc2, _⟩
        · exact hc2
        · exact (hnx a c hc2).elim
        · exact (hns a c hc2).elim
      obtain ⟨bk, hbk, hs2⟩ := endGame_ok hw
      have hd2 : d ∈ (countAction s1 (seatOf e)).deals := by
        change d ∈ s1.deals
        rw [hd1]
        exact hd
      have := refund_empties hd2 hsig hq hbk
      rw [hs2]
      exact this

/-- Commandment VI: any signer can give notice at any time. -/
theorem exit_accepted {s : State G} (hc : Core s) (hnd : (s.deals.map (·.id)).Nodup) {d : ActiveDeal} (hd : d ∈ s.deals) {i : Seat}
    (hi : i ∈ d.deal.signers) (hPhase : s.phase = .actions)
    (hA : s.actionsThisTurn i < maxActionsPerTurn) :
    ∃ s', Engine.step G s (.exit i d.id) = .ok s' ∧
      ∀ d' ∈ s'.deals, d'.id = d.id → d'.lastRound ≤ s.round + d.deal.exitNotice := by
  have hseat : i ∈ s.turnOrder := (hc.deals d hd).signers i hi
  have hca : canAct s i = true := by simp [canAct, hseat, hA]
  have hany : s.deals.any (fun x => x.id == d.id && x.deal.signers.contains i) = true := by
    apply List.any_eq_true.mpr
    exact ⟨d, hd, by simpa using hi⟩
  have hbody : exitBody s i d.id = .ok { s with deals := s.deals.map fun x =>
      if x.id == d.id then { x with lastRound := Nat.min x.lastRound (s.round + x.deal.exitNotice) }
      else x } := by
    unfold exitBody
    simp only [hPhase, hany]
    rfl
  have hhas : ∀ (x y : ActiveDeal), x ∈ s.deals → y ∈ s.deals → x.id = y.id → x = y := fun _ _ hx hy he =>
    eq_of_id_eq (·.id) hnd hx hy he
  refine ⟨countAction { s with deals := s.deals.map fun x =>
      if x.id == d.id then { x with lastRound := Nat.min x.lastRound (s.round + x.deal.exitNotice) }
      else x } i, ?_, ?_⟩
  · unfold Engine.step
    rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
    simp only [act, hca, ↓reduceIte, hbody]
  · intro d' hd' hid
    change d' ∈ s.deals.map _ at hd'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd'
    have hxid : x.id = d.id := by
      revert hid
      split <;> exact id
    have hxd : x = d := hhas x d hx hd hxid
    subst hxd
    simp only [beq_self_eq_true, ↓reduceIte, Nat.min_def]
    split <;> omega

/-! ## A deal restricts only what its signers do -/

/-- A blocked build comes from a no-build term of a running deal the builder signed. -/
theorem blocked_build_has_term (s : State G) (p : Seat) (k : PieceKind) (loc : Loc)
    (h : s.blockedByDeal p k loc = true) :
    ∃ d ∈ s.deals, p ∈ d.deal.signers ∧ ∃ spots, Term.noBuild p k spots ∈ d.deal.terms := by
  obtain ⟨d, hd, hx⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hx
  obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp hx.2
  refine ⟨d, hd, by simpa using hx.1, ?_⟩
  cases t with
  | noBuild x k' spots =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨rfl, rfl⟩, _⟩ := hm
    exact ⟨spots, ht⟩
  | everyRound _ => cases hm
  | onBuild _ _ _ => cases hm
  | noTrade _ _ => cases hm

/-- A blocked trade comes from a no-trade term of a running deal, in which a signer named the other
seat. -/
theorem blocked_trade_has_term (s : State G) (a b : Seat) (h : s.tradeBlocked a b = true) :
    ∃ d ∈ s.deals, ∃ x y, Term.noTrade x y ∈ d.deal.terms ∧ x ∈ d.deal.signers ∧
      ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
  obtain ⟨d, hd, hx⟩ := List.any_eq_true.mp h
  obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp hx
  cases t with
  | noTrade x y =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hm
    exact ⟨d, hd, x, y, ht, by simpa using hm.1, hm.2⟩
  | everyRound _ => cases hm
  | onBuild _ _ _ => cases hm
  | noBuild _ _ _ => cases hm

/-- The per-deal form of the build clause implies the older form: a seat that signed no running deal
is never blocked from a build. -/
theorem no_deal_no_build_block {s : State G}
    (h : ∀ p k loc, s.blockedByDeal p k loc = true →
      ∃ d ∈ s.deals, p ∈ d.deal.signers ∧ ∃ spots, Term.noBuild p k spots ∈ d.deal.terms) :
    ∀ p k loc, (∀ d ∈ s.deals, p ∉ d.deal.signers) → s.blockedByDeal p k loc = false := by
  intro p k loc hp
  cases hb : s.blockedByDeal p k loc with
  | false => rfl
  | true =>
    obtain ⟨d, hd, hs, _⟩ := h p k loc hb
    exact (hp d hd hs).elim

/-- The per-deal form of the trade clause implies the older form: two seats that signed no running
deal are never blocked from trading with each other. -/
theorem no_deal_no_trade_block {s : State G}
    (h : ∀ a b, s.tradeBlocked a b = true →
      ∃ d ∈ s.deals, ∃ x y, Term.noTrade x y ∈ d.deal.terms ∧ x ∈ d.deal.signers ∧
        ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) :
    ∀ a b, (∀ d ∈ s.deals, a ∉ d.deal.signers ∧ b ∉ d.deal.signers) →
      s.tradeBlocked a b = false := by
  intro a b hp
  cases hb : s.tradeBlocked a b with
  | false => rfl
  | true =>
    obtain ⟨d, hd, x, y, _, hx, hc⟩ := h a b hb
    rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ((hp d hd).1 hx).elim
    · exact ((hp d hd).2 hx).elim

end Charter.Proofs
