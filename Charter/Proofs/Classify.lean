import Charter.Proofs.Ids
import Charter.Proofs.Exact

/-!
# Every entry has a known source

A law can move money only between seats, the treasury and the bank, never a deposit. A harvest pays
from the bank to a seat. A deal payment and a refund leave a deposit. These lemmas say which kind of
entry each engine helper can write. Commandment V follows.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-- This account is not a deposit. -/
def NotDeposit (a : Account) : Prop := ∀ k i, a ≠ .deposit k i

theorem party_account_notDeposit {env : LawEnv} {p : Party} {a : Account}
    (h : p.account env = some a) : NotDeposit a := by
  intro k i he
  subst he
  cases p <;> simp [Party.account] at h

/-- The form of every entry a law plans. -/
def LawForm (x : Entry) : Prop := x.reason = .lawEffect ∧ NotDeposit x.src ∧ NotDeposit x.dst

mutual
  theorem plan_form (s : State G) : ∀ (e : Effect) (env : LawEnv),
      ∀ x ∈ Effect.plan s e env, LawForm x
    | .transfer src dst r amount, env, x, hx => by
      simp only [Effect.plan] at hx
      split at hx
      · rename_i a b c ha hb _
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨rfl, party_account_notDeposit ha, party_account_notDeposit hb⟩
      · simp at hx
    | .movePiece .., _, x, hx => by simp [Effect.plan] at hx
    | .forEach c body, env, x, hx => by
      simp only [Effect.plan, List.mem_flatMap] at hx
      obtain ⟨p, _, hx⟩ := hx
      split at hx
      · exact planAll_form s body _ x hx
      · simp at hx
    | .when c body, env, x, hx => by
      simp only [Effect.plan] at hx
      split at hx
      · exact planAll_form s body _ x hx
      · simp at hx

  theorem planAll_form (s : State G) : ∀ (es : List Effect) (env : LawEnv),
      ∀ x ∈ Effect.planAll s es env, LawForm x
    | [], _, x, hx => by simp [Effect.planAll] at hx
    | e :: es, env, x, hx => by
      simp only [Effect.planAll, List.mem_append] at hx
      cases hx with
      | inl hx => exact plan_form s e env x hx
      | inr hx => exact planAll_form s es env x hx
end

theorem lawPlan_form (s : State G) (t : Trigger) (L : Law) :
    ∀ x ∈ Law.plan s t L, LawForm x := by
  intro x hx
  simp only [Law.plan, List.mem_flatMap] at hx
  obtain ⟨c, _, hx⟩ := hx
  exact planAll_form s _ _ x hx

theorem settle_form {s : State G} {es : List Entry} (h : ∀ x ∈ es, LawForm x) :
    ∀ x ∈ settle s es, LawForm x := by
  intro x hx
  obtain ⟨e, he, h1, h2, _, h4⟩ := mem_settle hx
  have := h e he
  exact ⟨h4.trans this.1, h1 ▸ this.2.1, h2 ▸ this.2.2⟩

theorem lawEntries_form (s : State G) (t : Trigger) : ∀ x ∈ lawEntries s t, LawForm x :=
  settle_form (by
    intro x hx
    simp only [List.mem_flatMap] at hx
    obtain ⟨L, _, hx⟩ := hx
    exact lawPlan_form s t L.2 x hx)

/-- What the bank pays out for a roll. -/
theorem baseHarvest_form {s : State G} {roll : Nat} {x : Entry} (hx : x ∈ baseHarvest s roll) :
    x.src = .bank ∧ x.reason = .harvest ∧ ∃ o, x.dst = .player o := by
  obtain ⟨e, he, h1, h2, _, h4⟩ := mem_settle hx
  simp only [List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨_, _, q, _, hm⟩ := he
  split at hm
  · split at hm
    · simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨h1, h4, q.owner, h2⟩
    · cases hm
  · cases hm

/-- A harvest is the bank's payments, then what laws do in reaction. -/
theorem harvestEntries_cases {s : State G} {roll : Nat} {x : Entry}
    (hx : x ∈ harvestEntries s roll) : x ∈ baseHarvest s roll ∨ LawForm x := by
  simp only [harvestEntries, List.mem_append] at hx
  refine hx.imp id (fun hx => settle_form ?_ x hx)
  intro y hy
  simp only [List.mem_flatMap] at hy
  obtain ⟨b, _, hy⟩ := hy
  split at hy
  · simp only [List.mem_flatMap] at hy
    obtain ⟨L, _, hy⟩ := hy
    exact lawPlan_form _ _ L.2 y hy
  · simp at hy

theorem harvestEntries_form {s : State G} {roll : Nat} {x : Entry}
    (hx : x ∈ harvestEntries s roll) : NotDeposit x.src ∧ NotDeposit x.dst ∧
      x.reason ≠ .dealPayment ∧ x.reason ≠ .refund := by
  rcases harvestEntries_cases hx with h | h
  · obtain ⟨h1, h2, o, h3⟩ := baseHarvest_form h
    rw [h1, h2, h3]
    exact ⟨fun _ _ he => (by cases he), fun _ _ he => (by cases he), by simp, by simp⟩
  · exact ⟨h.2.1, h.2.2, by rw [h.1]; simp, by rw [h.1]; simp⟩

/-- A roll is the harvest, then what laws do in reaction to the roll. -/
theorem rollEntries_cases {s : State G} {roll : Nat} {x : Entry}
    (hx : x ∈ rollEntries s roll) : x ∈ harvestEntries s.atRoll roll ∨ LawForm x := by
  simp only [rollEntries, List.mem_append] at hx
  refine hx.imp id (fun hx => ?_)
  cases hn : s.nextRoller with
  | none => simp [hn] at hx
  | some a =>
    simp only [hn] at hx
    exact lawEntries_form _ _ x hx

theorem rollEntries_form {s : State G} {roll : Nat} {x : Entry}
    (hx : x ∈ rollEntries s roll) : NotDeposit x.src ∧ NotDeposit x.dst ∧
      x.reason ≠ .dealPayment ∧ x.reason ≠ .refund := by
  rcases rollEntries_cases hx with h | h
  · exact harvestEntries_form h
  · exact ⟨h.2.1, h.2.2, by rw [h.1]; simp, by rw [h.1]; simp⟩

/-- A deal's payment comes from a term of a running deal. -/
theorem duePayments_form {s : State G} {x : Entry} (hx : x ∈ s.duePayments) :
    x.reason = .dealPayment ∧ ∃ d ∈ s.deals, ∃ p ∈ d.deal.allPays,
      x.src = .deposit d.id p.src ∧ x.res = p.res ∧ x.amount = p.amount ∧ x.dst = p.dst.account := by
  simp only [State.duePayments, List.mem_flatMap] at hx
  obtain ⟨d, hd, t, ht, hx⟩ := hx
  have hsub : ∀ p ∈ t.pays, p ∈ d.deal.allPays := by
    intro p hp
    simp only [Deal.allPays, List.mem_flatMap]
    exact ⟨t, ht, hp⟩
  have key : ∀ ps, (∀ p ∈ ps, p ∈ d.deal.allPays) → x ∈ State.payEntries d.id ps →
      x.reason = .dealPayment ∧ ∃ d ∈ s.deals, ∃ p ∈ d.deal.allPays,
      x.src = .deposit d.id p.src ∧ x.res = p.res ∧ x.amount = p.amount ∧
        x.dst = p.dst.account := by
    intro ps hps hx
    simp only [State.payEntries, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨rfl, d, hd, p, hps p hp, rfl, rfl, rfl, rfl⟩
  cases t with
  | everyRound ps => exact key ps hsub hx
  | onBuild a k ps =>
    simp only at hx
    split at hx
    · exact key ps hsub hx
    · simp at hx
  | noBuild _ _ _ => simp at hx
  | noTrade _ _ => simp at hx

theorem payee_notDeposit (p : Payee) : NotDeposit p.account := by
  intro k i he
  cases p <;> cases he

/-- A refund goes from a signer's deposit to that signer. -/
theorem refundEntries_form {s : State G} {d : ActiveDeal} {x : Entry} (hx : x ∈ s.refundEntries d) :
    x.reason = .refund ∧ ∃ i ∈ d.deal.signers, x.src = .deposit d.id i ∧ x.dst = .player i := by
  simp only [State.refundEntries, List.mem_flatMap, List.mem_filterMap] at hx
  obtain ⟨i, hi, r, _, hm⟩ := hx
  split at hm
  · cases hm
  · simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨rfl, i, hi, rfl, rfl⟩

theorem closingDeals_mem {s : State G} {d : ActiveDeal} (h : d ∈ s.closingDeals) : d ∈ s.deals := by
  unfold State.closingDeals at h
  split at h
  · exact h
  · exact (List.mem_filter.mp h).1

theorem isLastTurn_phase {s : State G} (h : s.isLastTurn = true) : s.phase = .actions := by
  simp only [State.isLastTurn, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- After a round's end, a deal that closes is gone. -/
theorem closing_gone {s : State G} (hl : s.isLastTurn = true) (hnd : (s.deals.map (·.id)).Nodup)
    {d : ActiveDeal} (hd : d ∈ s.closingDeals) (roll : Nat) :
    ∀ d' ∈ (startNextTurn s roll).deals, d'.id ≠ d.id := by
  have hp := isLastTurn_phase hl
  have hs : nextStage s = if G.rounds ≤ s.round then .gameOver else .newRound := by
    unfold nextStage
    rw [hp]
    simp [hl]
  by_cases hr : G.rounds ≤ s.round
  · simp only [hr, ↓reduceIte] at hs
    intro d' hd'
    unfold startNextTurn at hd'
    rw [hs] at hd'
    cases hd'
  · simp only [hr, ↓reduceIte] at hs
    intro d' hd' he
    unfold startNextTurn at hd'
    rw [hs] at hd'
    have h1 := List.mem_filter.mp hd'
    have h2 : d ∈ s.deals := closingDeals_mem hd
    have heq : d' = d := eq_of_id_eq (·.id) hnd h1.1 h2 he
    subst heq
    unfold State.closingDeals at hd
    simp only [hr, ↓reduceIte] at hd
    have h3 := (List.mem_filter.mp hd).2
    have h4 := h1.2
    simp only [decide_eq_true_eq] at h3 h4
    omega

theorem mem_turnEntries {s : State G} {roll : Nat} {x : Entry} (hx : x ∈ turnEntries s roll) :
    (s.isLastTurn = true ∧ x ∈ s.roundEndEntries) ∨
    x ∈ rollEntries s.afterRoundEnd roll := by
  have before : x ∈ s.entriesBeforeRoll → s.isLastTurn = true ∧ x ∈ s.roundEndEntries := by
    intro h
    unfold State.entriesBeforeRoll at h
    split at h
    · exact ⟨by assumption, h⟩
    · simp at h
  simp only [turnEntries] at hx
  split at hx
  · cases List.mem_append.mp hx with
    | inl h => exact Or.inl (before h)
    | inr h => exact Or.inr h
  · exact Or.inl (before hx)

theorem mem_roundEndEntries {s : State G} {x : Entry} (hx : x ∈ s.roundEndEntries) :
    x ∈ s.duePayments ∨ x ∈ s.roundEndLawEntries ∨
    ∃ d ∈ s.closingDeals, x ∈ (s.afterPosting (s.duePayments ++ s.roundEndLawEntries)).refundEntries d := by
  simp only [State.roundEndEntries, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## Commandment V, entry by entry -/

/-- The ways money can leave seat `i`'s own account. -/
def SeatOut (s s' : State G) (e : Event) (x : Entry) (i : Seat) : Prop :=
  (x.reason = .cost ∧ ∃ k loc, e = .move i (.place k loc) ∧ x ∈ s.costEntries i k) ∨
  (x.reason = .trade ∧
    ((∃ give get, e = .move i (.bankTrade give get) ∧ x ∈ s.bankTradeEntries i give get) ∨
     (∃ p id o, e = .move p (.accept id) ∧ s.offers.find? (·.id == id) = some o ∧
       (i = o.src ∨ i = p) ∧ x ∈ offerEntries o p))) ∨
  (∃ k, FundsDeal s s' e x k i) ∨
  (x.reason = .lawEffect ∧
    ((∃ b k loc, e = .move b (.place k loc) ∧
       x ∈ lawEntries (s.afterPosting (s.costEntries b k)) (.build b k)) ∨
     (EndsTurn s e ∧
       (x ∈ s.roundEndLawEntries ∨
        x ∈ rollEntries s.afterRoundEnd (rollAt G s.seed s.rollsMade))) ∨
     (∃ L, LawPasses s e L ∧ x ∈ s.decreeEntries L)))

/-- Everything commandment V says about one entry. -/
def VConj (s s' : State G) (e : Event) (x : Entry) : Prop :=
  (∀ k i, x.dst = .deposit k i → FundsDeal s s' e x k i) ∧
  (∀ k i, x.src = .deposit k i →
    x.reason = .refund ∨
    (x.reason = .dealPayment ∧ ∃ d ∈ s.deals, d.id = k ∧ ∃ p ∈ d.deal.allPays,
      p.src = i ∧ p.res = x.res ∧ p.amount = x.amount ∧ x.dst = p.dst.account)) ∧
  (x.reason = .dealPayment →
    EndsTurn s e ∧ s.isLastTurn = true ∧ ∃ k i, x.src = .deposit k i) ∧
  (x.reason = .refund → ∃ k i, x.src = .deposit k i ∧ x.dst = .player i ∧
    (∃ d ∈ s.deals, d.id = k) ∧ ∀ d' ∈ s'.deals, d'.id ≠ k) ∧
  (∀ i, x.src = .player i → SeatOut s s' e x i)

/-- An entry that touches no deposit and is not a payment or refund needs only the last rule. -/
theorem vconj_plain {s s' : State G} {e : Event} {x : Entry} (h1 : NotDeposit x.src)
    (h2 : NotDeposit x.dst) (h3 : x.reason ≠ .dealPayment) (h4 : x.reason ≠ .refund)
    (h5 : ∀ i, x.src = .player i → SeatOut s s' e x i) : VConj s s' e x :=
  ⟨fun k i h => absurd h (h2 k i), fun k i h => absurd h (h1 k i), fun h => absurd h h3,
    fun h => absurd h h4, h5⟩

theorem vconj_refund {s s' : State G} {e : Event} {x : Entry} {d : ActiveDeal} (hd : d ∈ s.deals)
    (hgone : ∀ d' ∈ s'.deals, d'.id ≠ d.id) {i : Seat} (hr : x.reason = .refund)
    (hs : x.src = .deposit d.id i) (ht : x.dst = .player i) : VConj s s' e x := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k j h
    rw [ht] at h
    cases h
  · intro _ _ _
    exact Or.inl hr
  · intro h
    rw [hr] at h
    cases h
  · intro _
    exact ⟨d.id, i, hs, ht, ⟨d, hd, rfl⟩, hgone⟩
  · intro j h
    rw [hs] at h
    cases h

theorem vconj_payment {s s' : State G} {e : Event} {x : Entry} (hx : x ∈ s.duePayments)
    (hend : EndsTurn s e) (hl : s.isLastTurn = true) : VConj s s' e x := by
  obtain ⟨hr, d, hd, p, hp, h1, h2, h3, h4⟩ := duePayments_form hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k i h
    rw [h4] at h
    exact absurd h (payee_notDeposit _ _ _)
  · intro k i h
    rw [h1] at h
    injection h with hk hi
    exact Or.inr ⟨hr, d, hd, hk, p, hp, hi, h2.symm, h3.symm, h4⟩
  · intro _
    exact ⟨hend, hl, _, _, h1⟩
  · intro h
    rw [hr] at h
    cases h
  · intro j h
    rw [h1] at h
    cases h

/-- A law's entry at a turn change. -/
theorem vconj_turnLaw {s s' : State G} {e : Event} {x : Entry} (hf : LawForm x) (hend : EndsTurn s e)
    (hx : x ∈ s.roundEndLawEntries ∨
      x ∈ rollEntries s.afterRoundEnd (rollAt G s.seed s.rollsMade)) :
    VConj s s' e x :=
  vconj_plain hf.2.1 hf.2.2 (by rw [hf.1]; simp) (by rw [hf.1]; simp)
    (fun _ _ => Or.inr (Or.inr (Or.inr ⟨hf.1, Or.inr (Or.inl ⟨hend, hx⟩)⟩)))

/-- Every entry of a turn change is allowed. -/
theorem vconj_turn {s : State G} {e : Event} (hend : EndsTurn s e)
    (hnd : (s.deals.map (·.id)).Nodup) {b : Books} {j : List Entry} {ps : List Piece} {x : Entry}
    (hx : x ∈ turnEntries s (rollAt G s.seed s.rollsMade)) :
    VConj s (startNextTurn { s with books := b, journal := j, pieces := ps } (rollAt G s.seed s.rollsMade)) e x := by
  rcases mem_turnEntries hx with ⟨hl, hx⟩ | hx
  · rcases mem_roundEndEntries hx with h | h | ⟨d, hd, h⟩
    · exact vconj_payment h hend hl
    · exact vconj_turnLaw (lawEntries_form _ _ x h) hend (Or.inl h)
    · obtain ⟨hr, i, _, h1, h2⟩ := refundEntries_form h
      exact vconj_refund (closingDeals_mem hd)
        (closing_gone (s := { s with books := b, journal := j, pieces := ps }) hl hnd hd _) hr h1 h2
  · obtain ⟨h1, h2, h3, h4⟩ := rollEntries_form hx
    refine vconj_plain h1 h2 h3 h4 ?_
    intro i hi
    have hlaw : LawForm x := by
      rcases rollEntries_cases hx with hh | hb
      · rcases harvestEntries_cases hh with hb | hb
        · have := (baseHarvest_form hb).1
          rw [hi] at this
          cases this
        · exact hb
      · exact hb
    exact Or.inr (Or.inr (Or.inr ⟨hlaw.1, Or.inr (Or.inl ⟨hend, Or.inr hx⟩)⟩))

/-- The entries of a bundle go between the two accounts given. -/
theorem mem_bundleEntries {a b : Account} {bd : Bundle} {r : Reason} {x : Entry}
    (h : x ∈ bundleEntries a b bd r) : x.src = a ∧ x.dst = b ∧ x.reason = r := by
  simp only [bundleEntries, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- Every entry of an event body is allowed. If the event is a signature, `s'` must keep the deals
of the body's result. -/
theorem body_vconj {s s1 s' : State G} {e : Event} (hb : bodyOf s e = .ok s1)
    (hs' : ∀ seat id, e = .sign seat id → s'.deals = s1.deals) :
    ∃ es, s1.journal = s.journal ++ es ∧ ∀ x ∈ es, VConj s s' e x := by
  have notDepPlayer : ∀ i, NotDeposit (.player i) := fun _ _ _ he => by cases he
  have notDepBank : NotDeposit .bank := fun _ _ he => by cases he
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
          have hc' := hc
          simp only [State.costEntries, List.mem_map] at hc'
          obtain ⟨_, _, rfl⟩ := hc'
          refine vconj_plain (notDepPlayer _) notDepBank (by simp) (by simp) ?_
          intro i hi
          injection hi with hi
          subst hi
          exact Or.inl ⟨rfl, k, loc, rfl, hc⟩
        | inr hl =>
          have hf := lawEntries_form _ _ x hl
          exact vconj_plain hf.2.1 hf.2.2 (by rw [hf.1]; simp) (by rw [hf.1]; simp)
            (fun _ _ => Or.inr (Or.inr (Or.inr ⟨hf.1, Or.inl ⟨p, k, loc, rfl, hl⟩⟩)))
    | bankTrade a c =>
      obtain ⟨_, _, _, _, _, hr⟩ := bankTradeBody_ok hb
      obtain ⟨_, _, rfl⟩ := record_ok hr
      refine ⟨_, rfl, ?_⟩
      intro x hx
      have hx' := hx
      simp only [State.bankTradeEntries, List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl
      · refine vconj_plain (notDepPlayer _) notDepBank (by simp) (by simp) ?_
        intro i hi
        injection hi with hi
        subst hi
        exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨a, c, rfl, hx⟩⟩)
      · refine vconj_plain notDepBank (notDepPlayer _) (by simp) (by simp) ?_
        intro i hi
        cases hi
    | offer t a c =>
      obtain ⟨_, _, rfl⟩ := offerBody_ok hb
      exact ⟨[], by simp, by simp⟩
    | accept id =>
      obtain ⟨_, o, ho, _, _, _, _, _, rfl⟩ := acceptBody_ok hb
      refine ⟨_, rfl, ?_⟩
      intro x hx
      cases List.mem_append.mp hx with
      | inl h =>
        obtain ⟨h1, h2, h3⟩ := mem_bundleEntries h
        refine vconj_plain (h1 ▸ notDepPlayer _) (h2 ▸ notDepPlayer _) (by rw [h3]; simp) (by rw [h3]; simp) ?_
        intro i hi
        rw [h1] at hi
        injection hi with hi
        exact Or.inr (Or.inl ⟨h3, Or.inr ⟨p, id, o, rfl, ho, Or.inl hi.symm, hx⟩⟩)
      | inr h =>
        obtain ⟨h1, h2, h3⟩ := mem_bundleEntries h
        refine vconj_plain (h1 ▸ notDepPlayer _) (h2 ▸ notDepPlayer _) (by rw [h3]; simp) (by rw [h3]; simp) ?_
        intro i hi
        rw [h1] at hi
        injection hi with hi
        exact Or.inr (Or.inl ⟨h3, Or.inr ⟨p, id, o, rfl, ho, Or.inr hi.symm, hx⟩⟩)
    | cancel i =>
      obtain ⟨_, _, rfl⟩ := cancelBody_ok hb
      exact ⟨[], by simp, by simp⟩
    | declare r n =>
      obtain ⟨_, _, rfl⟩ := declareBody_ok hb
      exact ⟨[], by simp, by simp⟩
  | propose seat b =>
    obtain ⟨_, _, ⟨L, rfl, _, rfl⟩ | ⟨_, _, _, _, rfl⟩⟩ := proposeBody_ok hb
    · exact ⟨[], by simp [addProposal], by simp⟩
    · exact ⟨[], by simp [addProposal], by simp⟩
  | vote seat i y =>
    have hv : voteBody s seat i y = .ok s1 := hb
    rcases vote_view hv with ⟨L, hp, _, hs1⟩ | ⟨_, _, hj, _⟩
    · refine ⟨s.decreeEntries L, by rw [hs1], ?_⟩
      intro x hx
      have hf : LawForm x := settle_form (fun z hz => lawPlan_form s .now L z hz) x hx
      exact vconj_plain hf.2.1 hf.2.2 (by rw [hf.1]; simp) (by rw [hf.1]; simp)
        (fun _ _ => Or.inr (Or.inr (Or.inr ⟨hf.1, Or.inr (Or.inr ⟨L, hp, hx⟩)⟩)))
    · exact ⟨[], by simp [hj], by simp⟩
  | sign seat i =>
    obtain ⟨_, p, d, hp, hd, _, _, ⟨hall, hst⟩ | ⟨_, rfl⟩⟩ := signBody_ok hb
    · obtain ⟨_, hprob, _, _, hs1⟩ := startDeal_ok hst
      have hdeals := hs' seat i rfl
      have hin : ∃ a ∈ s'.deals, a.id = s.dealsStarted ∧ a.deal = d := by
        rw [hdeals, hs1]
        exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl, rfl⟩
      obtain ⟨hsig, hdep, _, _⟩ := dealProblems_nil hprob
      subst hs1
      refine ⟨_, rfl, ?_⟩
      intro x hx
      have hx' := hx
      simp only [depositEntries, List.mem_map] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      have hfund : FundsDeal s s' (.sign seat i)
          { src := .player y.1, dst := .deposit s.dealsStarted y.1, res := y.2.1,
            amount := y.2.2, reason := .setDeposit } s.dealsStarted y.1 :=
        ⟨rfl, rfl, rfl, seat, i, p, d, rfl, hp, hd, rfl, hin, hdep y hy,
          (all_contains_iff _ _ _).mp hall, by simpa using hy⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro k j h
        injection h with hk hj
        subst hk hj
        exact hfund
      · intro k j h
        cases h
      · intro h
        cases h
      · intro h
        cases h
      · intro j h
        injection h with hj
        subst hj
        exact Or.inr (Or.inr (Or.inl ⟨_, hfund⟩))
    · exact ⟨[], by simp, by simp⟩
  | exit seat i =>
    obtain ⟨_, _, rfl⟩ := exitBody_ok hb
    exact ⟨[], by simp, by simp⟩

/-- `finish` can end the game only after a move or a vote. -/
theorem finish_cases' {s s' : State G} {e : Event} (h : finish s e = .ok s') :
    s' = s ∨ ((∀ seat id, e ≠ .sign seat id) ∧ (∀ seat id, e ≠ .exit seat id) ∧
      ∃ w, endGame s w = .ok s') := by
  cases e with
  | move p m =>
    exact (checkWin_ok h).elim (fun x => Or.inl x.1)
      (fun x => Or.inr ⟨by simp, by simp, x⟩)
  | vote a b c =>
    exact (checkWin_ok h).elim (fun x => Or.inl x.1)
      (fun x => Or.inr ⟨by simp, by simp, x⟩)
  | propose a b => exact Or.inl (by simpa [finish] using h.symm)
  | sign a b => exact Or.inl (by simpa [finish] using h.symm)
  | exit a b => exact Or.inl (by simpa [finish] using h.symm)
  | forceEndTurn => exact Or.inl (by simpa [finish] using h.symm)

/-- Every entry of an accepted event is allowed. This is commandment V. -/
theorem step_vconj {s s' : State G} {e : Event} (hi : IdInv s) (h : Engine.step G s e = .ok s')
    {x : Entry} (hx : x ∈ newEntries s s') : VConj s s' e x := by
  rcases step_view h with ⟨hend, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨b, _, hs'⟩ := endTurnNow_ok h
    have hne : newEntries s s' = turnEntries s (rollAt G s.seed s.rollsMade) :=
      newEntries_of (by rw [hs']; simp)
    rw [hne] at hx
    subst hs'
    exact vconj_turn hend hi.deal_nodup hx
  · rcases finish_cases' hf with rfl | ⟨hns, hne, w, he⟩
    · obtain ⟨es, hj, hes⟩ := body_vconj hb (s' := countAction s1 (seatOf e)) (fun _ _ _ => rfl)
      have : newEntries s (countAction s1 (seatOf e)) = es := newEntries_of hj
      rw [this] at hx
      exact hes x hx
    · obtain ⟨es, hj, hes⟩ := body_vconj hb (s' := s') (fun a b hc => absurd hc (hns a b))
      have hd : s1.deals = s.deals := by
        rcases body_deals_cases hb with ⟨hd, _⟩ | ⟨a, b, hc, _⟩ | ⟨a, b, _, hc, _⟩
        · exact hd
        · exact absurd hc (hne a b)
        · exact absurd hc (hns a b)
      obtain ⟨bk, _, hs2⟩ := endGame_ok he
      have hnew : x ∈ es ++ (countAction s1 (seatOf e)).deals.flatMap
          (countAction s1 (seatOf e)).refundEntries := by
        have : newEntries s s' = es ++ (countAction s1 (seatOf e)).deals.flatMap
            (countAction s1 (seatOf e)).refundEntries :=
          newEntries_of (by rw [hs2]; simp [countAction, hj])
        rwa [this] at hx
      have hsd : s'.deals = [] := by rw [hs2]
      cases List.mem_append.mp hnew with
      | inl h1 => exact hes x h1
      | inr h1 =>
        obtain ⟨d, hdm, h2⟩ := List.mem_flatMap.mp h1
        obtain ⟨hr, j, _, h3, h4⟩ := refundEntries_form h2
        exact vconj_refund (by rw [← hd]; exact hdm) (fun _ hm => by rw [hsd] at hm; cases hm) hr h3 h4

end Charter.Proofs
