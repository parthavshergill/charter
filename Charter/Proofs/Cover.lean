import Charter.Proofs.Posting

/-!
# Deposits cover what deals can still owe

`Cover` is commandment IV(a). From it, a round's payments always post, so every turn change posts in
full, so the timer can always end a turn.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## What one deal pays at a round's end -/

/-- What one term of a running deal pays at this round's end. -/
def termDue (s : State G) (d : ActiveDeal) : Term → List Entry
  | .everyRound ps => State.payEntries d.id ps
  | .onBuild x k ps => if (s.buildsSeenBy d).contains (x, k) then State.payEntries d.id ps else []
  | _ => []

/-- What one running deal pays at this round's end. -/
def dealDue (s : State G) (d : ActiveDeal) : List Entry := d.deal.terms.flatMap (termDue s d)

theorem duePayments_eq (s : State G) : s.duePayments = s.deals.flatMap (dealDue s) := by
  unfold State.duePayments dealDue
  congr 1

/-- The most a list of payments takes from signer `i` in `r`. -/
def owedBy (ps : List Pay) (i : Seat) (r : Res) : Nat :=
  ((ps.filter fun p => p.src == i && p.res == r).map (·.amount)).sum

theorem owedBy_append (xs ys : List Pay) (i : Seat) (r : Res) :
    owedBy (xs ++ ys) i r = owedBy xs i r + owedBy ys i r := by
  simp [owedBy, List.filter_append]

theorem payEntries_outflow (id : Nat) (ps : List Pay) (i : Seat) (r : Res) :
    outflow (State.payEntries id ps) (.deposit id i) r = owedBy ps i r := by
  induction ps with
  | nil => rfl
  | cons p t ih =>
    have h1 : outflow (State.payEntries id (p :: t)) (.deposit id i) r =
        (if (Account.deposit id p.src) = .deposit id i ∧ p.res = r then p.amount else 0) +
        outflow (State.payEntries id t) (.deposit id i) r := by
      simp only [State.payEntries, List.map_cons, outflow_cons]
    rw [h1, ih]
    simp only [owedBy, List.filter_cons, Bool.and_eq_true, beq_iff_eq, Account.deposit.injEq, true_and]
    split <;> simp

theorem termDue_outflow (s : State G) (d : ActiveDeal) (t : Term) (i : Seat) (r : Res) :
    outflow (termDue s d t) (.deposit d.id i) r ≤ owedBy t.pays i r := by
  cases t with
  | everyRound ps => exact Nat.le_of_eq (payEntries_outflow _ _ _ _)
  | onBuild x k ps =>
    simp only [termDue]
    split
    · exact Nat.le_of_eq (payEntries_outflow _ _ _ _)
    · exact Nat.zero_le _
  | noBuild _ _ _ => exact Nat.zero_le _
  | noTrade _ _ => exact Nat.zero_le _

theorem dealDue_outflow (s : State G) (d : ActiveDeal) (i : Seat) (r : Res) :
    outflow (dealDue s d) (.deposit d.id i) r ≤ d.deal.owedPerRound i r := by
  have key : ∀ ts : List Term, outflow (ts.flatMap (termDue s d)) (.deposit d.id i) r ≤
      owedBy (ts.flatMap Term.pays) i r := by
    intro ts
    induction ts with
    | nil => exact Nat.zero_le _
    | cons t ts ih =>
      rw [List.flatMap_cons, List.flatMap_cons, outflow_append, owedBy_append]
      exact Nat.add_le_add (termDue_outflow s d t i r) ih
  exact key _

theorem dealDue_src {s : State G} {d : ActiveDeal} {x : Entry} (hx : x ∈ dealDue s d) :
    ∃ i, x.src = .deposit d.id i := by
  simp only [dealDue, List.mem_flatMap] at hx
  obtain ⟨t, _, hx⟩ := hx
  have key : ∀ ps, x ∈ State.payEntries d.id ps → ∃ i, x.src = .deposit d.id i := by
    intro ps hx
    simp only [State.payEntries, List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact ⟨_, rfl⟩
  cases t with
  | everyRound ps => exact key ps hx
  | onBuild a k ps =>
    simp only [termDue] at hx
    split at hx
    · exact key ps hx
    · simp at hx
  | noBuild _ _ _ => simp [termDue] at hx
  | noTrade _ _ => simp [termDue] at hx

/-- All deals together take from one deposit only what that deal owes. -/
theorem due_outflow_le_owed {s : State G} (hnd : (s.deals.map (·.id)).Nodup) {d : ActiveDeal}
    (hd : d ∈ s.deals) (i : Seat) (r : Res) :
    outflow s.duePayments (.deposit d.id i) r ≤ d.deal.owedPerRound i r := by
  rw [duePayments_eq]
  apply outflow_flatMap_le _ _ (·.id) hnd
  · intro d' hd'
    by_cases he : d' = d
    · subst he
      exact dealDue_outflow s d' i r
    · have hz : outflow (dealDue s d') (.deposit d.id i) r = 0 := by
        apply outflow_eq_zero'
        intro x hx h1 _
        obtain ⟨j, hj⟩ := dealDue_src hx
        rw [hj] at h1
        injection h1 with h2 _
        exact he (eq_of_id_eq (·.id) hnd hd' hd h2)
      rw [hz]
      exact Nat.zero_le _
  · intro u _ v _ h1 h2
    obtain ⟨x, hx, h3, _⟩ := exists_of_outflow_ne h1
    obtain ⟨y, hy, h4, _⟩ := exists_of_outflow_ne h2
    obtain ⟨j, hj⟩ := dealDue_src hx
    obtain ⟨k, hk⟩ := dealDue_src hy
    rw [hj] at h3
    rw [hk] at h4
    injection h3.trans h4.symm

/-! ## The invariant -/

/-- Commandment IV(a). -/
def Cover (s : State G) : Prop :=
  ∀ d ∈ s.deals, ∀ i r, s.worstCase d i r ≤ s.balance (.deposit d.id i) r

theorem Cover.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    Cover (initialState G seats serverSeed nonces) := by
  intro d hd
  cases hd

/-- A running deal owes at most its worst case in one round. -/
theorem owed_le_worstCase {s : State G} {d : ActiveDeal} (hr : s.round ≤ d.lastRound) (i : Seat)
    (r : Res) : d.deal.owedPerRound i r ≤ s.worstCase d i r := by
  unfold State.worstCase State.roundsLeft
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- A round's payments never overdraw a deposit. -/
theorem due_outflow {s : State G} (hc : Cover s) (hi : IdInv s) (a : Account) (r : Res) :
    outflow s.duePayments a r ≤ s.books a r := by
  rw [duePayments_eq]
  apply outflow_flatMap_le _ _ (·.id) hi.deal_nodup
  · intro d hd
    by_cases hz : outflow (dealDue s d) a r = 0
    · rw [hz]
      exact Nat.zero_le _
    · obtain ⟨x, hx, h3, _⟩ := exists_of_outflow_ne hz
      obtain ⟨j, hj⟩ := dealDue_src hx
      subst h3
      rw [hj]
      exact Nat.le_trans (dealDue_outflow s d j r)
        (Nat.le_trans (owed_le_worstCase (hi.deal_round d hd) j r) (hc d hd j r))
  · intro u _ v _ h1 h2
    obtain ⟨x, hx, h3, _⟩ := exists_of_outflow_ne h1
    obtain ⟨y, hy, h4, _⟩ := exists_of_outflow_ne h2
    obtain ⟨j, hj⟩ := dealDue_src hx
    obtain ⟨k, hk⟩ := dealDue_src hy
    rw [hj] at h3
    rw [hk] at h4
    injection h3.trans h4.symm

theorem due_ne {s : State G} {x : Entry} (hx : x ∈ s.duePayments) : x.src ≠ x.dst := by
  obtain ⟨_, d, _, p, _, h1, _, _, h4⟩ := duePayments_form hx
  intro he
  rw [h1, h4] at he
  exact payee_notDeposit _ _ _ he.symm

theorem due_posts {s : State G} (hc : Cover s) (hi : IdInv s) :
    ∃ b, s.books.postAll s.duePayments = some b :=
  postAll_some (fun _ hx => due_ne hx) (due_outflow hc hi)

theorem closing_nodup {s : State G} (hnd : (s.deals.map (·.id)).Nodup) :
    (s.closingDeals.map (·.id)).Nodup := by
  unfold State.closingDeals
  split
  · exact hnd
  · exact (List.filter_sublist.map _).nodup hnd

/-! ## Every turn change posts -/

theorem roundEnd_posts (hG : G.Valid) {s : State G} (hc : Cover s) (hi : IdInv s) :
    ∃ b, s.books.postAll s.roundEndEntries = some b := by
  obtain ⟨b1, h1⟩ := due_posts hc hi
  obtain ⟨b2, h2⟩ := settle_posts (s.afterPosting s.duePayments)
    ((s.afterPosting s.duePayments).laws.flatMap fun x =>
      Law.plan (s.afterPosting s.duePayments) .roundEnd x.2)
  rw [afterPosting_books h1] at h2
  have hpaid : s.books.postAll (s.duePayments ++ s.roundEndLawEntries) = some b2 := by
    rw [postAll_append, h1, Option.bind_some]
    exact h2
  obtain ⟨b3, h3⟩ := refunds_post hG (s.afterPosting (s.duePayments ++ s.roundEndLawEntries))
    s.closingDeals (closing_nodup hi.deal_nodup)
    (fun d hd => hi.signers_nodup d (closingDeals_mem hd))
  rw [afterPosting_books hpaid] at h3
  refine ⟨b3, ?_⟩
  simp only [State.roundEndEntries]
  rw [postAll_append, hpaid, Option.bind_some]
  exact h3

theorem beforeRoll_posts (hG : G.Valid) {s : State G} (hc : Cover s) (hi : IdInv s) :
    ∃ b, s.books.postAll s.entriesBeforeRoll = some b := by
  unfold State.entriesBeforeRoll
  split
  · exact roundEnd_posts hG hc hi
  · exact ⟨_, rfl⟩

theorem turnEntries_posts (hG : G.Valid) {s : State G} (hc : Cover s) (hi : IdInv s) (roll : Nat) :
    ∃ b, s.books.postAll (turnEntries s roll) = some b := by
  obtain ⟨b1, h1⟩ := beforeRoll_posts hG hc hi
  simp only [turnEntries]
  split
  · obtain ⟨b2, h2⟩ := rollEntries_posts s.afterRoundEnd roll
    have hbk : s.afterRoundEnd.books = b1 := afterPosting_books h1
    rw [hbk] at h2
    rw [postAll_append, h1, Option.bind_some]
    exact ⟨b2, h2⟩
  · exact ⟨b1, h1⟩

theorem record_some {s : State G} {es : List Entry} {b : Books} (h : s.books.postAll es = some b) :
    record s es = .ok { s with books := b, journal := s.journal ++ es } := by
  unfold record
  rw [h]

/-- The timer can always end a turn. -/
theorem endTurnNow_some (hG : G.Valid) {s : State G} (hc : Cover s) (hi : IdInv s) :
    ∃ s', endTurnNow s = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1 := by
  obtain ⟨b, hb⟩ := turnEntries_posts hG hc hi (rollAt G s.seed s.rollsMade)
  refine ⟨startNextTurn { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade), pieces := s.turnPieces (rollAt G s.seed s.rollsMade) }
    (rollAt G s.seed s.rollsMade), ?_, startNextTurn_turnsTaken _ _⟩
  unfold endTurnNow
  simp only
  rw [record_some hb]

/-- Commandment IX(a). -/
theorem cannot_stall (hG : G.Valid) {s : State G} (hc : Cover s) (hi : IdInv s)
    (he : s.phase ≠ .ended) :
    (∃ s', Engine.step G s .forceEndTurn = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1) ∧
    ∀ p, s.currentSeat = some p →
      ∃ s', Engine.step G s (.move p .endTurn) = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1 := by
  obtain ⟨s', h1, h2⟩ := endTurnNow_some hG hc hi
  refine ⟨⟨s', ?_, h2⟩, fun p hp => ⟨s', ?_, h2⟩⟩
  · unfold Engine.step
    rw [ite_eq_right_of_eq_false _ _ (by simpa using he)]
    exact h1
  · unfold Engine.step
    rw [ite_eq_right_of_eq_false _ _ (by simpa using he)]
    simp only [State.isTurnOf, hp, beq_self_eq_true, ↓reduceIte]
    exact h1

/-! ## Commandment IV(b): the shape of a round's end -/

/-- At a round's end, the entries start with the deals' payments. -/
theorem turnEntries_last {s : State G} (hl : s.isLastTurn = true) (roll : Nat) :
    ∃ H, turnEntries s roll = s.duePayments ++ (s.roundEndLawEntries ++
        (s.closingDeals.flatMap (s.afterPosting (s.duePayments ++ s.roundEndLawEntries)).refundEntries
          ++ H)) ∧
      ∀ x ∈ H, x ∈ rollEntries s.afterRoundEnd roll := by
  have hb : s.entriesBeforeRoll = s.roundEndEntries := by
    simp [State.entriesBeforeRoll, hl]
  simp only [turnEntries]
  split
  · refine ⟨_, ?_, fun x hx => hx⟩
    rw [hb]
    simp [State.roundEndEntries, List.append_assoc]
  · refine ⟨[], ?_, by simp⟩
    rw [hb]
    simp [State.roundEndEntries, List.append_assoc]

theorem step_endsTurn {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') :
    ∃ b, s.books.postAll (turnEntries s (rollAt G s.seed s.rollsMade)) = some b ∧
      s' = startNextTurn
        { s with
          books := b
          journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade)
          pieces := s.turnPieces (rollAt G s.seed s.rollsMade) }
        (rollAt G s.seed s.rollsMade) := by
  rcases step_view h with ⟨_, h⟩ | ⟨hn, _⟩
  · exact endTurnNow_ok h
  · exact absurd hend hn

theorem newEntries_endTurn {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') :
    newEntries s s' = turnEntries s (rollAt G s.seed s.rollsMade) := by
  obtain ⟨b, _, hs⟩ := step_endsTurn hend h
  exact newEntries_of (by rw [hs]; simp)

/-- Commandment IV(b). -/
theorem payments_exact {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') (hl : s.isLastTurn = true) :
    (newEntries s s').filter (·.reason == .dealPayment) = s.duePayments := by
  rw [newEntries_endTurn hend h]
  obtain ⟨H, hT, hH⟩ := turnEntries_last hl (rollAt G s.seed s.rollsMade)
  rw [hT, List.filter_append]
  have h1 : s.duePayments.filter (·.reason == .dealPayment) = s.duePayments := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [(duePayments_form hx).1]
  have h2 : ∀ x ∈ s.roundEndLawEntries ++
      (s.closingDeals.flatMap (s.afterPosting (s.duePayments ++ s.roundEndLawEntries)).refundEntries
        ++ H), x.reason ≠ .dealPayment := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx | hx
    · rw [(lawEntries_form _ _ x hx).1]
      simp
    · obtain ⟨d, _, hx⟩ := List.mem_flatMap.mp hx
      rw [(refundEntries_form hx).1]
      simp
    · exact (rollEntries_form (hH x hx)).2.2.1
  rw [h1, List.filter_eq_nil_iff.mpr]
  · simp
  · intro x hx
    simpa using h2 x hx

end Charter.Proofs
