import Charter.Proofs.Deals

/-!
# Laws and deals cannot be switched off

A bundle posts exactly when its owner can pay it, because it names each resource once. From this, a
proposal is accepted exactly when its checks pass, and a deal starts when everyone can pay.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## Bundles -/

/-- A checked bundle names each resource once. -/
theorem bundleOk_nodup {b : Bundle} (h : G.bundleOk b = true) : (b.map (·.1)).Nodup := by
  simp only [GameDef.bundleOk, Bool.and_eq_true, beq_iff_eq] at h
  exact nodup_of_eraseDups _ (by simpa using h.2)

theorem bundle_outflow_le {src dst : Account} {bd : Bundle} {rs : Reason} {b : Books}
    (hnd : (bd.map (·.1)).Nodup) (haff : ∀ x ∈ bd, x.2 ≤ b src x.1) (a : Account) (r : Res) :
    outflow (bundleEntries src dst bd rs) a r ≤ b a r := by
  induction bd with
  | nil => exact Nat.zero_le _
  | cons x t ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    have hrest := ih hnd.2 (fun y hy => haff y (by simp [hy]))
    have hstep : outflow (bundleEntries src dst (x :: t) rs) a r =
        (if src = a ∧ x.1 = r then x.2 else 0) + outflow (bundleEntries src dst t rs) a r := by
      simp only [bundleEntries, List.map_cons, outflow_cons]
    rw [hstep]
    by_cases hc : src = a ∧ x.1 = r
    · have hz : outflow (bundleEntries src dst t rs) a r = 0 := by
        apply outflow_eq_zero'
        intro y hy _ h2
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hnd.1 z hz (by rw [hc.2]; exact h2)
      rw [hz, ite_eq_left hc, Nat.add_zero, ← hc.1, ← hc.2]
      exact haff x (by simp)
    · rw [ite_eq_right hc, Nat.zero_add]
      exact hrest

/-- If the owner can pay every line of a bundle, the bundle posts. -/
theorem bundle_posts {src dst : Account} {bd : Bundle} {rs : Reason} {b : Books}
    (hnd : (bd.map (·.1)).Nodup) (haff : ∀ x ∈ bd, x.2 ≤ b src x.1) (hne : src ≠ dst) :
    ∃ b', b.postAll (bundleEntries src dst bd rs) = some b' := by
  apply postAll_some
  · intro x hx
    obtain ⟨h1, h2, _⟩ := mem_bundleEntries hx
    rw [h1, h2]
    exact hne
  · exact bundle_outflow_le hnd haff

/-- If a bundle posted, its owner could pay every line of it. -/
theorem bundle_affords {src dst : Account} {bd : Bundle} {rs : Reason} {b b' : Books}
    (h : b.postAll (bundleEntries src dst bd rs) = some b') (hne : src ≠ dst) :
    ∀ x ∈ bd, x.2 ≤ b src x.1 := by
  intro x hx
  have hbal := postAll_balance h src x.1
  have hin : inflow (bundleEntries src dst bd rs) src x.1 = 0 := by
    apply inflow_eq_zero'
    intro y hy h1 _
    exact hne ((mem_bundleEntries hy).2.1.symm.trans h1).symm
  have hmem : ({ src := src, dst := dst, res := x.1, amount := x.2, reason := rs } : Entry) ∈
      bundleEntries src dst bd rs := List.mem_map.mpr ⟨x, hx, rfl⟩
  have := amount_le_outflow hmem
  change x.2 ≤ outflow _ src x.1 at this
  omega

theorem affords_iff (s : State G) (p : Seat) (bd : Bundle) :
    s.affords p bd = true ↔ ∀ x ∈ bd, x.2 ≤ s.books (.player p) x.1 := by
  simp only [State.affords, State.balance, List.all_eq_true]
  exact ⟨fun h x hx => of_decide_eq_true (h x hx), fun h x hx => decide_eq_true (h x hx)⟩

theorem canAct_of {s : State G} {seat : Seat} (h1 : seat ∈ s.turnOrder)
    (h2 : s.actionsThisTurn seat < maxActionsPerTurn) : canAct s seat = true := by
  simp [canAct, h1, h2]

/-! ## Proposals -/

/-- The step of a proposal, for a seat that can act. -/
theorem step_propose {s : State G} {seat : Seat} {body : Proposal} (hPhase : s.phase = .actions)
    (hc : canAct s seat = true) {s1 : State G} (hb : proposeBody s seat body = .ok s1) :
    Engine.step G s (.propose seat body) = .ok (countAction s1 seat) := by
  unfold Engine.step
  rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
  simp only [act, hc, ↓reduceIte, hb]

theorem step_propose_body {s s' : State G} {seat : Seat} {body : Proposal}
    (h : Engine.step G s (.propose seat body) = .ok s') :
    ∃ s1, proposeBody s seat body = .ok s1 ∧ s' = countAction s1 seat := by
  obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  exact ⟨s1, hb, (Except.ok.inj hf).symm⟩

theorem proposeBody_law {s : State G} {seat : Seat} {L : Law}
    (hPhase : s.phase = .actions)
    (hOpen : (s.openProposals.filter (·.by_ == seat)).length < maxOpenPerSeat)
    (hp : lawProblems G s L = []) :
    proposeBody s seat (.law L) = .ok (addProposal s seat (.law L)) := by
  have hn : ¬ maxOpenPerSeat ≤ (s.openProposals.filter (·.by_ == seat)).length := by omega
  have h1 : (s.phase != .actions) = false := by simp [hPhase]
  unfold proposeBody proposeLaw
  simp only [h1, hp, hn, List.isEmpty_nil, ↓reduceIte, Bool.not_true, Bool.false_eq_true]

theorem proposeBody_deal {s : State G} {seat : Seat} {d : Deal} (hPhase : s.phase = .actions)
    (hOpen : (s.openProposals.filter (·.by_ == seat)).length < maxOpenPerSeat)
    (hp : dealProblems s d = []) (hs : seat ∈ d.signers) :
    proposeBody s seat (.deal d) = .ok (addProposal s seat (.deal d)) := by
  have hn : ¬ maxOpenPerSeat ≤ (s.openProposals.filter (·.by_ == seat)).length := by omega
  have hc : d.signers.contains seat = true := by simpa using hs
  have h1 : (s.phase != .actions) = false := by simp [hPhase]
  unfold proposeBody proposeDeal
  simp only [h1, hp, hn, hc, List.isEmpty_nil, ↓reduceIte, Bool.not_true, Bool.false_eq_true]

theorem proposals_are_accepted (s : State G) (seat : Seat)
    (hPhase : s.phase = .actions) (hSeat : seat ∈ s.turnOrder)
    (hActs : s.actionsThisTurn seat < maxActionsPerTurn)
    (hOpen : (s.openProposals.filter (·.by_ == seat)).length < maxOpenPerSeat) :
    (∀ L, (∃ s', Engine.step G s (.propose seat (.law L)) = .ok s') ↔
      lawProblems G s L = []) ∧
    (∀ d, (∃ s', Engine.step G s (.propose seat (.deal d)) = .ok s') ↔
      dealProblems s d = [] ∧ seat ∈ d.signers) ∧
    (∀ body s', Engine.step G s (.propose seat body) = .ok s' →
      s'.openProposals = s.openProposals ++
        [{ id := s.nextProposalId, by_ := seat, body := body, votes := [], signed := [] }]) := by
  have hc := canAct_of hSeat hActs
  refine ⟨?_, ?_, ?_⟩
  · intro L
    constructor
    · rintro ⟨s', h⟩
      obtain ⟨s1, hb, _⟩ := step_propose_body h
      obtain ⟨_, _, hcase⟩ := proposeBody_ok hb
      rcases hcase with ⟨L', hL, hp, _⟩ | ⟨_, hd, _⟩
      · injection hL with hL
        subst hL
        exact hp
      · cases hd
    · intro hp
      exact ⟨_, step_propose hPhase hc (proposeBody_law hPhase hOpen hp)⟩
  · intro d
    constructor
    · rintro ⟨s', h⟩
      obtain ⟨s1, hb, _⟩ := step_propose_body h
      obtain ⟨_, _, hcase⟩ := proposeBody_ok hb
      rcases hcase with ⟨_, hd, _⟩ | ⟨d', hd, hs, hp, _⟩
      · cases hd
      · injection hd with hd
        subst hd
        exact ⟨hp, by simpa using hs⟩
    · rintro ⟨hp, hs⟩
      exact ⟨_, step_propose hPhase hc (proposeBody_deal hPhase hOpen hp hs)⟩
  · intro body s' h
    obtain ⟨s1, hb, rfl⟩ := step_propose_body h
    obtain ⟨_, _, hcase⟩ := proposeBody_ok hb
    rcases hcase with ⟨_, rfl, _, _, _, rfl⟩ | ⟨_, rfl, _, _, rfl⟩ <;> rfl

/-! ## Signatures -/

theorem step_sign {s : State G} {seat id : Nat} (hPhase : s.phase = .actions)
    (hc : canAct s seat = true) {s1 : State G} (hb : signBody s seat id = .ok s1) :
    Engine.step G s (.sign seat id) = .ok (countAction s1 seat) := by
  unfold Engine.step
  rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
  simp only [act, hc, ↓reduceIte, hb]

theorem depositEntries_player_outflow (id : Nat) (d : Deal) (i : Seat) (r : Res) :
    outflow (depositEntries id d) (.player i) r = d.depositOf i r := by
  unfold depositEntries Deal.depositOf
  generalize d.deposits = L
  induction L with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, outflow_cons, ih, List.filter_cons, Bool.and_eq_true, beq_iff_eq,
      Account.player.injEq]
    split <;> simp

/-- If every signer can pay, the deposits post. -/
theorem deposits_post (s : State G) (id : Nat) (d : Deal)
    (haff : ∀ i r, d.depositOf i r ≤ s.balance (.player i) r) :
    ∃ b, s.books.postAll (depositEntries id d) = some b := by
  apply postAll_some
  · intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    simp
  · intro a r
    cases a with
    | player i =>
      rw [depositEntries_player_outflow]
      exact haff i r
    | bank | treasury | deposit =>
      rw [outflow_eq_zero']
      · exact Nat.zero_le _
      · intro x hx h1 _
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        cases h1

theorem deals_can_start (s : State G) (seat id : Nat) (p : OpenProposal) (d : Deal)
    (hPhase : s.phase = .actions)
    (hSeat : seat ∈ s.turnOrder) (hActs : s.actionsThisTurn seat < maxActionsPerTurn)
    (hOpen : s.openProposal? id = some p) (hBody : p.body = .deal d)
    (hSigner : seat ∈ d.signers) (hNew : seat ∉ p.signed) :
    ((¬ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
      ∃ s' q, Engine.step G s (.sign seat id) = .ok s' ∧
        s'.deals = s.deals ∧ newEntries s s' = [] ∧
        s'.openProposal? id = some q ∧ q.body = p.body ∧ q.signed = p.signed ++ [seat]) ∧
    ((∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
      dealProblems s d = [] →
      (∀ i r, d.depositOf i r ≤ s.balance (.player i) r) →
      s.canStartDeal = true →
      ∃ s', Engine.step G s (.sign seat id) = .ok s' ∧
        s'.deals = s.deals ++
          [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
             startRound := s.round, builtBefore := s.builtThisRound.length }] ∧
        s'.dealsStarted = s.dealsStarted + 1 ∧
        newEntries s s' = depositEntries s.dealsStarted d ∧
        s'.openProposal? id = none) := by
  have hc := canAct_of hSeat hActs
  have hsg : d.signers.contains seat = true := by simpa using hSigner
  have hns : p.signed.contains seat = false := by simpa using hNew
  have hid : p.id = id := (openProposal_mem hOpen).2
  constructor
  · intro hnot
    have hall : d.signers.all (p.signed ++ [seat]).contains = false := by
      cases hx : d.signers.all (p.signed ++ [seat]).contains with
      | false => rfl
      | true => exact absurd ((all_contains_iff _ _ _).mp hx) hnot
    have hbody : signBody s seat id = .ok { s with openProposals := s.openProposals.map fun q =>
        if q.id == id then { q with signed := p.signed ++ [seat] } else q } := by
      have h1 : (s.phase != .actions) = false := by simp [hPhase]
      unfold signBody
      simp only [h1, hOpen, hBody, hsg, hns, hall]
      rfl
    refine ⟨_, { p with signed := p.signed ++ [seat] }, step_sign hPhase hc hbody, rfl,
      newEntries_nil rfl, ?_, rfl, rfl⟩
    change (s.openProposals.map _).find? _ = _
    rw [List.find?_map]
    have hpred : ((fun x : OpenProposal => x.id == id) ∘ fun q : OpenProposal =>
        if q.id == id then { q with signed := p.signed ++ [seat] } else q) =
        fun x : OpenProposal => x.id == id := by
      funext q
      simp only [Function.comp_def]
      split <;> rfl
    rw [hpred]
    change (s.openProposal? id).map _ = _
    rw [hOpen]
    simp [hid]
  · intro hyes hprob haff hstart
    have hall : d.signers.all (p.signed ++ [seat]).contains = true :=
      (all_contains_iff _ _ _).mpr hyes
    obtain ⟨b, hb⟩ := deposits_post s s.dealsStarted d haff
    have hst : startDeal s id d = .ok { s with
        books := b, journal := s.journal ++ depositEntries s.dealsStarted d
        deals := s.deals ++
          [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
             startRound := s.round, builtBefore := s.builtThisRound.length }]
        dealsStarted := s.dealsStarted + 1
        openProposals := s.openProposals.filter (·.id != id) } := by
      unfold startDeal
      simp only [hstart, hprob, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [record_some hb]
      rfl
    have hbody : signBody s seat id = startDeal s id d := by
      have h1 : (s.phase != .actions) = false := by simp [hPhase]
      unfold signBody
      simp only [h1, hOpen, hBody, hsg, hns, hall]
      rfl
    refine ⟨_, step_sign hPhase hc (hbody.trans hst), rfl, rfl, newEntries_of rfl, ?_⟩
    change (s.openProposals.filter (·.id != id)).find? _ = none
    rw [List.find?_eq_none]
    intro x hx
    have := (List.mem_filter.mp hx).2
    simpa using this

end Charter.Proofs
