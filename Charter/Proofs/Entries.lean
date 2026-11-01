import Charter.Proofs.Books

/-!
# Every entry the engine writes uses real accounts

A law, a harvest, a deal payment or a refund can only name accounts of the game. This needs three
facts about the state: pieces are owned by seats in the game, and each running deal has a good id
and pays between seats in the game.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## Laws -/

/-- The seats a law is reacting to are in the game. -/
def EnvOk (T : List Seat) (env : LawEnv) : Prop :=
  (∀ a, env.actor = some a → a ∈ T) ∧ (∀ a, env.each = some a → a ∈ T)

theorem party_account_ok {T : List Seat} {env : LawEnv} (h : EnvOk T env) {p : Party} {a : Account}
    (hp : p.account env = some a) : AcctOk T a := by
  cases p <;> simp only [Party.account, Option.map_eq_some_iff, Option.some.injEq] at hp
  · obtain ⟨i, hi, rfl⟩ := hp; exact h.1 i hi
  · obtain ⟨i, hi, rfl⟩ := hp; exact h.2 i hi
  · subst hp; trivial
  · subst hp; trivial

mutual
  theorem plan_ok (s : State G) : ∀ (e : Effect) (env : LawEnv), EnvOk s.turnOrder env →
      ∀ x ∈ Effect.plan s e env, EntryOk s.turnOrder x
    | .transfer src dst r amount, env, h, x, hx => by
      simp only [Effect.plan] at hx
      split at hx
      · rename_i a b c ha hb _
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨party_account_ok h ha, party_account_ok h hb⟩
      · simp at hx
    | .forEach c body, env, h, x, hx => by
      simp only [Effect.plan, List.mem_flatMap] at hx
      obtain ⟨p, hp, hx⟩ := hx
      split at hx
      · refine planAll_ok s body { env with each := some p } ⟨h.1, ?_⟩ x hx
        intro a ha
        simp only [Option.some.injEq] at ha
        exact ha ▸ hp
      · simp at hx
    | .when c body, env, h, x, hx => by
      simp only [Effect.plan] at hx
      split at hx
      · exact planAll_ok s body _ h x hx
      · simp at hx

  theorem planAll_ok (s : State G) : ∀ (es : List Effect) (env : LawEnv), EnvOk s.turnOrder env →
      ∀ x ∈ Effect.planAll s es env, EntryOk s.turnOrder x
    | [], _, _, x, hx => by simp [Effect.planAll] at hx
    | e :: es, env, h, x, hx => by
      simp only [Effect.planAll, List.mem_append] at hx
      cases hx with
      | inl hx => exact plan_ok s e env h x hx
      | inr hx => exact planAll_ok s es env h x hx
end

/-- A trigger names only seats in the game. -/
def TriggerOk (T : List Seat) : Trigger → Prop
  | .harvest a _ _ => a ∈ T
  | .build a _ => a ∈ T
  | .roundEnd => True

theorem trigger_env_ok {T : List Seat} {t : Trigger} (h : TriggerOk T t) : EnvOk T t.env := by
  cases t <;> simp_all [EnvOk, Trigger.env, TriggerOk]

theorem lawPlan_ok (s : State G) {t : Trigger} (ht : TriggerOk s.turnOrder t) (L : Law) :
    ∀ x ∈ Law.plan s t L, EntryOk s.turnOrder x := by
  intro x hx
  simp only [Law.plan, List.mem_flatMap] at hx
  obtain ⟨c, _, hx⟩ := hx
  exact planAll_ok s _ _ (trigger_env_ok ht) x hx

/-- `settle` only shrinks or drops entries. It keeps who, what and why. -/
theorem mem_settle {s : State G} {es : List Entry} {x : Entry} (hx : x ∈ settle s es) :
    ∃ e ∈ es, x.src = e.src ∧ x.dst = e.dst ∧ x.res = e.res ∧ x.reason = e.reason := by
  simp only [settle, List.mem_filter, List.mem_map] at hx
  obtain ⟨⟨e, ⟨he, _⟩, rfl⟩, _⟩ := hx
  exact ⟨e, he, rfl, rfl, rfl, rfl⟩

theorem lawEntries_ok (s : State G) {t : Trigger} (ht : TriggerOk s.turnOrder t) :
    ∀ x ∈ lawEntries s t, EntryOk s.turnOrder x := by
  intro x hx
  obtain ⟨e, he, h1, h2, _⟩ := mem_settle hx
  simp only [List.mem_flatMap] at he
  obtain ⟨L, _, he⟩ := he
  have := lawPlan_ok s ht L.2 e he
  exact ⟨h1 ▸ this.1, h2 ▸ this.2⟩

/-! ## Harvests -/

@[simp] theorem afterPosting_turnOrder (s : State G) (es : List Entry) :
    (s.afterPosting es).turnOrder = s.turnOrder := rfl
@[simp] theorem afterPosting_pieces (s : State G) (es : List Entry) :
    (s.afterPosting es).pieces = s.pieces := rfl
@[simp] theorem afterPosting_laws (s : State G) (es : List Entry) :
    (s.afterPosting es).laws = s.laws := rfl
@[simp] theorem afterPosting_deals (s : State G) (es : List Entry) :
    (s.afterPosting es).deals = s.deals := rfl

/-- Every piece belongs to a seat in the game. -/
def PiecesOk (s : State G) : Prop := ∀ x ∈ s.pieces, x.owner ∈ s.turnOrder

theorem baseHarvest_shape {s : State G} (hp : PiecesOk s) {roll : Nat} {x : Entry}
    (hx : x ∈ baseHarvest s roll) : x.src = .bank ∧ ∃ o ∈ s.turnOrder, x.dst = .player o := by
  obtain ⟨e, he, h1, h2, _⟩ := mem_settle hx
  simp only [List.mem_flatMap, List.mem_filterMap] at he
  obtain ⟨_, _, q, hq, hm⟩ := he
  split at hm
  · split at hm
    · simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨h1, q.owner, hp q hq, h2⟩
    · cases hm
  · cases hm

theorem harvestEntries_ok {s : State G} (hp : PiecesOk s) (roll : Nat) :
    ∀ x ∈ harvestEntries s roll, EntryOk s.turnOrder x := by
  intro x hx
  simp only [harvestEntries, List.mem_append] at hx
  cases hx with
  | inl hx =>
    obtain ⟨h1, o, ho, h2⟩ := baseHarvest_shape hp hx
    exact ⟨by rw [h1]; trivial, by rw [h2]; exact ho⟩
  | inr hx =>
    obtain ⟨e, he, h1, h2, _⟩ := mem_settle hx
    simp only [List.mem_flatMap] at he
    obtain ⟨b, hb, he⟩ := he
    obtain ⟨_, o, ho, hd⟩ := baseHarvest_shape hp hb
    rw [hd] at he
    simp only [List.mem_flatMap] at he
    obtain ⟨L, _, he⟩ := he
    have := lawPlan_ok (s.afterPosting (baseHarvest s roll))
      (t := .harvest o b.res b.amount) ho L.2 e he
    exact ⟨h1 ▸ this.1, h2 ▸ this.2⟩

/-! ## Deals -/

/-- A running deal has an id below the limit, and its signers and payments use seats in the game. -/
structure DealOk (T : List Seat) (d : ActiveDeal) : Prop where
  id_lt : d.id < maxDealsPerGame
  signers : ∀ i ∈ d.deal.signers, i ∈ T
  pays_src : ∀ p ∈ d.deal.allPays, p.src ∈ T
  pays_dst : ∀ p ∈ d.deal.allPays, AcctOk T p.dst.account

/-- Every running deal is good. -/
def DealsOk (s : State G) : Prop := ∀ d ∈ s.deals, DealOk s.turnOrder d

/-- A deal with no problems uses only seats in the game. -/
theorem dealProblems_nil {s : State G} {d : Deal} (h : dealProblems s d = []) :
    (∀ i ∈ d.signers, i ∈ s.turnOrder) ∧
    (∀ x ∈ d.deposits, x.1 ∈ d.signers) ∧
    (∀ p ∈ d.allPays, p.src ∈ s.turnOrder) ∧
    (∀ p ∈ d.allPays, AcctOk s.turnOrder p.dst.account) := by
  simp only [dealProblems, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  have hsig : ∀ i ∈ d.signers, i ∈ s.turnOrder := by
    simpa using h3
  have hpays : ∀ p ∈ d.allPays, d.signers.contains p.src = true ∧
      (match p.dst with
       | .seat x => s.turnOrder.contains x = true
       | .treasury => True) := by
    intro p hp
    have := h7 p hp
    simp only [payProblems, List.append_eq_nil_iff] at this
    obtain ⟨⟨a, _⟩, c⟩ := this
    refine ⟨by simpa using a, ?_⟩
    cases hd : p.dst with
    | seat x =>
      rw [hd] at c
      simpa using c
    | treasury => trivial
  refine ⟨hsig, ?_, ?_, ?_⟩
  · simpa using h5
  · intro p hp
    exact hsig _ (by simpa using (hpays p hp).1)
  · intro p hp
    have := (hpays p hp).2
    cases hd : p.dst with
    | seat x =>
      rw [hd] at this
      simpa [Payee.account, AcctOk] using this
    | treasury => simp [Payee.account, AcctOk]

theorem payEntries_ok {T : List Seat} {d : ActiveDeal} (hd : DealOk T d) {ps : List Pay}
    (hps : ∀ p ∈ ps, p ∈ d.deal.allPays) :
    ∀ x ∈ State.payEntries d.id ps, EntryOk T x := by
  intro x hx
  simp only [State.payEntries, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨⟨hd.id_lt, hd.pays_src p (hps p hp)⟩, hd.pays_dst p (hps p hp)⟩

theorem duePayments_ok {s : State G} (hd : DealsOk s) :
    ∀ x ∈ s.duePayments, EntryOk s.turnOrder x := by
  intro x hx
  simp only [State.duePayments, List.mem_flatMap] at hx
  obtain ⟨d, hd', t, ht, hx⟩ := hx
  have hsub : ∀ p ∈ t.pays, p ∈ d.deal.allPays := by
    intro p hp
    simp only [Deal.allPays, List.mem_flatMap]
    exact ⟨t, ht, hp⟩
  cases t with
  | everyRound ps => exact payEntries_ok (hd d hd') hsub x hx
  | onBuild a k ps =>
    simp only at hx
    split at hx
    · exact payEntries_ok (hd d hd') hsub x hx
    · simp at hx
  | noBuild _ _ _ => simp at hx
  | noTrade _ _ => simp at hx

theorem refundEntries_ok {s : State G} {d : ActiveDeal} (hd : DealOk s.turnOrder d) :
    ∀ x ∈ s.refundEntries d, EntryOk s.turnOrder x := by
  intro x hx
  simp only [State.refundEntries, List.mem_flatMap, List.mem_filterMap] at hx
  obtain ⟨i, hi, r, _, hm⟩ := hx
  split at hm
  · cases hm
  · simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨⟨hd.id_lt, hd.signers i hi⟩, hd.signers i hi⟩

theorem allRefunds_ok {s : State G} (hd : DealsOk s) :
    ∀ x ∈ s.deals.flatMap s.refundEntries, EntryOk s.turnOrder x := by
  intro x hx
  simp only [List.mem_flatMap] at hx
  obtain ⟨d, h, hx⟩ := hx
  exact refundEntries_ok (hd d h) x hx

theorem depositEntries_ok {T : List Seat} {id : Nat} (hid : id < maxDealsPerGame) {d : Deal}
    (hs : ∀ i ∈ d.signers, i ∈ T) (hdep : ∀ x ∈ d.deposits, x.1 ∈ d.signers) :
    ∀ x ∈ depositEntries id d, EntryOk T x := by
  intro x hx
  simp only [depositEntries, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨hs _ (hdep y hy), hid, hs _ (hdep y hy)⟩

/-! ## The turn change -/

theorem roundEndEntries_ok {s : State G} (hd : DealsOk s) :
    ∀ x ∈ s.roundEndEntries, EntryOk s.turnOrder x := by
  intro x hx
  simp only [State.roundEndEntries, State.roundEndLawEntries, List.mem_append,
    List.mem_flatMap] at hx
  rcases hx with (hx | hx) | ⟨d, hdm, hx⟩
  · exact duePayments_ok hd x hx
  · exact lawEntries_ok (s.afterPosting s.duePayments) (t := .roundEnd) trivial x hx
  · have hm : d ∈ s.deals := by
      unfold State.closingDeals at hdm
      split at hdm
      · exact hdm
      · exact (List.mem_filter.mp hdm).1
    exact refundEntries_ok (s := s.afterPosting _) (hd d hm) x hx

theorem entriesBeforeRoll_ok {s : State G} (hd : DealsOk s) :
    ∀ x ∈ s.entriesBeforeRoll, EntryOk s.turnOrder x := by
  intro x hx
  unfold State.entriesBeforeRoll at hx
  split at hx
  · exact roundEndEntries_ok hd x hx
  · simp at hx

theorem turnEntries_ok {s : State G} (hp : PiecesOk s) (hd : DealsOk s) (roll : Nat) :
    ∀ x ∈ turnEntries s roll, EntryOk s.turnOrder x := by
  intro x hx
  simp only [turnEntries] at hx
  split at hx
  · simp only [List.mem_append] at hx
    cases hx with
    | inl hx => exact entriesBeforeRoll_ok hd x hx
    | inr hx => exact harvestEntries_ok (s := s.afterPosting _) hp roll x hx
  · exact entriesBeforeRoll_ok hd x hx

end Charter.Proofs
