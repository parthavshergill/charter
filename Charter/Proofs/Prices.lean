import Charter.Proofs.Accepted
import Charter.Proofs.Limits

/-!
# Prices are real

Every price in the current rules names each resource once. The game's own prices are checked by
`GameDef.Valid`, and a law's prices are checked by `lawProblems`. So a seat that can pay a price can
pay it in full, and a build is accepted exactly when `canPlace` says so.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## Prices in the rules are checked -/

/-- The price this clause sets is a checked bundle. -/
def ClausePriceOk (G : GameDef) : Clause → Prop
  | .setCost _ b => G.bundleOk b = true
  | .newPiece p => G.bundleOk p.cost = true
  | _ => True

/-- Every price in these rules is a checked bundle. -/
def RulesPriceOk (G : GameDef) (R : Rules) : Prop := ∀ d ∈ R.pieces, G.bundleOk d.cost = true

theorem clause_price {R : Rules} {c : Clause} (hR : RulesPriceOk G R) (hc : ClausePriceOk G c) :
    RulesPriceOk G (c.applyTo R) := by
  cases c with
  | setCost k b =>
    intro d hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    split
    · exact hc
    · exact hR d0 hd0
  | setPoints k n =>
    intro d hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    split
    · exact hR d0 hd0
    · exact hR d0 hd0
  | newPiece p =>
    intro d hd
    cases List.mem_append.mp hd with
    | inl h => exact hR d h
    | inr h =>
      simp only [List.mem_singleton] at h
      subst h
      exact hc
  | onHarvest _ => exact hR
  | onBuild _ _ => exact hR
  | onRoundEnd _ => exact hR
  | onRoll _ => exact hR
  | setBankRate _ => exact hR
  | setWorth _ _ => exact hR
  | repeal _ => exact hR

theorem law_price {R : Rules} {L : Law} (hR : RulesPriceOk G R)
    (hL : ∀ c ∈ L.clauses, ClausePriceOk G c) : RulesPriceOk G (L.applyTo R) := by
  unfold Law.applyTo
  generalize L.clauses = cs at hL
  induction cs generalizing R with
  | nil => exact hR
  | cons c t ih =>
    simp only [List.foldl_cons]
    exact ih (clause_price hR (hL c (by simp))) (fun x hx => hL x (by simp [hx]))

theorem rules_price {laws : List (Nat × Law)} (hG : G.Valid)
    (hL : ∀ x ∈ laws, ∀ c ∈ x.2.clauses, ClausePriceOk G c) : RulesPriceOk G (rulesFrom G laws) := by
  have h0 : RulesPriceOk G { pieces := G.pieces, bankRate := G.bankRate, worth := [] } := by
    have hG := valid_shape hG
    simp only [GameDef.shapeChecks, Bool.and_eq_true] at hG
    intro d hd
    exact List.all_eq_true.mp hG.1.1.1.1.1.1.1.1.1.1.2 d hd
  unfold rulesFrom
  generalize ({ pieces := G.pieces, bankRate := G.bankRate, worth := [] } : Rules) = R at h0
  induction laws generalizing R with
  | nil => exact h0
  | cons x t ih =>
    simp only [List.foldl_cons]
    exact ih (fun y hy => hL y (by simp [hy])) _ (law_price h0 (hL x (by simp)))

/-- A law with no problems sets only checked prices. -/
theorem lawProblems_price {s : State G} {L : Law} (h : lawProblems G s L = []) :
    ∀ c ∈ L.clauses, ClausePriceOk G c := by
  simp only [lawProblems, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  intro c hc
  have hp := h.2 c hc
  cases c with
  | setCost k b =>
    simp only [clauseProblems, List.append_eq_nil_iff] at hp
    exact ite_nil (c := G.bundleOk b = true) hp.2
  | newPiece p =>
    simp only [clauseProblems, List.append_eq_nil_iff] at hp
    exact ite_nil (c := G.bundleOk p.cost = true) hp.1.2
  | onHarvest _ => trivial
  | onBuild _ _ => trivial
  | onRoundEnd _ => trivial
  | onRoll _ => trivial
  | setPoints _ _ => trivial
  | setBankRate _ => trivial
  | setWorth _ _ => trivial
  | repeal _ => trivial

/-- Every law in force sets only checked prices. -/
def LawPrices (G : GameDef) (s : State G) : Prop :=
  ∀ x ∈ s.laws, ∀ c ∈ x.2.clauses, ClausePriceOk G c

theorem LawPrices.step {s s' : State G} {e : Event} (hp : LawPrices G s)
    (h : Engine.step G s e = .ok s') : LawPrices G s' := by
  by_cases hsame : s'.laws = s.laws
  · rw [LawPrices, hsame]
    exact hp
  · obtain ⟨seat, id, p, L, rfl, _, _, _, _, _, hl⟩ := laws_change h hsame
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hb' : voteBody s seat id true = .ok s1 := hb
    have hl1 : s'.laws = s1.laws := (finish_laws hf).trans rfl
    obtain ⟨_, p', L', _, _, _, ⟨_, hs1⟩ | ⟨_, hs1⟩⟩ := voteBody_ok hb'
    · have hnil : lawProblems G s L' = [] ∧ s1.laws = enact s.laws id L' := by
        by_cases hx : (lawProblems G s L').isEmpty = true
        · refine ⟨List.isEmpty_iff.mp hx, ?_⟩
          rw [hs1]
          unfold decideLaw
          simp [hx]
        · exfalso
          apply hsame
          rw [hl1, hs1]
          unfold decideLaw
          simp [hx]
      intro x hx
      rw [hl1, hnil.2] at hx
      rcases mem_enact hx with hm | rfl
      · exact hp x hm
      · exact lawProblems_price hnil.1
    · exact absurd (by rw [hl1, hs1]) hsame

/-! ## Commandment VII -/

theorem costEntries_eq (s : State G) (p : Seat) (k : PieceKind) :
    s.costEntries p k = bundleEntries (.player p) .bank (s.costOf k) .cost := rfl

theorem isTurnOf_mem {s : State G} {p : Seat} (h : s.isTurnOf p = true) : p ∈ s.turnOrder := by
  simp only [State.isTurnOf, beq_iff_eq, State.currentSeat] at h
  exact List.mem_of_getElem? h

/-- What `canPlace` requires. -/
theorem canPlace_parts {s : State G} {p : Seat} {k : PieceKind} {loc : Loc}
    (h : s.canPlace p k loc = true) :
    s.phase = .actions ∧ s.isTurnOf p = true ∧ s.actionsThisTurn p < maxActionsPerTurn ∧
      ∃ d, s.rules.piece? k = some d ∧ s.affords p d.cost = true := by
  simp only [State.canPlace, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  split at h4
  · rename_i d hd
    simp only [Bool.and_eq_true] at h4
    exact ⟨d, hd, h4.1.1.1⟩
  · cases h4

/-- A build's cost and the laws reacting to it post, for a seat that can pay. -/
theorem build_posts {s : State G} (hG : G.Valid) (hprices : LawPrices G s) {p : Seat} {k : PieceKind}
    {d : PieceDef} (hd : s.rules.piece? k = some d) (haff : s.affords p d.cost = true) :
    ∃ b, s.books.postAll (s.costEntries p k ++
      lawEntries (s.afterPosting (s.costEntries p k)) (.build p k)) = some b := by
  have hcost : s.costOf k = d.cost := by simp [State.costOf, hd]
  have hmem : d ∈ s.rules.pieces := List.mem_of_find?_eq_some hd
  have hok : G.bundleOk d.cost = true := rules_price hG hprices d hmem
  have hne : (Account.player p) ≠ .bank := by simp
  obtain ⟨b1, h1⟩ : ∃ b1, s.books.postAll (s.costEntries p k) = some b1 := by
    rw [costEntries_eq, hcost]
    exact bundle_posts (bundleOk_nodup hok) ((affords_iff s p _).mp haff) hne
  obtain ⟨b2, h2⟩ := settle_posts (s.afterPosting (s.costEntries p k))
    ((s.afterPosting (s.costEntries p k)).laws.flatMap fun x =>
      Law.plan (s.afterPosting (s.costEntries p k)) (.build p k) x.2)
  rw [afterPosting_books h1] at h2
  refine ⟨b2, ?_⟩
  rw [postAll_append, h1, Option.bind_some]
  exact h2

theorem build_is_exact (hG : G.Valid) (s : State G) (hprices : LawPrices G s) (hi : IdInv s)
    (p : Seat) (k : PieceKind) (loc : Loc) (hPhase : s.phase = .actions) :
    ((∃ s', Engine.step G s (.move p (.place k loc)) = .ok s') ↔ s.canPlace p k loc = true) ∧
    ∀ s', Engine.step G s (.move p (.place k loc)) = .ok s' →
      s'.pieces = s.placedPieces p k loc ∧
      ∃ refunds, newEntries s s' =
          s.costEntries p k ++ lawEntries (s.afterPosting (s.costEntries p k)) (.build p k) ++ refunds ∧
        (∀ x ∈ refunds, x.reason = .refund) ∧
        (refunds = [] ∨ s'.phase = .ended) := by
  have hbuild : ∀ s', Engine.step G s (.move p (.place k loc)) = .ok s' →
      ∃ s1, buildBody s p k loc = .ok s1 ∧ checkWin (countAction s1 p) = .ok s' := by
    intro s' h
    obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
    have hb' : placeBody s p k loc = .ok s1 := hb
    rcases placeBody_ok hb' with ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [hPhase] at h1
      cases h1
    · exact ⟨s1, h2, hf⟩
  constructor
  · constructor
    · rintro ⟨s', h⟩
      obtain ⟨s1, hb, _⟩ := hbuild s' h
      exact (buildBody_ok hb).1
    · intro hc
      obtain ⟨_, hturn, hA, d, hd, haff⟩ := canPlace_parts hc
      have hca := canAct_of (isTurnOf_mem hturn) hA
      obtain ⟨b, hb⟩ := build_posts hG hprices hd haff
      have hbody : buildBody s p k loc = .ok { s with
          books := b
          journal := s.journal ++ (s.costEntries p k ++
            lawEntries (s.afterPosting (s.costEntries p k)) (.build p k))
          pieces := s.placedPieces p k loc
          builtThisRound := s.builtThisRound ++ [(p, k)] } := by
        unfold buildBody
        simp only [hc, ↓reduceIte]
        rw [record_some hb]
      obtain ⟨s', h1, _⟩ := checkWin_some hG (countAction { s with
          books := b
          journal := s.journal ++ (s.costEntries p k ++
            lawEntries (s.afterPosting (s.costEntries p k)) (.build p k))
          pieces := s.placedPieces p k loc
          builtThisRound := s.builtThisRound ++ [(p, k)] } p) hi.deal_nodup hi.signers_nodup
      refine ⟨s', ?_⟩
      have hpb : placeBody s p k loc = buildBody s p k loc := by
        unfold placeBody
        rw [hPhase]
      unfold Engine.step
      rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
      simp only [actThenCheckWin, act, hca, ↓reduceIte, moveBody, hpb, hbody]
      exact h1
  · intro s' h
    obtain ⟨s1, hb, hf⟩ := hbuild s' h
    obtain ⟨_, _, _, hs1⟩ := buildBody_ok hb
    rcases checkWin_ok hf with ⟨rfl, _⟩ | ⟨w, hw⟩
    · subst hs1
      exact ⟨rfl, [], newEntries_of (by simp [countAction]), by simp, Or.inl rfl⟩
    · obtain ⟨bk, _, hs2⟩ := endGame_ok hw
      refine ⟨by rw [hs2, hs1]; rfl,
        (countAction s1 p).deals.flatMap (countAction s1 p).refundEntries,
        newEntries_of (by rw [hs2, hs1]; simp [countAction, List.append_assoc]), ?_,
        Or.inr (by rw [hs2])⟩
      intro x hx
      obtain ⟨d, _, hx⟩ := List.mem_flatMap.mp hx
      exact (refundEntries_form hx).1

end Charter.Proofs
