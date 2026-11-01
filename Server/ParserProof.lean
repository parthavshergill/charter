import Server.ResourcesNamed

/-!
# Why the parser ignores nothing

The proof behind `Server/ParserFacts.lean`. Each parser gets one lemma with the same two parts: the
S-expression can be rebuilt from what the parser returned, and every resource in the result is in the
game. The printer in `Server/Rules.lean` does the rebuilding, which saves writing that function again.
The statements in `Server/ParserFacts.lean` do not mention the printer.
-/

namespace Charter.Rules
open Charter SExp

private theorem bind_ok {α β : Type} {x : P α} {f : α → P β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

private theorem map_ok {α β : Type} {x : P α} {f : α → β} {b : β} :
    (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Functor.map, Except.map]

private theorem pure_ok {α : Type} {a b : α} : (pure a : P α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- What a parser promises: it can be undone, and it names only resources in `rs`. -/
private def Faithful {α : Type} (rs : List Res) (g : SExp → P α) (print : α → SExp)
    (names : α → List Res) : Prop :=
  ∀ x v, g x = .ok v → print v = x ∧ ∀ r ∈ names v, r ∈ rs

/-- Reading a list item by item keeps that promise. -/
private theorem mapM_ok {α : Type} {rs : List Res} {g : SExp → P α} {print : α → SExp}
    {names : α → List Res} (hg : Faithful rs g print names) {xs : List SExp} {vs : List α}
    (h : xs.mapM g = .ok vs) : vs.map print = xs ∧ ∀ v ∈ vs, ∀ r ∈ names v, r ∈ rs := by
  induction xs generalizing vs with
  | nil =>
    have : vs = [] := by simpa [pure, Except.pure] using h.symm
    simp [this]
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_ok, pure_ok] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    have h1 := hg _ _ ha
    have h2 := ih has
    simp only [List.map_cons, h1.1, h2.1, List.mem_cons, forall_eq_or_imp, true_and]
    exact ⟨h1.2, h2.2⟩

attribute [local grind =] exprS condS exprNames condNames effectS effectNames refNames natS partyS placementS
  clauseS clauseNames payS

/-- Go through each branch of a parser: a branch that fails has nothing to check, and the others follow
from the lemmas marked for `grind`. -/
local macro "check_branches " h:ident : tactic =>
  `(tactic| (split at $h:ident <;> (try simp only [map_ok, bind_ok, pure_ok] at $h:ident) <;>
    first | (cases $h:ident; done) | grind))

private theorem parseNat_ok {x : SExp} {n : Nat} (h : parseNat x = .ok n) : natS n = x := by
  unfold parseNat at h
  split at h
  · split at h
    · cases h; simp only [natS]; congr 1; omega
    · cases h
  · cases h

private theorem parseRes_ok {rs : List Res} {x : SExp} {r : Res} (h : parseRes rs x = .ok r) :
    SExp.atom r = x ∧ r ∈ rs := by
  unfold parseRes at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨rfl, by simpa using hc⟩
    · cases h
  · cases h

attribute [local grind →] parseNat_ok parseRes_ok

private theorem parseKind_ok {x : SExp} {k : PieceKind} (h : parseKind x = .ok k) : SExp.atom k = x := by
  unfold parseKind at h
  check_branches h

private theorem parseParty_ok {x : SExp} {p : Party} (h : parseParty x = .ok p) : partyS p = x := by
  unfold parseParty at h
  check_branches h

attribute [local grind →] parseKind_ok parseParty_ok

private theorem parseResRef_ok {rs : List Res} {x : SExp} {r : ResRef} (h : parseResRef rs x = .ok r) :
    resRefS r = x ∧ ∀ n ∈ refNames r, n ∈ rs := by
  unfold parseResRef at h
  split at h
  · cases h; simp [resRefS, refNames]
  · simp only [map_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hr⟩ := parseRes_ok ha
    simp [resRefS, refNames, hr]

private theorem parseBundle_ok {rs : List Res} {x : SExp} {b : Bundle} (h : parseBundle rs x = .ok b) :
    bundleS b = x ∧ ∀ r ∈ b.map (·.1), r ∈ rs := by
  unfold parseBundle at h
  split at h
  · have := mapM_ok (rs := rs) (print := fun x => .list [.atom x.1, natS x.2]) (names := fun x => [x.1])
      (by
        intro y v hy
        dsimp only at hy
        split at hy
        · simp only [bind_ok, pure_ok] at hy
          obtain ⟨a, ha, n, hn, rfl⟩ := hy
          obtain ⟨rfl, hr⟩ := parseRes_ok ha
          simp [parseNat_ok hn, hr]
        · cases hy) h
    simpa [bundleS] using this
  · cases h

attribute [local grind →] parseResRef_ok parseBundle_ok

private theorem expr_cond_ok (rs : List Res) :
    Faithful rs (parseExpr rs) exprS exprNames ∧ Faithful rs (parseCond rs) condS condNames := by
  apply parseExpr.mutual_induct
    (fun x => ∀ e, parseExpr rs x = .ok e → exprS e = x ∧ ∀ r ∈ exprNames e, r ∈ rs)
    (fun x => ∀ c, parseCond rs x = .ok c → condS c = x ∧ ∀ r ∈ condNames c, r ∈ rs)
  all_goals
    intros
    rename_i h
    simp only [parseExpr, parseCond, bind_ok, pure_ok] at h
    first
      | (cases h; done)
      | grind [Int.toNat_of_nonneg]

private theorem parseExpr_ok {rs : List Res} {x : SExp} {e : Expr} (h : parseExpr rs x = .ok e) :
    exprS e = x ∧ ∀ r ∈ exprNames e, r ∈ rs := (expr_cond_ok rs).1 x e h

private theorem parseCond_ok {rs : List Res} {x : SExp} {c : Cond} (h : parseCond rs x = .ok c) :
    condS c = x ∧ ∀ r ∈ condNames c, r ∈ rs := (expr_cond_ok rs).2 x c h

attribute [local grind →] parseExpr_ok parseCond_ok

private theorem parseMove_ok (rs : List Res) : Faithful rs (parseMove rs) effectS effectNames := by
  intro x e h
  unfold parseMove parseTransfer at h
  split at h
  · simp only [bind_ok, pure_ok] at h
    grind
  · check_branches h

/-- A list of effects keeps the promise too, in the printer's own form for lists of effects. -/
private theorem effects_ok {rs : List Res} {g : SExp → P Effect} (hg : Faithful rs g effectS effectNames)
    {xs : List SExp} {es : List Effect} (h : xs.mapM g = .ok es) :
    effectsS es = xs ∧ ∀ r ∈ effectsNames es, r ∈ rs := by
  obtain ⟨h1, h2⟩ := mapM_ok hg h
  subst h1
  clear h
  induction es with
  | nil => simp [effectsS, effectsNames]
  | cons e es ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h2
    simp only [effectsS, effectsNames, List.map_cons, List.mem_append]
    have := ih h2.2
    grind

private theorem parseInnerEffect_ok (rs : List Res) : Faithful rs (parseInnerEffect rs) effectS effectNames := by
  intro x e h
  unfold parseInnerEffect at h
  split at h
  · simp only [bind_ok] at h
    obtain ⟨c, hc, b, hb, h⟩ := h
    split at h
    · cases h
    · simp only [pure_ok] at h
      have := effects_ok (parseMove_ok rs) hb
      grind
  · exact parseMove_ok rs _ _ h

private theorem parseEffect_ok (rs : List Res) : Faithful rs (parseEffect rs) effectS effectNames := by
  intro x e h
  unfold parseEffect at h
  split at h
  · simp only [bind_ok] at h
    obtain ⟨c, hc, b, hb, h⟩ := h
    split at h
    · cases h
    · simp only [pure_ok] at h
      have := effects_ok (parseInnerEffect_ok rs) hb
      grind
  · exact parseInnerEffect_ok rs _ _ h

private theorem parseEffects1_ok {rs : List Res} {what : String} {xs : List SExp} {b : List Effect}
    (h : parseEffects1 rs what xs = .ok b) : effectsS b = xs ∧ ∀ r ∈ effectsNames b, r ∈ rs := by
  unfold parseEffects1 at h
  simp only [bind_ok] at h
  obtain ⟨es, hes, h⟩ := h
  split at h
  · cases h
  · simp only [pure_ok] at h
    subst h
    exact effects_ok (parseEffect_ok rs) hes

private theorem parsePlacement_ok {x : SExp} {p : Placement} (h : parsePlacement x = .ok p) :
    placementS p = x := by
  unfold parsePlacement at h
  check_branches h

attribute [local grind →] parseEffects1_ok parsePlacement_ok

private theorem parseClause_ok (rs : List Res) : Faithful rs (parseClause rs) clauseS clauseNames := by
  intro x c h
  unfold parseClause at h
  check_branches h

private theorem parseLaw_ok {rs : List Res} {x : SExp} {L : Law} (h : parseLaw rs x = .ok L) :
    lawS L = x ∧ ∀ r ∈ L.clauses.flatMap clauseNames, r ∈ rs := by
  unfold parseLaw at h
  split at h
  · simp only [bind_ok] at h
    obtain ⟨cs, hcs, h⟩ := h
    split at h
    · cases h
    · simp only [pure_ok] at h
      subst h
      obtain ⟨h1, h2⟩ := mapM_ok (parseClause_ok rs) hcs
      simp only [lawS, h1, List.mem_flatMap]
      exact ⟨trivial, fun r ⟨c, hc, hr⟩ => h2 c hc r hr⟩
  · cases h

private theorem parsePayee_ok {x : SExp} {p : Payee} (h : parsePayee x = .ok p) : payeeS p = x := by
  unfold parsePayee at h
  split at h
  · cases h; rfl
  · simp only [map_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact parseNat_ok ha

attribute [local grind →] parsePayee_ok

private theorem parsePay_ok (rs : List Res) : Faithful rs (parsePay rs) payS (fun p => [p.res]) := by
  intro x p h
  unfold parsePay at h
  check_branches h

private theorem parseNat_faithful (rs : List Res) : Faithful rs parseNat natS (fun _ => []) := by
  intro x n h
  simp [parseNat_ok h]

private theorem parseTerm_ok (rs : List Res) : Faithful rs (parseTerm rs) termS (fun t => t.pays.map (·.res)) := by
  intro x t h
  unfold parseTerm at h
  split at h
  all_goals (try simp only [map_ok, bind_ok, pure_ok] at h)
  · obtain ⟨ps, hps, rfl⟩ := h
    have := mapM_ok (parsePay_ok rs) hps
    grind [termS, Term.pays]
  · obtain ⟨s, hs, k, hk, ps, hps, rfl⟩ := h
    have := mapM_ok (parsePay_ok rs) hps
    grind [termS, Term.pays]
  · obtain ⟨s, hs, k, hk, ns, hns, rfl⟩ := h
    have := mapM_ok (parseNat_faithful rs) hns
    grind [termS, Term.pays]
  · obtain ⟨a, ha, b, hb, rfl⟩ := h
    grind [termS, Term.pays]
  · cases h

private theorem parseDeposit_ok (rs : List Res) : Faithful rs (parseDeposit rs)
    (fun x => .list [natS x.1, .atom x.2.1, natS x.2.2]) (fun x => [x.2.1]) := by
  intro x v h
  unfold parseDeposit at h
  check_branches h

private theorem parseDeal_ok {rs : List Res} {x : SExp} {d : Deal} (h : parseDeal rs x = .ok d) :
    dealS d = x ∧ ∀ r ∈ d.deposits.map (·.2.1) ++ d.allPays.map (·.res), r ∈ rs := by
  unfold parseDeal at h
  split at h
  · simp only [bind_ok, pure_ok] at h
    obtain ⟨ss, hss, n, hn, e, he, ds, hds, ts, hts, rfl⟩ := h
    obtain ⟨s1, -⟩ := mapM_ok (parseNat_faithful rs) hss
    obtain ⟨d1, d2⟩ := mapM_ok (parseDeposit_ok rs) hds
    obtain ⟨t1, t2⟩ := mapM_ok (parseTerm_ok rs) hts
    refine ⟨by simp only [dealS, s1, d1, t1, parseNat_ok hn, parseNat_ok he], ?_⟩
    intro r hr
    simp only [Deal.allPays, List.mem_append, List.mem_map, List.mem_flatMap] at hr
    rcases hr with ⟨v, hv, rfl⟩ | ⟨p, ⟨t, ht, hp⟩, rfl⟩
    · exact d2 v hv _ (by simp)
    · exact t2 t ht _ (List.mem_map_of_mem hp)
  · cases h

/-- The S-expression can be rebuilt from what the parser returned, and every resource it names is in
the game. `Server/ParserFacts.lean` draws its two statements from this. -/
theorem parse_ok {rs : List Res} {x : SExp} {p : Proposal} (h : parseProposalSExp rs x = .ok p) :
    proposalToSExp p = x ∧ ∀ r ∈ resourcesNamed p, r ∈ rs := by
  unfold parseProposalSExp at h
  split at h
  · simp only [map_ok] at h
    obtain ⟨L, hL, rfl⟩ := h
    exact parseLaw_ok hL
  · simp only [map_ok] at h
    obtain ⟨d, hd, rfl⟩ := h
    exact parseDeal_ok hd
  · cases h

end Charter.Rules
