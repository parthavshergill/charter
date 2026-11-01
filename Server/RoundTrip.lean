import Server.Readable

/-!
# Printing a law and reading it back

People and Claude seats read a law as text. The engine runs a `Law` value. This file proves that the
two agree: if you turn a law or a deal into its S-expression and parse that S-expression, you get back
exactly the same value. So a printer cannot show 3 for a law that pays 5, and a parser cannot drop a
clause.

This is about the S-expression, not the characters. `SExp.render` and `SExp.read`, which turn an
S-expression into characters and back, are only tested.
-/

namespace Charter.Rules
open Charter SExp

/-! ## Small facts about reading a list -/

private theorem ok_bind {α β : Type} (a : α) (f : α → P β) : (Except.ok a >>= f) = f a := rfl
private theorem ok_map {α β : Type} (a : α) (f : α → β) : (f <$> (Except.ok a : P α)) = .ok (f a) := rfl
private theorem pure_eq {α : Type} (a : α) : (pure a : P α) = .ok a := rfl

/-- Reading each item of a printed list gives back the list. -/
private theorem mapM_map_ok {α : Type} (f : α → SExp) (g : SExp → P α) (l : List α)
    (h : ∀ x ∈ l, g (f x) = .ok x) : (l.map f).mapM g = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.mapM_cons, hx, hxs]
    rfl

/-! ## The pieces -/

private theorem parseNat_natS (n : Nat) : parseNat (natS n) = .ok n := by
  simp [natS, parseNat]

private theorem parseNat_map (l : List Nat) : (l.map natS).mapM parseNat = .ok l :=
  mapM_map_ok _ _ _ fun x _ => parseNat_natS x

private theorem parseRes_atom (rs : List Res) (r : Res) (h : Readable.res rs r) :
    parseRes rs (.atom r) = .ok r := by
  simp only [parseRes, show rs.contains r = true from h, ite_true]

private theorem parseResRef_resRefS (rs : List Res) (r : ResRef) (h : Readable.resRef rs r) :
    parseResRef rs (resRefS r) = .ok r := by
  cases r with
  | harvested => simp [resRefS, parseResRef]
  | lit r =>
    simp only [Readable.resRef, Bool.and_eq_true, bne_iff_ne] at h
    have : parseResRef rs (.atom r) = ResRef.lit <$> parseRes rs (.atom r) := by
      rw [parseResRef]
      simpa using h.1
    simp [resRefS, this, parseRes_atom rs r h.2, ok_map]

private theorem parseParty_partyS (p : Party) : parseParty (partyS p) = .ok p := by
  cases p <;> simp [partyS, parseParty]

private theorem parseBundle_bundleS (rs : List Res) (b : Bundle) (h : Readable.bundle rs b) :
    parseBundle rs (bundleS b) = .ok b := by
  simp only [bundleS, parseBundle]
  apply mapM_map_ok
  intro x hx
  have hr : Readable.res rs x.1 := by
    simp only [Readable.bundle, List.all_eq_true] at h
    exact h x hx
  simp only [parseRes_atom rs x.1 hr, parseNat_natS, ok_bind, pure_eq]

/-- Only a plain number prints as a plain number. -/
private theorem exprS_num (e : Expr) (i : Int) (h : exprS e = .num i) : ∃ n, e = .lit n := by
  cases e <;> simp [exprS, natS] at h ⊢

mutual
  private theorem parseExpr_exprS (rs : List Res) : (e : Expr) → Readable.expr rs e →
      parseExpr rs (exprS e) = .ok e
    | .lit n, _ => by simp [exprS, natS, parseExpr]
    | .harvestedAmount, _ => by simp [exprS, parseExpr]
    | .rolled, _ => by simp [exprS, parseExpr]
    | .round, _ => by simp [exprS, parseExpr]
    | .declared p r, h => by
      simp only [Readable.expr] at h
      simp only [exprS, parseExpr, parseParty_partyS, parseResRef_resRefS rs r h, ok_bind, pure_eq]
    | .holding p r, h => by
      simp only [Readable.expr] at h
      simp only [exprS, parseExpr, parseParty_partyS, parseResRef_resRefS rs r h, ok_bind, pure_eq]
    | .points p, _ => by
      simp only [exprS, parseExpr, parseParty_partyS, ok_bind, pure_eq]
    | .count p k, _ => by
      simp only [exprS, parseExpr, parseParty_partyS, parseKind, ok_bind, pure_eq]
    | .add a b, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .sub a b, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .mul a b, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .min a b, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .max a b, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .div a n, h => by
      simp only [Readable.expr] at h
      have hn : parseNat (.num (n : Int)) = .ok n := parseNat_natS n
      simp only [exprS, natS, parseExpr, parseExpr_exprS rs a h, hn, ok_bind, pure_eq]
    | .divBy a b, h => by
      have hb : ∀ i : Int, exprS b = .num i → False := by
        intro i hi
        obtain ⟨n, rfl⟩ := exprS_num b i hi
        simp [Readable.expr] at h
      have split : Readable.expr rs a = true ∧ Readable.expr rs b = true := by
        cases b <;> first | (simp [Readable.expr] at h; done) | simpa [Readable.expr] using h
      rw [exprS, parseExpr]
      · simp only [parseExpr_exprS rs a split.1, parseExpr_exprS rs b split.2, ok_bind, pure_eq]
      · exact hb
    | .totalOver c a, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseCond_condS rs c h.1, parseExpr_exprS rs a h.2, ok_bind, pure_eq]
    | .mostOver c a, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseCond_condS rs c h.1, parseExpr_exprS rs a h.2, ok_bind, pure_eq]
    | .leastOver c a, h => by
      simp only [Readable.expr, Bool.and_eq_true] at h
      simp only [exprS, parseExpr, parseCond_condS rs c h.1, parseExpr_exprS rs a h.2, ok_bind, pure_eq]

  private theorem parseCond_condS (rs : List Res) : (c : Cond) → Readable.cond rs c →
      parseCond rs (condS c) = .ok c
    | .yes, _ => by simp [condS, parseCond]
    | .lt a b, h => by
      simp only [Readable.cond, Bool.and_eq_true] at h
      simp only [condS, parseCond, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .le a b, h => by
      simp only [Readable.cond, Bool.and_eq_true] at h
      simp only [condS, parseCond, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .eq a b, h => by
      simp only [Readable.cond, Bool.and_eq_true] at h
      simp only [condS, parseCond, parseExpr_exprS rs a h.1, parseExpr_exprS rs b h.2, ok_bind, pure_eq]
    | .and a b, h => by
      simp only [Readable.cond, Bool.and_eq_true] at h
      simp only [condS, parseCond, parseCond_condS rs a h.1, parseCond_condS rs b h.2, ok_bind, pure_eq]
    | .or a b, h => by
      simp only [Readable.cond, Bool.and_eq_true] at h
      simp only [condS, parseCond, parseCond_condS rs a h.1, parseCond_condS rs b h.2, ok_bind, pure_eq]
    | .not c, h => by
      simp only [Readable.cond] at h
      simp only [condS, parseCond, parseCond_condS rs c h, ok_bind, pure_eq]
    | .harvestedIs r, h => by
      simp only [Readable.cond] at h
      simp only [condS, parseCond, parseRes_atom rs r h, ok_bind, pure_eq]
end

/-- `effectsS` is a plain map. -/
private theorem effectsS_eq (b : List Effect) : effectsS b = b.map effectS := by
  induction b with
  | nil => simp [effectsS]
  | cons e es ih => simp [effectsS, ih]

private theorem parseMove_effectS (rs : List Res) (e : Effect) (h : Readable.move rs e) :
    parseMove rs (effectS e) = .ok e := by
  cases e with
  | transfer f t r a =>
    simp only [Readable.move, Bool.and_eq_true] at h
    simp [effectS, parseMove, parseTransfer, parseParty_partyS, parseResRef_resRefS rs r h.1,
      parseExpr_exprS rs a h.2, ok_bind, pure_eq]
  | movePiece f t k =>
    simp only [effectS, parseMove, parseParty_partyS, parseKind, ok_bind, pure_eq]
  | forEach c b => simp [Readable.move] at h
  | «when» c b => simp [Readable.move] at h

private theorem parseInnerEffect_effectS (rs : List Res) (e : Effect) (h : Readable.inner rs e) :
    parseInnerEffect rs (effectS e) = .ok e := by
  cases e with
  | «when» c b =>
    simp only [Readable.inner, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    have hb : (b.map effectS).mapM (parseMove rs) = .ok b :=
      mapM_map_ok _ _ _ fun x hx => parseMove_effectS rs x (h.2 x hx)
    simp only [effectS, parseInnerEffect, parseCond_condS rs c h.1.1, effectsS_eq, hb, ok_bind, h.1.2,
      Bool.false_eq_true, ite_false, pure_eq]
  | transfer f t r a =>
    have hm : Readable.move rs (.transfer f t r a) := by simpa [Readable.inner] using h
    have := parseMove_effectS rs _ hm
    simpa [effectS, parseInnerEffect] using this
  | movePiece f t k =>
    have := parseMove_effectS rs (.movePiece f t k) (by simp [Readable.move])
    simpa [effectS, parseInnerEffect] using this
  | forEach c b => simp [Readable.inner, Readable.move] at h

private theorem parseEffect_effectS (rs : List Res) (e : Effect) (h : Readable.top rs e) :
    parseEffect rs (effectS e) = .ok e := by
  cases e with
  | forEach c b =>
    simp only [Readable.top, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    have hb : (b.map effectS).mapM (parseInnerEffect rs) = .ok b :=
      mapM_map_ok _ _ _ fun x hx => parseInnerEffect_effectS rs x (h.2 x hx)
    simp only [effectS, parseEffect, parseCond_condS rs c h.1.1, effectsS_eq, hb, ok_bind, h.1.2,
      Bool.false_eq_true, ite_false, pure_eq]
  | «when» c b =>
    have := parseInnerEffect_effectS rs (.when c b) (by simpa [Readable.top] using h)
    simpa [effectS, parseEffect] using this
  | transfer f t r a =>
    have := parseInnerEffect_effectS rs (.transfer f t r a) (by simpa [Readable.top] using h)
    simpa [effectS, parseEffect] using this
  | movePiece f t k =>
    have := parseInnerEffect_effectS rs (.movePiece f t k) (by simpa [Readable.top] using h)
    simpa [effectS, parseEffect] using this

private theorem parseEffects1_effectsS (rs : List Res) (what : String) (b : List Effect)
    (h : Readable.body rs b) : parseEffects1 rs what (effectsS b) = .ok b := by
  simp only [Readable.body, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  have hb : (b.map effectS).mapM (parseEffect rs) = .ok b :=
    mapM_map_ok _ _ _ fun x hx => parseEffect_effectS rs x (h.2 x hx)
  simp only [parseEffects1, effectsS_eq, hb, ok_bind, h.1, Bool.false_eq_true, ite_false, pure_eq]

private theorem parsePlacement_placementS (p : Placement) : parsePlacement (placementS p) = .ok p := by
  cases p <;> simp [placementS, parsePlacement, parseKind, ok_bind, pure_eq]

private theorem parseClause_clauseS (rs : List Res) (c : Clause) (h : Readable.clause rs c) :
    parseClause rs (clauseS c) = .ok c := by
  cases c with
  | onHarvest b =>
    simp only [clauseS, parseClause, parseEffects1_effectsS rs _ b h, ok_map]
  | onBuild k b =>
    simp only [clauseS, parseClause, parseKind, parseEffects1_effectsS rs _ b h, ok_bind, pure_eq]
  | onRoundEnd b =>
    simp only [clauseS, parseClause, parseEffects1_effectsS rs _ b h, ok_map]
  | onRoll b =>
    simp only [clauseS, parseClause, parseEffects1_effectsS rs _ b h, ok_map]
  | now b =>
    simp only [clauseS, parseClause, parseEffects1_effectsS rs _ b h, ok_map]
  | setCost k b =>
    simp only [clauseS, parseClause, parseKind, parseBundle_bundleS rs b h, ok_bind, pure_eq]
  | setPoints k n =>
    simp only [clauseS, parseClause, parseKind, parseNat_natS, ok_bind, pure_eq]
  | setBankRate n =>
    simp only [clauseS, parseClause, parseNat_natS, ok_bind, pure_eq]
  | setWorth r n =>
    simp only [clauseS, parseClause, parseRes_atom rs r h, parseNat_natS, ok_bind, pure_eq]
  | newPiece p =>
    cases p with
    | mk name cost points placement yield limit =>
      have hc : Readable.bundle rs cost := h
      simp only [clauseS, parseClause, parseBundle_bundleS rs cost hc, parseNat_natS,
        parsePlacement_placementS, ok_bind, pure_eq]
  | repeal n =>
    simp only [clauseS, parseClause, parseNat_natS, ok_bind, pure_eq]
  | endGame => simp [clauseS, parseClause]

private theorem parseLaw_lawS (rs : List Res) (L : Law) (h : Readable.law rs L) :
    parseLaw rs (lawS L) = .ok L := by
  cases L with
  | mk title clauses =>
    simp only [Readable.law, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    have hc : (clauses.map clauseS).mapM (parseClause rs) = .ok clauses :=
      mapM_map_ok _ _ _ fun x hx => parseClause_clauseS rs x (h.2 x hx)
    simp only [lawS, parseLaw, hc, ok_bind, h.1, Bool.false_eq_true, ite_false, pure_eq]

private theorem parsePay_payS (rs : List Res) (p : Pay) (h : Readable.pay rs p) :
    parsePay rs (payS p) = .ok p := by
  cases p with
  | mk src dst res amount =>
    have hd : parsePayee (payeeS dst) = .ok dst := by
      cases dst with
      | treasury => simp [payeeS, parsePayee]
      | seat s =>
        have : parsePayee (natS s) = Payee.seat <$> parseNat (natS s) := by
          simp [natS, parsePayee]
        simp [payeeS, this, parseNat_natS, ok_map]
    simp only [payS, parsePay, parseNat_natS, hd, parseRes_atom rs res h, ok_bind, pure_eq]

private theorem parsePays (rs : List Res) (ps : List Pay) (h : ps.all (Readable.pay rs)) :
    (ps.map payS).mapM (parsePay rs) = .ok ps := by
  simp only [List.all_eq_true] at h
  exact mapM_map_ok _ _ _ fun x hx => parsePay_payS rs x (h x hx)

private theorem parseTerm_termS (rs : List Res) (t : Term) (h : Readable.term rs t) :
    parseTerm rs (termS t) = .ok t := by
  cases t with
  | everyRound ps =>
    simp only [termS, parseTerm, parsePays rs ps h, ok_map]
  | onBuild s k ps =>
    simp only [termS, parseTerm, parseNat_natS, parseKind, parsePays rs ps h, ok_bind, pure_eq]
  | noBuild s k spots =>
    simp only [termS, parseTerm, parseNat_natS, parseKind, parseNat_map, ok_bind, pure_eq]
  | noTrade a b =>
    simp only [termS, parseTerm, parseNat_natS, ok_bind, pure_eq]

private theorem parseDeal_dealS (rs : List Res) (d : Deal) (h : Readable.deal rs d) :
    parseDeal rs (dealS d) = .ok d := by
  cases d with
  | mk title signers rounds exitNotice deposits terms =>
    simp only [Readable.deal, Bool.and_eq_true, List.all_eq_true] at h
    have hd : (deposits.map fun x => SExp.list [natS x.1, .atom x.2.1, natS x.2.2]).mapM
        (parseDeposit rs) = .ok deposits := mapM_map_ok _ _ _ fun x hx => by
      simp only [parseDeposit, parseNat_natS, parseRes_atom rs x.2.1 (h.1 x hx), ok_bind, pure_eq]
    have ht : (terms.map termS).mapM (parseTerm rs) = .ok terms :=
      mapM_map_ok _ _ _ fun x hx => parseTerm_termS rs x (h.2 x hx)
    simp only [dealS, parseDeal, parseNat_map, parseNat_natS, hd, ht, ok_bind, pure_eq]

/-! ## The theorem -/

/-- **What the text says is the law.** Turn a law or a deal into its S-expression, parse that, and you
get back exactly the same value, for any law or deal the text can say.

This does not cover the characters. `SExp.render` and `SExp.read` are only tested. -/
theorem parse_of_print (rs : List Res) (p : Proposal) (h : Readable.proposal rs p) :
    parseProposalSExp rs (proposalToSExp p) = .ok p := by
  cases p with
  | law L =>
    simp only [proposalToSExp, lawS, parseProposalSExp]
    have := parseLaw_lawS rs L h
    simp only [lawS] at this
    simp only [this, ok_map]
  | deal d =>
    simp only [proposalToSExp, dealS, parseProposalSExp]
    have := parseDeal_dealS rs d h
    simp only [dealS] at this
    simp only [this, ok_map]

/-! ## Everything the parser returns can be read back -/

private theorem bind_eq_ok {α β : Type} {x : P α} {f : α → P β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

private theorem map_eq_ok {α β : Type} {x : P α} {f : α → β} {b : β} :
    (f <$> x) = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => simp [Functor.map, Except.map]
  | ok a => simp [Functor.map, Except.map]

private theorem pure_eq_ok {α : Type} {a b : α} : (pure a : P α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- Each thing a list read gave came from one item of the list. -/
private theorem mem_of_mapM {α : Type} {g : SExp → P α} {l : List SExp} {r : List α}
    (h : l.mapM g = .ok r) : ∀ e ∈ r, ∃ x ∈ l, g x = .ok e := by
  induction l generalizing r with
  | nil =>
    have : r = [] := by simpa [pure, Except.pure] using h.symm
    simp [this]
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨a, ha, as, has, rfl⟩ := h
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨x, by simp, ha⟩
    · obtain ⟨y, hy, hg⟩ := ih has e he
      exact ⟨y, by simp [hy], hg⟩

/-- A resource the parser read is real, and it is the atom the text wrote. -/
private theorem res_of_parse {rs : List Res} {x : SExp} {r : Res} (h : parseRes rs x = .ok r) :
    x = .atom r ∧ Readable.res rs r := by
  unfold parseRes at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact ⟨rfl, hc⟩
    · cases h
  · cases h

private theorem resRef_of_parse {rs : List Res} {x : SExp} {r : ResRef} (h : parseResRef rs x = .ok r) :
    Readable.resRef rs r := by
  unfold parseResRef at h
  split at h
  · cases h
    rfl
  · rename_i hx
    simp only [map_eq_ok] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨rfl, hr⟩ := res_of_parse ha
    have hne : a ≠ "res" := fun e => hx (by rw [e])
    simp [Readable.resRef, hr, hne]

private theorem bundle_of_parse {rs : List Res} {x : SExp} {b : Bundle} (h : parseBundle rs x = .ok b) :
    Readable.bundle rs b := by
  unfold parseBundle at h
  split at h
  · simp only [Readable.bundle, List.all_eq_true]
    intro e he
    obtain ⟨y, _, hy⟩ := mem_of_mapM h e he
    split at hy
    · simp only [bind_eq_ok, pure_eq_ok] at hy
      obtain ⟨a, ha, _, _, rfl⟩ := hy
      exact (res_of_parse ha).2
    · cases hy
  · cases h

/-- A computed divisor can be read back unless it is a plain number. -/
private theorem expr_divBy {rs : List Res} {a b : Expr} (ha : Readable.expr rs a = true)
    (hb : Readable.expr rs b = true) (hn : ∀ n, b = .lit n → False) :
    Readable.expr rs (.divBy a b) = true := by
  cases b with
  | lit n => exact (hn n rfl).elim
  | _ => simp_all [Readable.expr]

private theorem expr_cond_of_parse (rs : List Res) :
    (∀ x e, parseExpr rs x = .ok e → Readable.expr rs e = true ∧ ∀ n, e = .lit n → ∃ i, x = .num i) ∧
    (∀ x c, parseCond rs x = .ok c → Readable.cond rs c = true) := by
  apply parseExpr.mutual_induct
    (fun x => ∀ e, parseExpr rs x = .ok e →
      Readable.expr rs e = true ∧ ∀ n, e = .lit n → ∃ i, x = .num i)
    (fun x => ∀ c, parseCond rs x = .ok c → Readable.cond rs c = true)
  case case1 =>
    intro i hi e h
    simp only [parseExpr, hi, ite_true, Except.ok.injEq] at h
    subst h
    exact ⟨by simp [Readable.expr], fun _ _ => ⟨i, rfl⟩⟩
  case case2 =>
    intro i hi e h
    simp only [parseExpr, hi, ite_false] at h
    cases h
  case case3 =>
    intro e h
    simp only [parseExpr, Except.ok.injEq] at h
    subst h
    simp [Readable.expr]
  case case4 =>
    intro e h
    simp only [parseExpr, Except.ok.injEq] at h
    subst h
    simp [Readable.expr]
  case case5 =>
    intro e h
    simp only [parseExpr, Except.ok.injEq] at h
    subst h
    simp [Readable.expr]
  case case6 =>
    intro p r e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, hr, rfl⟩ := h
    simp [Readable.expr, resRef_of_parse hr]
  case case7 =>
    intro p r e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, hr, rfl⟩ := h
    simp [Readable.expr, resRef_of_parse hr]
  case case8 =>
    intro p e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    simp [Readable.expr]
  case case9 =>
    intro p k e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    simp [Readable.expr]
  case case10 =>
    intro a b iha ihb e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.expr, (iha _ ha).1, (ihb _ hb).1]
  case case11 =>
    intro a b iha ihb e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.expr, (iha _ ha).1, (ihb _ hb).1]
  case case12 =>
    intro a b iha ihb e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.expr, (iha _ ha).1, (ihb _ hb).1]
  case case13 =>
    intro a n iha e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, _, rfl⟩ := h
    simp [Readable.expr, (iha _ ha).1]
  case case14 =>
    intro a b hb' iha ihb e h
    rw [parseExpr.eq_13 rs a b hb'] at h
    simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, b₁, hb, rfl⟩ := h
    refine ⟨expr_divBy (iha _ ha).1 (ihb _ hb).1 ?_, by simp⟩
    intro n hn
    obtain ⟨i, hi⟩ := (ihb _ hb).2 n hn
    exact hb' i hi
  case case15 =>
    intro a b iha ihb e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.expr, (iha _ ha).1, (ihb _ hb).1]
  case case16 =>
    intro a b iha ihb e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.expr, (iha _ ha).1, (ihb _ hb).1]
  case case17 =>
    intro c a ihc iha e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, hc, _, ha, rfl⟩ := h
    simp [Readable.expr, ihc _ hc, (iha _ ha).1]
  case case18 =>
    intro c a ihc iha e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, hc, _, ha, rfl⟩ := h
    simp [Readable.expr, ihc _ hc, (iha _ ha).1]
  case case19 =>
    intro c a ihc iha e h
    simp only [parseExpr, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, hc, _, ha, rfl⟩ := h
    simp [Readable.expr, ihc _ hc, (iha _ ha).1]
  case case20 =>
    intro x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 e h
    rw [parseExpr.eq_19 rs x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18] at h
    cases h
  case case21 =>
    intro c h
    simp only [parseCond, Except.ok.injEq] at h
    subst h
    rfl
  case case22 =>
    intro a b iha ihb c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.cond, (iha _ ha).1, (ihb _ hb).1]
  case case23 =>
    intro a b iha ihb c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.cond, (iha _ ha).1, (ihb _ hb).1]
  case case24 =>
    intro a b iha ihb c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.cond, (iha _ ha).1, (ihb _ hb).1]
  case case25 =>
    intro a b iha ihb c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.cond, iha _ ha, ihb _ hb]
  case case26 =>
    intro a b iha ihb c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, _, hb, rfl⟩ := h
    simp [Readable.cond, iha _ ha, ihb _ hb]
  case case27 =>
    intro a iha c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, ha, rfl⟩ := h
    simp [Readable.cond, iha _ ha]
  case case28 =>
    intro r c h
    simp only [parseCond, bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, hr, rfl⟩ := h
    simp only [Readable.cond]
    exact (res_of_parse hr).2
  case case29 =>
    intro x h1 h2 h3 h4 h5 h6 h7 h8 c h
    rw [parseCond.eq_9 rs x h1 h2 h3 h4 h5 h6 h7 h8] at h
    cases h

private theorem move_of_parse {rs : List Res} {x : SExp} {e : Effect} (h : parseMove rs x = .ok e) :
    Readable.move rs e = true := by
  unfold parseMove at h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    rfl
  · unfold parseTransfer at h
    split at h
    · simp only [bind_eq_ok, pure_eq_ok] at h
      obtain ⟨_, _, _, _, _, hr, _, ha, rfl⟩ := h
      simp [Readable.move, resRef_of_parse hr, ((expr_cond_of_parse rs).1 _ _ ha).1]
    · cases h

private theorem inner_of_move {rs : List Res} {e : Effect} (h : Readable.move rs e = true) :
    Readable.inner rs e = true := by
  cases e with
  | «when» c b => simp [Readable.move] at h
  | _ => simpa [Readable.inner] using h

private theorem inner_of_parse {rs : List Res} {x : SExp} {e : Effect}
    (h : parseInnerEffect rs x = .ok e) : Readable.inner rs e = true := by
  unfold parseInnerEffect at h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨_, hc, b, hb, h⟩ := h
    split at h
    · cases h
    · rename_i hne
      simp only [pure_eq_ok] at h
      subst h
      simp only [Readable.inner, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
      refine ⟨⟨(expr_cond_of_parse rs).2 _ _ hc, by simpa using hne⟩, ?_⟩
      intro y hy
      obtain ⟨_, _, hm⟩ := mem_of_mapM hb y hy
      exact move_of_parse hm
  · exact inner_of_move (move_of_parse h)

private theorem top_of_inner {rs : List Res} {e : Effect} (h : Readable.inner rs e = true) :
    Readable.top rs e = true := by
  cases e with
  | forEach c b => simp [Readable.inner, Readable.move] at h
  | _ => simpa [Readable.top] using h

private theorem top_of_parse {rs : List Res} {x : SExp} {e : Effect} (h : parseEffect rs x = .ok e) :
    Readable.top rs e = true := by
  unfold parseEffect at h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨_, hc, b, hb, h⟩ := h
    split at h
    · cases h
    · rename_i hne
      simp only [pure_eq_ok] at h
      subst h
      simp only [Readable.top, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
      refine ⟨⟨(expr_cond_of_parse rs).2 _ _ hc, by simpa using hne⟩, ?_⟩
      intro y hy
      obtain ⟨_, _, hm⟩ := mem_of_mapM hb y hy
      exact inner_of_parse hm
  · exact top_of_inner (inner_of_parse h)

private theorem body_of_parse {rs : List Res} {what : String} {xs : List SExp} {b : List Effect}
    (h : parseEffects1 rs what xs = .ok b) : Readable.body rs b = true := by
  unfold parseEffects1 at h
  simp only [bind_eq_ok] at h
  obtain ⟨b', hb, h⟩ := h
  split at h
  · cases h
  · rename_i hne
    simp only [pure_eq_ok] at h
    subst h
    simp only [Readable.body, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
    refine ⟨by simpa using hne, ?_⟩
    intro y hy
    obtain ⟨_, _, hm⟩ := mem_of_mapM hb y hy
    exact top_of_parse hm

private theorem clause_of_parse {rs : List Res} {x : SExp} {c : Clause} (h : parseClause rs x = .ok c) :
    Readable.clause rs c = true := by
  unfold parseClause at h
  split at h
  · simp only [map_eq_ok] at h
    obtain ⟨_, hb, rfl⟩ := h
    exact body_of_parse hb
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, hb, rfl⟩ := h
    exact body_of_parse hb
  · simp only [map_eq_ok] at h
    obtain ⟨_, hb, rfl⟩ := h
    exact body_of_parse hb
  · simp only [map_eq_ok] at h
    obtain ⟨_, hb, rfl⟩ := h
    exact body_of_parse hb
  · simp only [map_eq_ok] at h
    obtain ⟨_, hb, rfl⟩ := h
    exact body_of_parse hb
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, hb, rfl⟩ := h
    exact bundle_of_parse hb
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, hr, _, _, rfl⟩ := h
    exact (res_of_parse hr).2
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, hb, _, _, _, _, _, _, _, _, rfl⟩ := h
    exact bundle_of_parse hb
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  · cases h
    rfl
  · cases h

private theorem law_of_parse {rs : List Res} {x : SExp} {L : Law} (h : parseLaw rs x = .ok L) :
    Readable.law rs L = true := by
  unfold parseLaw at h
  split at h
  · simp only [bind_eq_ok] at h
    obtain ⟨cs, hcs, h⟩ := h
    split at h
    · cases h
    · rename_i hne
      simp only [pure_eq_ok] at h
      subst h
      simp only [Readable.law, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
      refine ⟨by simpa using hne, ?_⟩
      intro y hy
      obtain ⟨_, _, hm⟩ := mem_of_mapM hcs y hy
      exact clause_of_parse hm
  · cases h

private theorem pay_of_parse {rs : List Res} {x : SExp} {p : Pay} (h : parsePay rs x = .ok p) :
    Readable.pay rs p = true := by
  unfold parsePay at h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, _, hr, _, _, rfl⟩ := h
    exact (res_of_parse hr).2
  · cases h

private theorem pays_of_parse {rs : List Res} {xs : List SExp} {ps : List Pay}
    (h : xs.mapM (parsePay rs) = .ok ps) : ps.all (Readable.pay rs) = true := by
  simp only [List.all_eq_true]
  intro y hy
  obtain ⟨_, _, hm⟩ := mem_of_mapM h y hy
  exact pay_of_parse hm

private theorem term_of_parse {rs : List Res} {x : SExp} {t : Term} (h : parseTerm rs x = .ok t) :
    Readable.term rs t = true := by
  unfold parseTerm at h
  split at h
  · simp only [map_eq_ok] at h
    obtain ⟨_, hp, rfl⟩ := h
    exact pays_of_parse hp
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, _, hp, rfl⟩ := h
    exact pays_of_parse hp
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, rfl⟩ := h
    rfl
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl
  · cases h

private theorem deal_of_parse {rs : List Res} {x : SExp} {d : Deal} (h : parseDeal rs x = .ok d) :
    Readable.deal rs d = true := by
  unfold parseDeal at h
  split at h
  · simp only [bind_eq_ok, pure_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, ds, hds, ts, hts, rfl⟩ := h
    simp only [Readable.deal, Bool.and_eq_true, List.all_eq_true]
    constructor
    · intro y hy
      obtain ⟨z, _, hm⟩ := mem_of_mapM hds y hy
      unfold parseDeposit at hm
      split at hm
      · simp only [bind_eq_ok, pure_eq_ok] at hm
        obtain ⟨_, _, _, hr, _, _, rfl⟩ := hm
        exact (res_of_parse hr).2
      · cases hm
    · intro y hy
      obtain ⟨_, _, hm⟩ := mem_of_mapM hts y hy
      exact term_of_parse hm
  · cases h

/-- Every law and deal the parser returns meets the conditions of `parse_of_print`. -/
theorem readable_of_parse (rs : List Res) (x : SExp) (p : Proposal)
    (h : parseProposalSExp rs x = .ok p) : Readable.proposal rs p := by
  unfold parseProposalSExp at h
  split at h
  · simp only [map_eq_ok] at h
    obtain ⟨_, hL, rfl⟩ := h
    exact law_of_parse hL
  · simp only [map_eq_ok] at h
    obtain ⟨_, hd, rfl⟩ := h
    exact deal_of_parse hd
  · cases h

/-- A law or a deal that a seat proposes as text has no conditions to meet: what the parser returned,
printed and parsed again, is the same value. -/
theorem parse_of_print_of_parse (rs : List Res) (x : SExp) (p : Proposal)
    (h : parseProposalSExp rs x = .ok p) : parseProposalSExp rs (proposalToSExp p) = .ok p :=
  parse_of_print rs p (readable_of_parse rs x p h)

/-- Two different laws or deals the text can say never print the same. So the text cannot show 3 for a
law that pays 5. -/
theorem print_injective (rs : List Res) (p q : Proposal) (hp : Readable.proposal rs p)
    (hq : Readable.proposal rs q) (h : proposalToSExp p = proposalToSExp q) : p = q := by
  have hp' := parse_of_print rs p hp
  have hq' := parse_of_print rs q hq
  rw [h, hq'] at hp'
  exact (Except.ok.inj hp').symm

/-! ## The server runs these same functions -/

theorem parseProposal_eq (text : String) (rs : List Res) :
    parseProposal text rs = (SExp.read text >>= parseProposalSExp rs) := rfl

theorem printProposal_eq (p : Proposal) : printProposal p = (proposalToSExp p).render := rfl

/-! ## Every deal the game accepts can be read back -/

/-- A resource `GameDef.isRes` accepts is one the game's list of names contains. -/
private theorem res_of_isRes {G : GameDef} {r : Res} (h : G.isRes r = true) :
    Readable.res (G.resources.map (·.name)) r = true := by
  simp only [GameDef.isRes, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨d, hd, rfl⟩ := h
  simp only [Readable.res, List.contains_iff_mem, List.mem_map]
  exact ⟨d, hd, rfl⟩

/-- `dealProblems` already checks everything `Readable.deal` asks. So a deal that can run needs no other
condition to round-trip. -/
theorem readable_of_dealProblems {G : GameDef} (s : State G) (d : Deal) (h : dealProblems s d = []) :
    Readable.deal (G.resources.map (·.name)) d = true := by
  simp only [dealProblems, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hdep⟩, hpay⟩, _⟩, _⟩ := h
  simp only [Readable.deal, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro x hx
    apply res_of_isRes
    split at hdep
    · rename_i hall
      simp only [List.all_eq_true] at hall
      exact hall x hx
    · cases hdep
  · intro t ht
    have hall : ∀ p ∈ t.pays, Readable.pay (G.resources.map (·.name)) p = true := by
      intro p hp
      have hmem : p ∈ d.allPays := by
        simp only [Deal.allPays, List.mem_flatMap]
        exact ⟨t, ht, hp⟩
      have hprob := hpay p hmem
      simp only [payProblems, List.append_eq_nil_iff] at hprob
      obtain ⟨⟨_, hres⟩, _⟩ := hprob
      apply res_of_isRes
      split at hres
      · assumption
      · cases hres
    cases t with
    | everyRound ps => simpa [Readable.term, Term.pays] using hall
    | onBuild s k ps => simpa [Readable.term, Term.pays] using hall
    | noBuild _ _ _ => rfl
    | noTrade _ _ => rfl

/-- Every deal that can run round-trips, with no other condition. -/
theorem parse_of_print_of_dealProblems {G : GameDef} (s : State G) (d : Deal)
    (h : dealProblems s d = []) :
    parseProposalSExp (G.resources.map (·.name)) (proposalToSExp (.deal d)) = .ok (.deal d) :=
  parse_of_print _ _ (readable_of_dealProblems s d h)

/-! ## Examples: the conditions can be met

These use every clause, every effect, every kind of number and test, and every part of a deal, with
each condition checked. -/

/-- The resources of these examples. -/
def exampleRes : List Res := ["ore", "renown"]

/-- A law that pays 3 for each new shaft. -/
def shaftReward : Law :=
  { title := "Shaft reward"
    clauses := [.onBuild "shaft" [.transfer .bank .actor (.lit "renown") (.lit 3)]] }

/-- One law with every clause, every effect, every number and every test. -/
def everyClause : Law :=
  { title := "Every clause"
    clauses :=
      [ .onHarvest [.transfer .actor .treasury .harvested (.div .harvestedAmount 2)]
      , .onBuild "shaft" [.when (.harvestedIs "ore") [.movePiece .each .bank "shaft"]]
      , .onRoundEnd
          [ .forEach (.or (.not (.lt .round .rolled)) (.and (.le (.lit 1) (.points .each)) .yes))
              [ .when (.eq (.count .each "shaft") (.lit 0))
                  [ .transfer .each .treasury (.lit "ore")
                      (.add (.holding .each .harvested) (.sub (.holding .each (.lit "ore"))
                        (.mul (.declared .each (.lit "ore")) (.declared .each .harvested)))) ]
              , .transfer .treasury .each (.lit "ore")
                  (.divBy (.min (.lit 1) (.lit 2)) (.max (.lit 3) (.lit 4))) ] ]
      , .onRoll [.transfer .bank .treasury (.lit "ore")
          (.totalOver .yes (.add (.mostOver .yes (.lit 1)) (.leastOver .yes (.lit 2))))]
      , .now [.forEach .yes [.movePiece .each .bank "shaft"]]
      , .setCost "shaft" [("ore", 2)]
      , .setPoints "shaft" 2
      , .setBankRate 3
      , .setWorth "renown" 1
      , .newPiece { name := "spire", cost := [("ore", 1)], points := 1, placement := .link, yield := 0, limit := 1 }
      , .newPiece { name := "dock", cost := [], points := 0, placement := .spot, yield := 1, limit := 2 }
      , .newPiece { name := "tower", cost := [], points := 0, placement := .upgrade "dock", yield := 1, limit := 2 }
      , .newPiece { name := "flag", cost := [], points := 0, placement := .attach "dock", yield := 1, limit := 2 }
      , .repeal 4
      , .endGame ] }

/-- One deal with every kind of promise. -/
def everyTerm : Deal :=
  { title := "Every term"
    signers := [0, 1]
    rounds := 2
    exitNotice := 1
    deposits := [(0, "ore", 2)]
    terms :=
      [ .everyRound [{ src := 0, dst := .seat 1, res := "ore", amount := 1 }]
      , .onBuild 1 "shaft" [{ src := 1, dst := .treasury, res := "renown", amount := 1 }]
      , .noBuild 0 "shaft" [3, 4]
      , .noTrade 0 2 ] }

example : parseProposalSExp exampleRes (proposalToSExp (.law shaftReward)) = .ok (.law shaftReward) :=
  parse_of_print _ _ (by decide)
example : parseProposalSExp exampleRes (proposalToSExp (.law everyClause)) = .ok (.law everyClause) :=
  parse_of_print _ _ (by decide)
example : parseProposalSExp exampleRes (proposalToSExp (.deal everyTerm)) = .ok (.deal everyTerm) :=
  parse_of_print _ _ (by decide)

/-! ## Examples: a changed law reads as a different law -/

/-- The same law, paying 5. -/
def shaftRewardFive : Law :=
  { title := "Shaft reward"
    clauses := [.onBuild "shaft" [.transfer .bank .actor (.lit "renown") (.lit 5)]] }

/-- The same law with a second clause. -/
def shaftRewardTwice : Law :=
  { shaftReward with clauses := shaftReward.clauses ++ [.setBankRate 3] }

/-- A law that pays 5 does not print the same as one that pays 3, and it does not read as one. -/
example : proposalToSExp (.law shaftRewardFive) ≠ proposalToSExp (.law shaftReward) := by
  intro h
  have := print_injective exampleRes _ _ (by decide) (by decide) h
  simp [shaftRewardFive, shaftReward] at this

example : parseProposalSExp exampleRes (proposalToSExp (.law shaftRewardFive)) ≠ .ok (.law shaftReward) := by
  rw [parse_of_print exampleRes _ (by decide)]
  simp [shaftRewardFive, shaftReward]

/-- A printed law with its second clause dropped reads as the law with one clause. -/
example : parseProposalSExp exampleRes
      (.list [.atom "law", .str "Shaft reward", clauseS (shaftRewardTwice.clauses[0])]) =
    .ok (.law shaftReward) := by
  have := parse_of_print exampleRes (.law shaftReward) (by decide)
  exact this

/-- So that text does not read as the law with two clauses. -/
example : parseProposalSExp exampleRes
      (.list [.atom "law", .str "Shaft reward", clauseS (shaftRewardTwice.clauses[0])]) ≠
    .ok (.law shaftRewardTwice) := by
  have h := parse_of_print exampleRes (.law shaftReward) (by decide)
  have h' : parseProposalSExp exampleRes
      (.list [.atom "law", .str "Shaft reward", clauseS (shaftRewardTwice.clauses[0])]) =
      .ok (.law shaftReward) := h
  rw [h']
  simp [shaftRewardTwice, shaftReward]

-- The same, through the real text.
#guard match parseProposal "(law \"Shaft reward\" (on-build shaft (transfer bank actor renown 5)))" exampleRes with
  | .ok p => proposalToSExp p == proposalToSExp (.law shaftRewardFive) &&
      proposalToSExp p != proposalToSExp (.law shaftReward)
  | .error _ => false
#guard match parseProposal "(law \"Shaft reward\" (on-build shaft (transfer bank actor renown 3)))" exampleRes with
  | .ok p => proposalToSExp p == proposalToSExp (.law shaftReward) &&
      proposalToSExp p != proposalToSExp (.law shaftRewardTwice)
  | .error _ => false

/-! ## Examples: each condition is needed

Without each condition, the theorem would be false. None of these values can come from the parser.
`lawProblems` does not refuse them, and `ServerTests.lean` checks that. So these are gaps between what
the engine accepts and what the text can say. -/

/-- An effect to put inside the others. -/
def anEffect : Effect := .transfer .bank .treasury (.lit "ore") (.lit 1)

/-- A law with this body at the end of a round. -/
def lawWith (b : List Effect) : Law := { title := "T", clauses := [.onRoundEnd b] }

/-- An `if` around a `for-each-player`. The text has no such thing, so it does not read at all. -/
example : (parseProposalSExp exampleRes (proposalToSExp (.law (lawWith [.when .yes [.forEach .yes [anEffect]]])))).toOption.isNone := by
  decide

/-- A `for-each-player` inside a `for-each-player`. -/
example : (parseProposalSExp exampleRes (proposalToSExp (.law (lawWith [.forEach .yes [.forEach .yes [anEffect]]])))).toOption.isNone := by
  decide

/-- An `if` inside an `if`. -/
example : (parseProposalSExp exampleRes (proposalToSExp (.law (lawWith [.when .yes [.when .yes [anEffect]]])))).toOption.isNone := by
  decide

/-- An empty `if` beside another effect. -/
example : (parseProposalSExp exampleRes (proposalToSExp (.law (lawWith [.when .yes [], anEffect])))).toOption.isNone := by
  decide

/-- A resource the game does not have. -/
example : (parseProposalSExp exampleRes (proposalToSExp (.law (lawWith [.transfer .bank .treasury (.lit "gold") (.lit 1)])))).toOption.isNone := by
  decide

/-- A computed division by a plain number comes back as a fixed division. It reads, but as another value,
so a number that was `.divBy` is now `.div`. -/
example : parseProposalSExp exampleRes
      (proposalToSExp (.law (lawWith [.transfer .bank .treasury (.lit "ore") (.divBy (.lit 7) (.lit 2))]))) =
    .ok (.law (lawWith [.transfer .bank .treasury (.lit "ore") (.div (.lit 7) 2)])) := by
  have := parse_of_print exampleRes (.law (lawWith [.transfer .bank .treasury (.lit "ore") (.div (.lit 7) 2)])) (by decide)
  exact this

/-- A resource called `res` comes back as the resource the dice just paid. -/
example : parseProposalSExp ["res"]
      (proposalToSExp (.law (lawWith [.transfer .bank .treasury (.lit "res") (.lit 1)]))) =
    .ok (.law (lawWith [.transfer .bank .treasury .harvested (.lit 1)])) := by
  have := parse_of_print ["res"] (.law (lawWith [.transfer .bank .treasury .harvested (.lit 1)])) (by decide)
  exact this

/-! ## Tests of the text layer

No theorem covers the characters. These only test them, on the laws above that use every part of the
language. -/

/-- This S-expression survives `SExp.render` and `SExp.read`. -/
def survivesText (x : SExp) : Bool :=
  match SExp.read x.render with
  | .ok y => y == x
  | .error _ => false

#guard survivesText (proposalToSExp (.law shaftReward))
#guard survivesText (proposalToSExp (.law everyClause))
#guard survivesText (proposalToSExp (.deal everyTerm))
#guard survivesText (proposalToSExp (.law { shaftReward with title := "A \"quoted\" \\ title\nwith ; (parens)" }))

-- A value that passes `Readable` can still fail in the text, because the theorem does not cover it. A
-- piece name with a space, or one that looks like a number, prints as something else.
#guard !survivesText (proposalToSExp (.law { title := "T", clauses := [.setPoints "two words" 1] }))
#guard !survivesText (proposalToSExp (.law { title := "T", clauses := [.setPoints "12" 1] }))

end Charter.Rules
