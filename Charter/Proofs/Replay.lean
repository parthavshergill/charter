import Charter.Proofs.Majority

/-!
# What you vote on is what runs

The entries of a turn change depend only on some fields of the state. So the preview shown at a vote
is exact. A round's end and a roll write exactly what the rules say.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## What the rule language reads -/

/-- Two states look the same to a law. -/
structure Agree (s t : State G) : Prop where
  turnOrder : s.turnOrder = t.turnOrder
  books : s.books = t.books
  pieces : s.pieces = t.pieces
  laws : s.laws = t.laws
  round : s.round = t.round
  declared : s.declared = t.declared

theorem Agree.pointsOf {s t : State G} (h : Agree s t) (q : Seat) : s.pointsOf q = t.pointsOf q :=
  pointsOf_congr h.pieces h.laws h.books q

theorem Agree.countOf {s t : State G} (h : Agree s t) (q : Seat) (k : PieceKind) :
    s.countOf q k = t.countOf q k := by
  simp only [State.countOf, h.pieces]

theorem measured_congr {s t : State G} (h : Agree s t) (env : LawEnv) (test : LawEnv → Bool)
    (value : LawEnv → Nat) : measured s env test value = measured t env test value := by
  simp only [measured, h.turnOrder]

mutual
  theorem expr_congr {s t : State G} (h : Agree s t) : ∀ (x : Expr) (env : LawEnv),
      x.eval s env = x.eval t env
    | .lit _, _ => by simp only [Expr.eval]
    | .harvestedAmount, _ => rfl
    | .rolled, _ => rfl
    | .holding p r, env => by
      simp only [Expr.eval, State.balance, h.books]
    | .points p, env => by
      simp only [Expr.eval]
      cases p.seat env with
      | none => rfl
      | some q => simp [h.pointsOf]
    | .count p k, env => by
      simp only [Expr.eval]
      cases p.seat env with
      | none => rfl
      | some q => simp [h.countOf]
    | .add a b, env => by simp only [Expr.eval, expr_congr h a, expr_congr h b]
    | .sub a b, env => by simp only [Expr.eval, expr_congr h a, expr_congr h b]
    | .mul a b, env => by simp only [Expr.eval, expr_congr h a, expr_congr h b]
    | .div a n, env => by simp only [Expr.eval, expr_congr h a]
    | .divBy a b, env => by simp only [Expr.eval, expr_congr h a, expr_congr h b]
    | .min a b, env => by simp only [Expr.eval, expr_congr h a, expr_congr h b]
    | .max a b, env => by simp only [Expr.eval, expr_congr h a, expr_congr h b]
    | .round, _ => by simp only [Expr.eval, h.round]
    | .declared p r, env => by simp only [Expr.eval, h.declared]
    | .totalOver c a, env => by
      simp only [Expr.eval, measured_congr h, cond_congr h c, expr_congr h a]
    | .mostOver c a, env => by
      simp only [Expr.eval, measured_congr h, cond_congr h c, expr_congr h a]
    | .leastOver c a, env => by
      simp only [Expr.eval, measured_congr h, cond_congr h c, expr_congr h a]

  theorem cond_congr {s t : State G} (h : Agree s t) : ∀ (c : Cond) (env : LawEnv),
      c.eval s env = c.eval t env
    | .yes, _ => rfl
    | .lt a b, env => by simp only [Cond.eval, expr_congr h a, expr_congr h b]
    | .le a b, env => by simp only [Cond.eval, expr_congr h a, expr_congr h b]
    | .eq a b, env => by simp only [Cond.eval, expr_congr h a, expr_congr h b]
    | .and a b, env => by simp only [Cond.eval, cond_congr h a, cond_congr h b]
    | .or a b, env => by simp only [Cond.eval, cond_congr h a, cond_congr h b]
    | .not c, env => by simp only [Cond.eval, cond_congr h c]
    | .harvestedIs _, _ => rfl
end

mutual
  theorem plan_congr {s t : State G} (h : Agree s t) : ∀ (e : Effect) (env : LawEnv),
      Effect.plan s e env = Effect.plan t e env
    | .transfer src dst r amount, env => by
      simp only [Effect.plan, expr_congr h amount]
    | .movePiece .., _ => rfl
    | .forEach c body, env => by
      simp only [Effect.plan, h.turnOrder]
      congr 1
      funext p
      simp only [cond_congr h c, planAll_congr h body]
    | .when c body, env => by
      simp only [Effect.plan, cond_congr h c, planAll_congr h body]

  theorem planAll_congr {s t : State G} (h : Agree s t) : ∀ (es : List Effect) (env : LawEnv),
      Effect.planAll s es env = Effect.planAll t es env
    | [], _ => rfl
    | e :: es, env => by
      simp only [Effect.planAll, plan_congr h e, planAll_congr h es]
end

theorem lawPlan_congr {s t : State G} (h : Agree s t) (tr : Trigger) (L : Law) :
    Law.plan s tr L = Law.plan t tr L := by
  simp only [Law.plan, planAll_congr h]

theorem settle_congr {s t : State G} (h : s.books = t.books) (es : List Entry) :
    settle s es = settle t es := by
  simp only [settle, State.balance, h]
  rfl

theorem lawEntries_congr {s t : State G} (h : Agree s t) (tr : Trigger) :
    lawEntries s tr = lawEntries t tr := by
  simp only [lawEntries, h.laws, lawPlan_congr h]
  exact settle_congr h.books _

theorem Agree.afterPosting {s t : State G} (h : Agree s t) (es : List Entry) :
    Agree (s.afterPosting es) (t.afterPosting es) :=
  ⟨h.turnOrder, by simp only [State.afterPosting, h.books], h.pieces, h.laws, h.round, h.declared⟩

theorem baseHarvest_congr {s t : State G} (h : Agree s t) (roll : Nat) :
    baseHarvest s roll = baseHarvest t roll := by
  have hr : s.rules = t.rules := by simp only [State.rules, h.laws]
  simp only [baseHarvest, h.pieces, hr]
  exact settle_congr h.books _

theorem harvestEntries_congr {s t : State G} (h : Agree s t) (roll : Nat) :
    harvestEntries s roll = harvestEntries t roll := by
  have hb := baseHarvest_congr h roll
  have ha := h.afterPosting (baseHarvest t roll)
  simp only [harvestEntries, hb, h.laws]
  congr 1
  have : (s.afterPosting (baseHarvest t roll)).books = (t.afterPosting (baseHarvest t roll)).books :=
    ha.books
  rw [settle_congr this]
  congr 1
  simp only [lawPlan_congr ha]

/-! ## What a turn change reads -/

/-- Two states look the same to a turn change. -/
structure TurnAgree (s t : State G) : Prop extends Agree s t where
  phase : s.phase = t.phase
  turnIndex : s.turnIndex = t.turnIndex
  turnsTaken : s.turnsTaken = t.turnsTaken
  deals : s.deals = t.deals
  builtThisRound : s.builtThisRound = t.builtThisRound

theorem TurnAgree.nextStage {s t : State G} (h : TurnAgree s t) :
    Charter.nextStage s = Charter.nextStage t := by
  simp only [Charter.nextStage, State.isLastTurn, h.phase, h.turnIndex, h.turnsTaken, h.round,
    h.turnOrder]
  rfl

theorem TurnAgree.afterPosting {s t : State G} (h : TurnAgree s t) (es : List Entry) :
    TurnAgree (s.afterPosting es) (t.afterPosting es) :=
  { toAgree := h.toAgree.afterPosting es, phase := h.phase, turnIndex := h.turnIndex,
    turnsTaken := h.turnsTaken, deals := h.deals,
    builtThisRound := h.builtThisRound }

theorem TurnAgree.nextRoller {s t : State G} (h : TurnAgree s t) : s.nextRoller = t.nextRoller := by
  simp only [State.nextRoller, h.nextStage, h.turnOrder]

theorem TurnAgree.atRoll {s t : State G} (h : TurnAgree s t) : Agree s.atRoll t.atRoll := by
  simp only [State.atRoll, h.nextStage]
  split
  · exact ⟨h.turnOrder, h.books, h.pieces, h.laws, by simp only [h.round], rfl⟩
  · exact h.toAgree

/-- The whole of a roll is the same in two states that agree on what a turn change reads. -/
theorem rollEntries_congr {s t : State G} (h : TurnAgree s t) (roll : Nat) :
    rollEntries s roll = rollEntries t roll := by
  simp only [rollEntries, harvestEntries_congr h.atRoll, h.nextRoller]
  congr 1
  cases t.nextRoller with
  | none => rfl
  | some a => exact lawEntries_congr (h.atRoll.afterPosting _) _

theorem TurnAgree.duePayments {s t : State G} (h : TurnAgree s t) :
    s.duePayments = t.duePayments := by
  have hb : ∀ d, s.buildsSeenBy d = t.buildsSeenBy d := by
    intro d
    simp only [State.buildsSeenBy, h.round, h.builtThisRound]
  simp only [State.duePayments, h.deals, hb]

theorem TurnAgree.roundEndLawEntries {s t : State G} (h : TurnAgree s t) :
    s.roundEndLawEntries = t.roundEndLawEntries := by
  simp only [State.roundEndLawEntries, h.duePayments]
  exact lawEntries_congr (h.toAgree.afterPosting _) _

theorem TurnAgree.closingDeals {s t : State G} (h : TurnAgree s t) :
    s.closingDeals = t.closingDeals := by
  simp only [State.closingDeals, h.round, h.deals]

theorem TurnAgree.roundEndEntries {s t : State G} (h : TurnAgree s t) :
    s.roundEndEntries = t.roundEndEntries := by
  simp only [State.roundEndEntries, h.duePayments, h.roundEndLawEntries, h.closingDeals]
  congr 2
  funext d
  exact refundEntries_congr (h.toAgree.afterPosting _).books d

theorem TurnAgree.entriesBeforeRoll {s t : State G} (h : TurnAgree s t) :
    s.entriesBeforeRoll = t.entriesBeforeRoll := by
  simp only [State.entriesBeforeRoll, State.isLastTurn, h.phase, h.turnIndex, h.turnOrder,
    h.roundEndEntries]
  rfl

mutual
  theorem planOrders_congr {s t : State G} (h : Agree s t) : ∀ (e : Effect) (env : LawEnv),
      Effect.planOrders s e env = Effect.planOrders t e env
    | .transfer .., _ => rfl
    | .movePiece .., _ => rfl
    | .forEach c body, env => by
      simp only [Effect.planOrders, h.turnOrder]
      congr 1
      funext p
      simp only [cond_congr h c, planOrdersAll_congr h body]
    | .when c body, env => by
      simp only [Effect.planOrders, cond_congr h c, planOrdersAll_congr h body]

  theorem planOrdersAll_congr {s t : State G} (h : Agree s t) : ∀ (es : List Effect) (env : LawEnv),
      Effect.planOrdersAll s es env = Effect.planOrdersAll t es env
    | [], _ => rfl
    | e :: es, env => by
      simp only [Effect.planOrdersAll, planOrders_congr h e, planOrdersAll_congr h es]
end

theorem lawOrders_congr {s t : State G} (h : Agree s t) (tr : Trigger) :
    lawOrders s tr = lawOrders t tr := by
  simp only [lawOrders, h.laws, planOrdersAll_congr h]

theorem TurnAgree.piecesBeforeRoll {s t : State G} (h : TurnAgree s t) :
    s.piecesBeforeRoll = t.piecesBeforeRoll := by
  have hr : s.rules = t.rules := by simp only [State.rules, h.laws]
  have hl : s.isLastTurn = t.isLastTurn := by
    simp only [State.isLastTurn, h.phase, h.turnIndex, h.turnOrder]
  have ho : lawOrders (s.afterPosting s.duePayments) .roundEnd =
      lawOrders (t.afterPosting t.duePayments) .roundEnd := by
    rw [h.duePayments]
    exact lawOrders_congr (h.toAgree.afterPosting _) _
  simp only [State.piecesBeforeRoll, hl, ho, hr, h.pieces]

/-- On a turn that does not end a round, the round's end changes nothing. -/
theorem afterRoundEnd_not_last {s : State G} (hl : s.isLastTurn = false) : s.afterRoundEnd = s := by
  simp [State.afterRoundEnd, State.entriesBeforeRoll, State.piecesBeforeRoll, hl, State.afterPosting,
    Books.postAll]

theorem TurnAgree.afterRoundEnd {s t : State G} (h : TurnAgree s t) :
    TurnAgree s.afterRoundEnd t.afterRoundEnd :=
  let a := h.afterPosting s.entriesBeforeRoll
  { toAgree := ⟨a.turnOrder, by
      simp only [State.afterRoundEnd]
      rw [h.entriesBeforeRoll]
      have := (h.afterPosting t.entriesBeforeRoll).books
      exact this, h.piecesBeforeRoll, a.laws, a.round, a.declared⟩
    phase := h.phase, turnIndex := h.turnIndex, turnsTaken := h.turnsTaken, deals := h.deals,
    builtThisRound := h.builtThisRound }

/-- A turn change writes the same entries in two states that agree on what it reads. -/
theorem turnEntries_congr {s t : State G} (h : TurnAgree s t) (roll : Nat) :
    turnEntries s roll = turnEntries t roll := by
  simp only [turnEntries, h.nextStage, h.entriesBeforeRoll]
  split
  · rw [rollEntries_congr h.afterRoundEnd]
  · rfl

/-! ## Rolls -/

theorem turnEntries_rolls {s : State G} (h : (nextStage s).rolls = true) (roll : Nat) :
    turnEntries s roll = s.entriesBeforeRoll ++
      rollEntries s.afterRoundEnd roll := by
  simp only [turnEntries, h, ↓reduceIte]

theorem turnEntries_no_roll {s : State G} (h : (nextStage s).rolls = false) (roll : Nat) :
    turnEntries s roll = s.entriesBeforeRoll := by
  simp only [turnEntries, h]
  rfl

theorem startNextTurn_rolled {s : State G} (h : (nextStage s).rolls = true) (roll : Nat) :
    (startNextTurn s roll).rollsMade = s.rollsMade + 1 ∧
    (startNextTurn s roll).lastRoll = some roll := by
  unfold startNextTurn
  split
  · rename_i he
    rw [he] at h
    cases h
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · rename_i he
    rw [he] at h
    cases h

theorem startNextTurn_not_rolled {s : State G} (h : (nextStage s).rolls = false) (roll : Nat) :
    (startNextTurn s roll).rollsMade = s.rollsMade := by
  unfold startNextTurn
  split
  · rfl
  · rename_i he
    rw [he] at h
    cases h
  · rename_i he
    rw [he] at h
    cases h
  · rename_i he
    rw [he] at h
    cases h
  · rfl

/-- If the roll counter moved, the turn change rolled. -/
theorem rolls_of_counter {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') (hc : s'.rollsMade = s.rollsMade + 1) :
    (nextStage s).rolls = true := by
  obtain ⟨b, _, hs⟩ := step_endsTurn hend h
  cases hr : (nextStage s).rolls with
  | true => rfl
  | false =>
    have := startNextTurn_not_rolled (s := { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade), pieces := s.turnPieces (rollAt G s.seed s.rollsMade) })
      hr (rollAt G s.seed s.rollsMade)
    rw [← hs] at this
    change s'.rollsMade = s.rollsMade at this
    omega

/-- If the roll counter stayed, the turn change did not roll. -/
theorem no_roll_of_counter {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') (hc : s'.rollsMade = s.rollsMade) :
    (nextStage s).rolls = false := by
  obtain ⟨b, _, hs⟩ := step_endsTurn hend h
  cases hr : (nextStage s).rolls with
  | false => rfl
  | true =>
    have := (startNextTurn_rolled (s := { s with books := b, journal := s.journal ++ turnEntries s (rollAt G s.seed s.rollsMade), pieces := s.turnPieces (rollAt G s.seed s.rollsMade) })
      hr (rollAt G s.seed s.rollsMade)).1
    rw [← hs] at this
    change s'.rollsMade = s.rollsMade + 1 at this
    omega

theorem afterPosting_nil (s : State G) : s.afterPosting [] = s := rfl

/-- A clause that is not an `onRoll` clause has no body for a roll. -/
theorem bodyFor_roll {c : Clause} (h : ∀ b, c ≠ .onRoll b) (a : Seat) (n : Nat) :
    c.bodyFor (.roll a n) = [] := by
  cases c with
  | onRoll b => exact absurd rfl (h b)
  | _ => rfl

/-- With no `onRoll` law in force, the whole of a roll is the harvest alone. So a saved game with no
such law replays as it always did. -/
theorem rollEntries_no_roll_law (s : State G) (roll : Nat)
    (h : ∀ x ∈ s.laws, ∀ c ∈ x.2.clauses, ∀ b, c ≠ .onRoll b) :
    rollEntries s roll = harvestEntries s.atRoll roll := by
  have hlaw : ∀ (a : Seat) (t : State G), t.laws = s.laws → lawEntries t (.roll a roll) = [] := by
    intro a t ht
    have hplan : t.laws.flatMap (fun x => Law.plan t (.roll a roll) x.2) = [] := by
      rw [ht]
      apply List.flatMap_eq_nil_iff.mpr
      intro x hx
      apply List.flatMap_eq_nil_iff.mpr
      intro c hc
      rw [bodyFor_roll (h x hx c hc)]
      rfl
    simp only [lawEntries, hplan]
    rfl
  simp only [rollEntries]
  cases s.nextRoller with
  | none => simp
  | some a =>
    simp only
    rw [hlaw a (s.atRoll.afterPosting (harvestEntries s.atRoll roll)) (atRoll_laws s),
      List.append_nil]

/-! ## Commandment X, parts (c), (d), (e) -/

/-- X(c): deals pay first, then the laws do what the rule language says. -/
theorem round_end_prefix {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hend : EndsTurn s e) (hl : s.isLastTurn = true) :
    (s.duePayments ++ lawEntries (s.afterPosting s.duePayments) .roundEnd) <+: newEntries s s' := by
  rw [newEntries_endTurn hend h]
  obtain ⟨H, hT, _⟩ := turnEntries_last hl (rollAt G s.seed s.rollsMade)
  rw [hT, ← List.append_assoc]
  exact List.prefix_append _ _

/-- The turn that a roll starts belongs to the seat the laws saw as the actor. -/
theorem startNextTurn_currentSeat {s : State G} (h : (nextStage s).rolls = true) (roll : Nat) :
    (startNextTurn s roll).currentSeat = s.nextRoller := by
  unfold startNextTurn State.nextRoller
  cases he : nextStage s with
  | setupTurn i => rw [he] at h; cases h
  | firstRound => rfl
  | sameRound i => rfl
  | newRound => rfl
  | gameOver => rw [he] at h; cases h

/-- X(d): a new turn rolls, and the entries are the whole of that roll. -/
theorem roll_entries {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hend : EndsTurn s e) (hc : s'.rollsMade = s.rollsMade + 1) :
    (s.isLastTurn = false →
      newEntries s s' = rollEntries s (rollAt G s.seed s.rollsMade)) ∧
    (s.isLastTurn = true →
      newEntries s s' = s.roundEndEntries ++
        rollEntries s.afterRoundEnd (rollAt G s.seed s.rollsMade)) ∧
    s.nextRoller = s'.currentSeat := by
  have hr := rolls_of_counter hend h hc
  refine ⟨?_, ?_, ?_⟩
  · intro hl
    have hb : s.entriesBeforeRoll = [] := by simp [State.entriesBeforeRoll, hl]
    rw [newEntries_endTurn hend h, turnEntries_rolls hr, hb, afterRoundEnd_not_last hl]
    rfl
  · intro hl
    have hb : s.entriesBeforeRoll = s.roundEndEntries := by simp [State.entriesBeforeRoll, hl]
    rw [newEntries_endTurn hend h, turnEntries_rolls hr, hb]
  · obtain ⟨b, _, hs⟩ := step_endsTurn hend h
    rw [hs, startNextTurn_currentSeat (s := { s with books := b, journal := _, pieces := _ }) hr]
    rfl

/-- X(e): a turn change with no roll writes only the round-end entries, if any. -/
theorem no_roll_entries {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hend : EndsTurn s e) (hc : s'.rollsMade = s.rollsMade) :
    newEntries s s' = s.entriesBeforeRoll := by
  rw [newEntries_endTurn hend h, turnEntries_no_roll (no_roll_of_counter hend h hc)]

/-! ## Commandment X(b): the preview is exact -/

theorem vote_fields {s s1 : State G} {seat id : Nat} {yes : Bool}
    (hb : voteBody s seat id yes = .ok s1) :
    s1.books = s.books ∧ s1.pieces = s.pieces ∧ s1.deals = s.deals ∧
    s1.builtThisRound = s.builtThisRound := by
  obtain ⟨_, _, L, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := voteBody_ok hb
  · unfold decideLaw
    simp only
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem preview_exact {s s1 s2 : State G} {seat id : Nat} {L : Law} {roll : Nat} {e : Event}
    (h1 : Engine.step G s (.vote seat id true) = .ok s1) (hl : s1.laws = enact s.laws id L)
    (hend : EndsTurn s1 e) (h2 : Engine.step G s1 e = .ok s2) (hr : s2.lastRoll = some roll) :
    newEntries s1 s2 = Engine.predictNextTurn G (s.withLaw id L) roll := by
  have hne1 := step_not_ended h2
  obtain ⟨_, sb, hb, hf⟩ := step_act h1 (by simp [EndsTurn])
  have hs1 : s1 = countAction sb seat := by
    rcases finish_cases hf with h | ⟨w, hw⟩
    · exact h
    · obtain ⟨_, _, h3⟩ := endGame_ok hw
      exact absurd (by rw [h3]) hne1
  have hb' : voteBody s seat id true = .ok sb := hb
  obtain ⟨f1, f2, f3, f4⟩ := vote_fields hb'
  have fr := bodyOf_frame hb
  have hagree : TurnAgree s1 (s.withLaw id L) := by
    rw [hs1] at hl ⊢
    exact ⟨⟨fr.turnOrder, f1, f2, hl, fr.round, by
      have hd := bodyOf_declared hb (by simp)
      exact hd⟩, fr.phase, fr.turnIndex, fr.turnsTaken, f3, f4⟩
  have hroll : turnEntries s1 (rollAt G s1.seed s1.rollsMade) = turnEntries s1 roll := by
    cases hrs : (nextStage s1).rolls with
    | false => rw [turnEntries_no_roll hrs, turnEntries_no_roll hrs]
    | true =>
      obtain ⟨b, _, hs2⟩ := step_endsTurn hend h2
      have := (startNextTurn_rolled (s := { s1 with books := b, journal := s1.journal ++ turnEntries s1 (rollAt G s1.seed s1.rollsMade), pieces := s1.turnPieces (rollAt G s1.seed s1.rollsMade) })
        hrs (rollAt G s1.seed s1.rollsMade)).2
      rw [← hs2, hr] at this
      injection this with h3
      rw [h3]
  rw [newEntries_endTurn hend h2, hroll, turnEntries_congr hagree]
  rfl

/-! ## Commandment X(a): replaying events -/

/-- A property every accepted event keeps holds after any list of events. -/
theorem foldlM_step_induct {P : State G → Prop}
    (hP : ∀ s e s', P s → Engine.step G s e = .ok s' → P s') :
    ∀ (events : List Event) (s0 s : State G), P s0 → events.foldlM (Engine.step G) s0 = .ok s → P s := by
  intro events
  induction events with
  | nil =>
    intro s0 s h0 h
    simp only [List.foldlM_nil] at h
    cases h
    exact h0
  | cons e t ih =>
    intro s0 s h0 h
    simp only [List.foldlM_cons] at h
    cases hs : Engine.step G s0 e with
    | error m =>
      rw [hs] at h
      cases h
    | ok s1 =>
      rw [hs] at h
      exact ih s1 s (hP _ _ _ h0 hs) h

/-- An accepted replay had a legal game and ran every event from the start. -/
theorem replay_ok {seats : Nat} {seed : UInt64} {nonces : List UInt64} {events : List Event}
    {s : State G} (h : replay G seats seed nonces events = .ok s) :
    minSeats ≤ seats ∧ seats ≤ maxSeats ∧ nonces ≠ [] ∧
      events.foldlM (Engine.step G) (initialState G seats seed nonces) = .ok s := by
  unfold replay at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or,
    Decidable.not_not] at h1
  exact ⟨h1.1, h1.2, by simpa using h2, h⟩

theorem replay_of {seats : Nat} {seed : UInt64} {nonces : List UInt64} {events : List Event}
    {s : State G} (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats) (h3 : nonces ≠ [])
    (h : events.foldlM (Engine.step G) (initialState G seats seed nonces) = .ok s) :
    replay G seats seed nonces events = .ok s := by
  have hc : (!(decide (minSeats ≤ seats) && decide (seats ≤ maxSeats))) = false := by
    simp [h1, h2]
  have he : nonces.isEmpty = false := by simpa using h3
  unfold replay
  simp only [hc, he, Bool.false_eq_true, ↓reduceIte]
  exact h

/-- One more event at the end of a list runs after the rest. -/
theorem replay_snoc {seats : Nat} {seed : UInt64} {nonces : List UInt64} {events : List Event}
    {s s' : State G} {e : Event} (h1 : replay G seats seed nonces events = .ok s)
    (h2 : Engine.step G s e = .ok s') : replay G seats seed nonces (events ++ [e]) = .ok s' := by
  obtain ⟨a, b, c, d⟩ := replay_ok h1
  apply replay_of a b c
  rw [List.foldlM_append, d]
  simp only [bind, Except.bind, List.foldlM_cons, List.foldlM_nil, h2]
  rfl

end Charter.Proofs
