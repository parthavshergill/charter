import Charter.Proofs.Exact

/-!
# What can happen to a seat's pieces

A turn change leaves exactly what the laws say, and no other event but placing a piece changes any. A piece
leaves its owner only for that seat's own upgrade or a law in force, and a seat keeps its last piece.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

theorem step_turn_pieces {s s' : State G} {e : Event} (hend : EndsTurn s e)
    (h : Engine.step G s e = .ok s') : s'.pieces = s.turnPieces (rollAt G s.seed s.rollsMade) := by
  obtain ⟨_, _, rfl⟩ := endTurnNow_ok (step_endTurnNow hend h)
  simp only [startNextTurn_pieces]

theorem body_final_pieces {s1 s' : State G} {e : Event} (hb : finish (countAction s1 (seatOf e)) e = .ok s') :
    s'.pieces = s1.pieces := by
  rcases finish_cases hb with rfl | ⟨w, hw⟩
  · rfl
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    rfl

theorem pieces_kept {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    PiecesKept s s' e := by
  refine ⟨fun hend => step_turn_pieces hend h, fun L hp => ?_,
    fun hnot hne hnl => (step_is_exact h).2.2.2.2.2.2.2.2.2.1 hnot hne hnl⟩
  have hp' := hp
  obtain ⟨seat, id, p, rfl, _⟩ := hp
  obtain ⟨_, s1, hb, hf⟩ := step_act h (by simp [EndsTurn])
  have hv : voteBody s seat id true = .ok s1 := hb
  rcases vote_view hv with ⟨L', hq, hu, hs1⟩ | ⟨hno, _⟩
  · have hL : L = L' := hu L hp'
    subst hL
    rw [body_final_pieces hf, hs1]
    rfl
  · exact absurd hp' (hno L)

/-- A place move's pieces, in either phase. -/
theorem place_pieces {s s1 : State G} {p : Seat} {k : PieceKind} {loc : Loc}
    (h : placeBody s p k loc = .ok s1) : s1.pieces = s.placedPieces p k loc := by
  rcases placeBody_ok h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, rfl⟩ := setupBody_ok h
    rfl
  · obtain ⟨_, _, _, rfl⟩ := buildBody_ok h
    rfl

/-- After a place move, a piece is one of the old ones or the new one, and every old piece stays unless it
was the placer's. -/
theorem placed_keeps {s : State G} {p : Seat} {k : PieceKind} {loc : Loc} {x : Piece} (hx : x ∈ s.pieces)
    (hgone : x ∉ s.placedPieces p k loc) : x.owner = p := by
  unfold State.placedPieces at hgone
  simp only at hgone
  have hkept : x ∉ (match (s.rules.piece? k).map (·.placement), loc with
      | some (.upgrade old), .spot v => s.pieces.erase ⟨p, old, .spot v⟩
      | _, _ => s.pieces) := fun hm => hgone (List.mem_append_left _ hm)
  generalize (s.rules.piece? k).map (·.placement) = pl at hkept
  cases pl with
  | none => exact absurd hx hkept
  | some pl =>
    cases pl with
    | upgrade old =>
      cases loc with
      | spot v =>
        by_cases heq : x = ⟨p, old, .spot v⟩
        · rw [heq]
        · exact absurd ((List.mem_erase_of_ne heq).mpr hx) hkept
      | link l => exact absurd hx hkept
    | link => exact absurd hx hkept
    | spot => exact absurd hx hkept
    | attach j => exact absurd hx hkept

/-! What a turn change's orders ask for comes from a clause of a law in force that can move a piece. -/

mutual
  theorem planOrders_kind {s : State G} : ∀ (e : Effect) (env : LawEnv),
      ∀ o ∈ Effect.planOrders s e env, o.kind ∈ e.kindsMoved
    | .transfer .., _, o, ho => by simp [Effect.planOrders] at ho
    | .movePiece src dst k, env, o, ho => by
      simp only [Effect.planOrders] at ho
      simp only [Effect.kindsMoved, List.mem_singleton]
      split at ho
      · simp only [List.mem_singleton] at ho
        rw [ho]
      · simp only [List.mem_singleton] at ho
        rw [ho]
      · simp at ho
    | .forEach c body, env, o, ho => by
      simp only [Effect.planOrders, List.mem_flatMap] at ho
      obtain ⟨p, _, ho⟩ := ho
      split at ho
      · simp only [Effect.kindsMoved]
        exact planOrdersAll_kind body _ o ho
      · simp at ho
    | .when c body, env, o, ho => by
      simp only [Effect.planOrders] at ho
      split at ho
      · simp only [Effect.kindsMoved]
        exact planOrdersAll_kind body _ o ho
      · simp at ho

  theorem planOrdersAll_kind {s : State G} : ∀ (es : List Effect) (env : LawEnv),
      ∀ o ∈ Effect.planOrdersAll s es env, o.kind ∈ Effect.kindsMovedAll es
    | [], _, o, ho => by simp [Effect.planOrdersAll] at ho
    | e :: es, env, o, ho => by
      simp only [Effect.planOrdersAll, List.mem_append] at ho
      simp only [Effect.kindsMovedAll, List.mem_append]
      cases ho with
      | inl ho => exact Or.inl (planOrders_kind e env o ho)
      | inr ho => exact Or.inr (planOrdersAll_kind es env o ho)
end

theorem bodyFor_effects (c : Clause) (t : Trigger) :
    c.bodyFor t = [] ∨ c.bodyFor t = c.effects := by
  cases c <;> cases t <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (simp only [Clause.bodyFor]; split <;> simp [Clause.effects])

theorem lawOrders_law {s x : State G} {t : Trigger} {o : PieceOrder} (hl : x.laws = s.laws)
    (ho : o ∈ lawOrders x t) : ∃ L ∈ s.laws, L.2.clauses.any Clause.movesPieces = true := by
  simp only [lawOrders, List.mem_flatMap] at ho
  obtain ⟨L, hL, c, hc, ho⟩ := ho
  refine ⟨L, hl ▸ hL, List.any_eq_true.mpr ⟨c, hc, ?_⟩⟩
  rcases bodyFor_effects c t with he | he
  · rw [he] at ho
    simp [Effect.planOrdersAll] at ho
  · rw [he] at ho
    have := planOrdersAll_kind (s := x) c.effects t.env o ho
    simp only [Clause.movesPieces, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    intro hnil
    rw [hnil] at this
    cases this

theorem turnPieces_gone {s : State G} {roll : Nat} {x : Piece} (hx : x ∈ s.pieces)
    (hgone : x ∉ s.turnPieces roll) : ∃ L ∈ s.laws, L.2.clauses.any Clause.movesPieces = true := by
  have hb : x ∈ s.piecesBeforeRoll → x ∉ s.turnPieces roll →
      ∃ L ∈ s.laws, L.2.clauses.any Clause.movesPieces = true := by
    intro hb hg
    unfold State.turnPieces at hg
    simp only at hg
    split at hg
    · split at hg
      · obtain ⟨o, ho, _⟩ := applyOrders_gone (R := s.afterRoundEnd.rules) hb hg
        exact lawOrders_law (by
          show s.afterRoundEnd.atRoll.laws = s.laws
          rw [atRoll_laws]
          rfl) ho
      · exact absurd hb hg
    · exact absurd hb hg
  by_cases h1 : x ∈ s.piecesBeforeRoll
  · exact hb h1 hgone
  · unfold State.piecesBeforeRoll at h1
    split at h1
    · obtain ⟨o, ho, _⟩ := applyOrders_gone hx h1
      exact lawOrders_law (x := s.afterPosting s.duePayments) rfl ho
    · exact absurd hx h1

theorem piece_leaves_only_for {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    PieceLeavesOnlyFor s s' e := by
  intro x hx hgone
  rcases step_view h with ⟨hend, _⟩ | ⟨hnot, _, s1, hb, hf⟩
  · rw [step_turn_pieces hend h] at hgone
    exact Or.inr (Or.inl ⟨hend, turnPieces_gone hx hgone⟩)
  · rw [body_final_pieces hf] at hgone
    cases e with
    | move p m =>
      cases m with
      | place k loc =>
        have := place_pieces hb
        rw [this] at hgone
        have ho := placed_keeps hx hgone
        exact Or.inl ⟨k, loc, by rw [ho]⟩
      | _ =>
        have := body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb
        rw [this] at hgone
        exact absurd hx hgone
    | forceEndTurn => cases hb
    | propose a b =>
      have := body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb
      rw [this] at hgone
      exact absurd hx hgone
    | vote a b c =>
      have hv : voteBody s a b c = .ok s1 := hb
      rcases vote_view hv with ⟨L, hp, hu, hs1⟩ | ⟨_, hk, _⟩
      · have hmoved : L.clauses.any Clause.movesPieces = true := by
          rw [hs1] at hgone
          have hg : x ∉ applyOrders s.rules (s.decreeOrders L) s.pieces := hgone
          obtain ⟨o, ho, _⟩ := applyOrders_gone hx hg
          simp only [State.decreeOrders, List.mem_flatMap] at ho
          obtain ⟨c, hc, ho⟩ := ho
          refine List.any_eq_true.mpr ⟨c, hc, ?_⟩
          rcases bodyFor_effects c .now with he | he
          · rw [he] at ho
            simp [Effect.planOrdersAll] at ho
          · rw [he] at ho
            have := planOrdersAll_kind (s := s) c.effects _ o ho
            simp only [Clause.movesPieces, Bool.not_eq_true', List.isEmpty_eq_false_iff]
            intro hnil
            rw [hnil] at this
            cases this
        exact Or.inr (Or.inr ⟨L, hp, hmoved⟩)
      · rw [hk] at hgone
        exact absurd hx hgone
    | sign a b =>
      have := body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb
      rw [this] at hgone
      exact absurd hx hgone
    | exit a b =>
      have := body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb
      rw [this] at hgone
      exact absurd hx hgone

theorem turnPieces_keeps {s : State G} {roll : Nat} {q : Seat} (h : ∃ x ∈ s.pieces, x.owner = q) :
    ∃ x ∈ s.turnPieces roll, x.owner = q := by
  have h1 : ∃ x ∈ s.piecesBeforeRoll, x.owner = q := by
    unfold State.piecesBeforeRoll
    split
    · exact applyOrders_keeps h
    · exact h
  unfold State.turnPieces
  simp only
  split
  · split
    · exact applyOrders_keeps h1
    · exact h1
  · exact h1

/-- **A law can never take a seat's last piece.** A seat that has a piece still has one after any step. -/
theorem seats_keep_a_piece {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s') :
    SeatsKeepAPiece s s' := by
  intro q hq
  rcases step_view h with ⟨hend, _⟩ | ⟨hnot, _, s1, hb, hf⟩
  · rw [step_turn_pieces hend h]
    exact turnPieces_keeps hq
  · rw [body_final_pieces hf]
    cases e with
    | move p m =>
      cases m with
      | place k loc =>
        rw [place_pieces hb]
        obtain ⟨x, hx, ho⟩ := hq
        by_cases hin : x ∈ s.placedPieces p k loc
        · exact ⟨x, hin, ho⟩
        · have := placed_keeps hx hin
          exact ⟨⟨p, k, loc⟩, by simp [State.placedPieces], by rw [← ho, this]⟩
      | _ =>
        rw [body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb]
        exact hq
    | forceEndTurn => cases hb
    | propose a b =>
      rw [body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb]
      exact hq
    | vote a b c =>
      have hv : voteBody s a b c = .ok s1 := hb
      rcases vote_view hv with ⟨L, _, _, hs1⟩ | ⟨_, hk, _⟩
      · rw [hs1]
        exact applyOrders_keeps hq
      · rw [hk]
        exact hq
    | sign a b =>
      rw [body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb]
      exact hq
    | exit a b =>
      rw [body_pieces (s1 := s1) (by simp) (fun L hl => by obtain ⟨_, _, _, he, _⟩ := hl; cases he) hb]
      exact hq

end Charter.Proofs
