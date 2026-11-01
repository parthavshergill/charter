import Charter.Proofs.Basic

/-!
# What a law's move does to the pieces

One order at a time, and then a list of orders. The results are about any list of pieces, so later proofs
need only these.
-/

namespace Charter.Proofs

open Charter Charter.Engine

/-- Every piece a move carries has the same owner as the piece it starts from. -/
theorem carriedWith_owner (R : Rules) (ps : List Piece) (x : Piece) :
    ∀ y ∈ carriedWith R ps x, y.owner = x.owner := by
  unfold carriedWith
  have key : ∀ (l acc : List Piece), (∀ y ∈ acc, y.owner = x.owner) →
      ∀ y ∈ l.foldl (fun acc y =>
        if y.owner == x.owner && y.loc == x.loc && !acc.contains y && R.attachesTo y.kind (acc.map (·.kind))
        then acc ++ [y] else acc) acc, y.owner = x.owner := by
    intro l
    induction l with
    | nil => intro acc h; simpa using h
    | cons a t ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        intro y hy
        cases List.mem_append.mp hy with
        | inl hy => exact h y hy
        | inr hy =>
          simp only [List.mem_singleton] at hy
          rw [hy]
          exact hc.1.1.1
      · exact h
  exact key ps [x] (by simp)

/-- A piece that one order takes away was owned by the seat that order names. -/
theorem applyOrder_gone {R : Rules} {ps : List Piece} {o : PieceOrder} {x : Piece}
    (hx : x ∈ ps) (hgone : x ∉ applyOrder R ps o) : x.owner = o.src := by
  unfold applyOrder at hgone
  split at hgone
  · exact absurd hx hgone
  split at hgone
  · exact absurd hx hgone
  · rename_i y hlast
    simp only at hgone
    split at hgone
    · exact absurd hx hgone
    · have hy : y.owner = o.src := by
        have hm := List.mem_of_getLast? hlast
        have := (List.mem_filter.mp hm).2
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        exact this.1
      by_cases hc : (carriedWith R ps y).contains x = true
      · have : x ∈ carriedWith R ps y := by simpa using hc
        rw [carriedWith_owner R ps y x this, hy]
      · exfalso
        apply hgone
        apply List.mem_filterMap.mpr
        have hf : (carriedWith R ps y).contains x = false := by simpa using hc
        exact ⟨x, hx, by simp only [hf, Bool.false_eq_true, ↓reduceIte]⟩

/-- A piece that a list of orders takes away was owned by a seat one of the orders names. -/
theorem applyOrders_gone {R : Rules} {orders : List PieceOrder} {ps : List Piece} {x : Piece}
    (hx : x ∈ ps) (hgone : x ∉ applyOrders R orders ps) : ∃ o ∈ orders, x.owner = o.src := by
  induction orders generalizing ps with
  | nil => exact absurd hx hgone
  | cons o t ih =>
    by_cases h1 : x ∈ applyOrder R ps o
    · obtain ⟨o', ho, h⟩ := ih h1 hgone
      exact ⟨o', by simp [ho], h⟩
    · exact ⟨o, by simp, applyOrder_gone hx h1⟩

/-- One order leaves every seat that has a piece with a piece. -/
theorem applyOrder_keeps {R : Rules} {ps : List Piece} {o : PieceOrder} {q : Seat}
    (h : ∃ x ∈ ps, x.owner = q) : ∃ x ∈ applyOrder R ps o, x.owner = q := by
  obtain ⟨x0, hx0, hq⟩ := h
  unfold applyOrder
  split
  · exact ⟨x0, hx0, hq⟩
  split
  · exact ⟨x0, hx0, hq⟩
  · rename_i y hlast
    simp only
    split
    · exact ⟨x0, hx0, hq⟩
    · rename_i hne
      have hy : y.owner = o.src := by
        have hm := List.mem_of_getLast? hlast
        have := (List.mem_filter.mp hm).2
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        exact this.1
      have stays : ∀ z ∈ ps, (carriedWith R ps y).contains z = false →
          z ∈ ps.filterMap fun w => if (carriedWith R ps y).contains w then landing R ps o.dst w else some w := by
        intro z hz hc
        exact List.mem_filterMap.mpr ⟨z, hz, by simp only [hc, Bool.false_eq_true, ↓reduceIte]⟩
      by_cases hsrc : q = o.src
      · -- The seat that gives keeps what the order does not take, and the check says that is something.
        have hnon : ps.filter (fun w => w.owner == o.src && !(carriedWith R ps y).contains w) ≠ [] := by
          intro he
          rw [he] at hne
          exact hne rfl
        obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hnon
        obtain ⟨hzm, hzc⟩ := List.mem_filter.mp hz
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hzc
        exact ⟨z, stays z hzm hzc.2, by rw [hzc.1, hsrc]⟩
      · -- Any other seat keeps what it had, because a move carries only the giver's pieces.
        have hc : (carriedWith R ps y).contains x0 = false := Bool.eq_false_iff.mpr fun hcon => by
          have hmem : x0 ∈ carriedWith R ps y := by simpa using hcon
          have := carriedWith_owner R ps y x0 hmem
          exact hsrc (by rw [← hq, this, hy])
        exact ⟨x0, stays x0 hx0 hc, hq⟩

/-- A list of orders leaves every seat that has a piece with a piece. -/
theorem applyOrders_keeps {R : Rules} {orders : List PieceOrder} {ps : List Piece} {q : Seat}
    (h : ∃ x ∈ ps, x.owner = q) : ∃ x ∈ applyOrders R orders ps, x.owner = q := by
  induction orders generalizing ps with
  | nil => exact h
  | cons o t ih => exact ih (applyOrder_keeps h)

/-- One order sends a piece only to a seat it names, so every owner is a seat in the game. -/
theorem applyOrder_owner {R : Rules} {T : List Seat} {ps : List Piece} {o : PieceOrder}
    (hps : ∀ x ∈ ps, x.owner ∈ T) (ho : ∀ q, o.dst = some q → q ∈ T) :
    ∀ x ∈ applyOrder R ps o, x.owner ∈ T := by
  unfold applyOrder
  split
  · exact hps
  split
  · exact hps
  · rename_i y _
    simp only
    split
    · exact hps
    · intro x hx
      obtain ⟨z, hz, hf⟩ := List.mem_filterMap.mp hx
      split at hf
      · unfold landing at hf
        split at hf
        · rename_i q hd
          split at hf
          · simp only [Option.some.injEq] at hf
            rw [← hf]
            exact ho q hd
          · cases hf
        · cases hf
      · simp only [Option.some.injEq] at hf
        rw [← hf]
        exact hps z hz

theorem applyOrders_owner {R : Rules} {T : List Seat} {orders : List PieceOrder} {ps : List Piece}
    (hps : ∀ x ∈ ps, x.owner ∈ T) (ho : ∀ o ∈ orders, ∀ q, o.dst = some q → q ∈ T) :
    ∀ x ∈ applyOrders R orders ps, x.owner ∈ T := by
  induction orders generalizing ps with
  | nil => exact hps
  | cons o t ih =>
    exact ih (applyOrder_owner hps (ho o (by simp))) (fun o' h' => ho o' (by simp [h']))

/-- With no orders, nothing moves. -/
theorem applyOrders_nil (R : Rules) (ps : List Piece) : applyOrders R [] ps = ps := rfl

end Charter.Proofs
