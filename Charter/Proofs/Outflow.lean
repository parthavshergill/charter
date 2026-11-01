import Charter.Proofs.Books

/-!
# What leaves and enters an account

Counting entries, posting them, and why `settle` never asks an account for more than it holds.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## Counting what leaves and enters an account -/

/-- The total a list of entries takes out of an account. -/
def outflow (es : List Entry) (a : Account) (r : Res) : Nat :=
  ((es.filter fun x => x.src == a && x.res == r).map (·.amount)).sum

/-- The total a list of entries puts in an account. -/
def inflow (es : List Entry) (a : Account) (r : Res) : Nat :=
  ((es.filter fun x => x.dst == a && x.res == r).map (·.amount)).sum

theorem outflow_nil (a : Account) (r : Res) : outflow [] a r = 0 := rfl

theorem outflow_cons (x : Entry) (es : List Entry) (a : Account) (r : Res) :
    outflow (x :: es) a r = (if x.src = a ∧ x.res = r then x.amount else 0) + outflow es a r := by
  simp only [outflow, List.filter_cons, Bool.and_eq_true, beq_iff_eq]
  split <;> simp

theorem inflow_cons (x : Entry) (es : List Entry) (a : Account) (r : Res) :
    inflow (x :: es) a r = (if x.dst = a ∧ x.res = r then x.amount else 0) + inflow es a r := by
  simp only [inflow, List.filter_cons, Bool.and_eq_true, beq_iff_eq]
  split <;> simp

theorem outflow_append (xs ys : List Entry) (a : Account) (r : Res) :
    outflow (xs ++ ys) a r = outflow xs a r + outflow ys a r := by
  simp [outflow, List.filter_append]

theorem inflow_append (xs ys : List Entry) (a : Account) (r : Res) :
    inflow (xs ++ ys) a r = inflow xs a r + inflow ys a r := by
  simp [inflow, List.filter_append]

theorem outflow_eq_zero {es : List Entry} {a : Account} {r : Res}
    (h : ∀ x ∈ es, x.src = a → x.res = r → x.amount = 0) : outflow es a r = 0 := by
  induction es with
  | nil => rfl
  | cons x t ih =>
    rw [outflow_cons, ih (fun y hy => h y (by simp [hy]))]
    split
    · rename_i hc
      simpa using h x (by simp) hc.1 hc.2
    · rfl

theorem outflow_eq_zero' {es : List Entry} {a : Account} {r : Res}
    (h : ∀ x ∈ es, x.src = a → x.res = r → False) : outflow es a r = 0 :=
  outflow_eq_zero fun x hx h1 h2 => (h x hx h1 h2).elim

/-- If anything leaves an account, some entry says so. -/
theorem exists_of_outflow_ne {es : List Entry} {a : Account} {r : Res} (h : outflow es a r ≠ 0) :
    ∃ x ∈ es, x.src = a ∧ x.res = r := by
  by_cases hc : ∃ x ∈ es, x.src = a ∧ x.res = r
  · exact hc
  · exact absurd (outflow_eq_zero' fun x hx h1 h2 => hc ⟨x, hx, h1, h2⟩) h

theorem outflow_flatMap_zero {α : Type} (L : List α) (f : α → List Entry) {a : Account} {r : Res}
    (h : ∀ x ∈ L, outflow (f x) a r = 0) : outflow (L.flatMap f) a r = 0 := by
  induction L with
  | nil => rfl
  | cons x t ih =>
    rw [List.flatMap_cons, outflow_append, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- If at most one member of a list can take from an account, the whole list takes no more than
any one member can. -/
theorem outflow_flatMap_le {α β : Type} (L : List α) (f : α → List Entry) (key : α → β)
    (hnd : (L.map key).Nodup) {a : Account} {r : Res} {c : Nat}
    (h1 : ∀ x ∈ L, outflow (f x) a r ≤ c)
    (h2 : ∀ x ∈ L, ∀ y ∈ L, outflow (f x) a r ≠ 0 → outflow (f y) a r ≠ 0 → key x = key y) :
    outflow (L.flatMap f) a r ≤ c := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons x t ih =>
    rw [List.flatMap_cons, outflow_append]
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    by_cases hx : outflow (f x) a r = 0
    · rw [hx, Nat.zero_add]
      exact ih hnd.2 (fun y hy => h1 y (by simp [hy]))
        (fun u hu v hv => h2 u (by simp [hu]) v (by simp [hv]))
    · have hz : outflow (t.flatMap f) a r = 0 := by
        apply outflow_flatMap_zero
        intro y hy
        by_cases hy0 : outflow (f y) a r = 0
        · exact hy0
        · exact absurd (h2 y (by simp [hy]) x (by simp) hy0 hx) (hnd.1 y hy)
      rw [hz, Nat.add_zero]
      exact h1 x (by simp)

/-! ## Posting -/

theorem post_some_of {b : Books} {x : Entry} (h1 : x.amount ≤ b x.src x.res) (h2 : x.src ≠ x.dst) :
    b.post x = some fun a r =>
      if r = x.res then
        if a = x.src then b a r - x.amount
        else if a = x.dst then b a r + x.amount
        else b a r
      else b a r := by
  unfold Books.post
  rw [ite_eq_left ⟨h1, h2⟩]

/-- Entries post if no account is asked for more than it holds, counted over the whole list. -/
theorem postAll_some {es : List Entry} {b : Books} (h1 : ∀ x ∈ es, x.src ≠ x.dst)
    (h2 : ∀ a r, outflow es a r ≤ b a r) : ∃ b', b.postAll es = some b' := by
  induction es generalizing b with
  | nil => exact ⟨b, rfl⟩
  | cons x t ih =>
    have hx : x.amount ≤ b x.src x.res := by
      have := h2 x.src x.res
      rw [outflow_cons, ite_eq_left ⟨rfl, rfl⟩] at this
      omega
    have hne := h1 x (by simp)
    simp only [Books.postAll]
    rw [post_some_of hx hne]
    simp only [Option.bind_some]
    apply ih (fun y hy => h1 y (by simp [hy]))
    intro a r
    have := h2 a r
    rw [outflow_cons] at this
    by_cases hr : r = x.res
    · by_cases ha : a = x.src
      · simp only [hr, ha, ite_true, and_self] at this ⊢
        omega
      · have hna : ¬ (x.src = a ∧ x.res = r) := fun h => ha h.1.symm
        rw [ite_eq_right hna] at this
        simp only [hr, ha, ite_true, ite_false] at this ⊢
        split <;> omega
    · have hna : ¬ (x.src = a ∧ x.res = r) := fun h => hr h.2.symm
      rw [ite_eq_right hna] at this
      simp only [hr, ite_false]
      omega

/-- What an account holds after posting, exactly. -/
theorem postAll_balance {es : List Entry} {b b' : Books} (h : b.postAll es = some b') (a : Account)
    (r : Res) : b' a r + outflow es a r = b a r + inflow es a r := by
  induction es generalizing b with
  | nil =>
    simp only [Books.postAll, Option.some.injEq] at h
    subst h
    rfl
  | cons x t ih =>
    simp only [Books.postAll] at h
    cases hp : b.post x with
    | none => simp [hp] at h
    | some b1 =>
      rw [hp] at h
      have := ih (by simpa using h)
      obtain ⟨hle, hne, hb1⟩ := post_some hp
      rw [outflow_cons, inflow_cons]
      have hv : b1 a r = if r = x.res then
          if a = x.src then b a r - x.amount
          else if a = x.dst then b a r + x.amount
          else b a r
        else b a r := by rw [hb1]
      by_cases hr : r = x.res
      · by_cases h1 : a = x.src
        · have e1 : b1 a r = b a r - x.amount := by rw [hv]; simp [hr, h1]
          have e2 : (if x.src = a ∧ x.res = r then x.amount else 0) = x.amount := by simp [hr, h1]
          have e3 : (if x.dst = a ∧ x.res = r then x.amount else 0) = 0 := by
            simp [h1, hne.symm]
          have hle' : x.amount ≤ b a r := by rw [h1, hr]; exact hle
          omega
        · have e2 : (if x.src = a ∧ x.res = r then x.amount else 0) = 0 := by
            have : ¬ x.src = a := fun e => h1 e.symm
            simp [this]
          by_cases h2 : a = x.dst
          · have e1 : b1 a r = b a r + x.amount := by rw [hv]; simp [hr, h2, hne.symm]
            have e3 : (if x.dst = a ∧ x.res = r then x.amount else 0) = x.amount := by simp [hr, h2]
            omega
          · have e1 : b1 a r = b a r := by rw [hv]; simp [hr, h1, h2]
            have e3 : (if x.dst = a ∧ x.res = r then x.amount else 0) = 0 := by
              have : ¬ x.dst = a := fun e => h2 e.symm
              simp [this]
            omega
      · have e1 : b1 a r = b a r := by rw [hv]; simp [hr]
        have hr' : ¬ x.res = r := fun e => hr e.symm
        have e2 : (if x.src = a ∧ x.res = r then x.amount else 0) = 0 := by simp [hr']
        have e3 : (if x.dst = a ∧ x.res = r then x.amount else 0) = 0 := by simp [hr']
        omega

theorem afterPosting_books {s : State G} {es : List Entry} {b : Books}
    (h : s.books.postAll es = some b) : (s.afterPosting es).books = b := by
  simp [State.afterPosting, h]

/-! ## `settle` never overdraws -/

theorem settle_ne {s : State G} {es : List Entry} {x : Entry} (hx : x ∈ settle s es) :
    x.src ≠ x.dst := by
  simp only [settle, List.mem_filter, List.mem_map] at hx
  obtain ⟨⟨e, ⟨_, h⟩, rfl⟩, _⟩ := hx
  simpa using h

theorem sum_scale_le (L : List Entry) (h D : Nat) :
    (L.map fun e => e.amount * h / D).sum * D ≤ (L.map (·.amount)).sum * h := by
  induction L with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    have := Nat.div_mul_le_self (x.amount * h) D
    omega

/-- Dropping entries that move nothing does not change what leaves an account. -/
theorem outflow_filter_nonzero (es : List Entry) (a : Account) (r : Res) :
    outflow (es.filter (·.amount != 0)) a r = outflow es a r := by
  induction es with
  | nil => rfl
  | cons x t ih =>
    rw [List.filter_cons]
    split
    · rw [outflow_cons, outflow_cons, ih]
    · rename_i hz
      rw [outflow_cons, ih]
      have : x.amount = 0 := by simpa using hz
      simp [this]

/-- What a list of entries takes from an account, when their amounts have been changed. -/
theorem outflow_map_amount (L : List Entry) (g : Entry → Nat) (a : Account) (r : Res) :
    outflow (L.map fun e => { e with amount := g e }) a r =
      ((L.filter fun x => x.src == a && x.res == r).map g).sum := by
  induction L with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, outflow_cons, ih, List.filter_cons, Bool.and_eq_true, beq_iff_eq]
    split <;> simp

/-- `settle` never asks an account for more than it holds. -/
theorem settle_outflow (s : State G) (es : List Entry) (a : Account) (r : Res) :
    outflow (settle s es) a r ≤ s.books a r := by
  simp only [settle]
  rw [outflow_filter_nonzero, outflow_map_amount]
  generalize es.filter (fun e => e.src != e.dst) = moving
  generalize hM : moving.filter (fun x => x.src == a && x.res == r) = M
  have hmem : ∀ e ∈ M, e.src = a ∧ e.res = r := by
    intro e he
    rw [← hM] at he
    simpa using (List.mem_filter.mp he).2
  by_cases hle : (M.map (·.amount)).sum ≤ s.books a r
  · refine Nat.le_trans (Nat.le_of_eq (congrArg List.sum (List.map_congr_left ?_))) hle
    intro e he
    obtain ⟨h1, h2⟩ := hmem e he
    simp only [h1, h2, hM, State.balance, hle, ↓reduceIte]
  · have hpos : 0 < (M.map (·.amount)).sum := by omega
    have hs := sum_scale_le M (s.books a r) (M.map (·.amount)).sum
    rw [Nat.mul_comm (M.map (·.amount)).sum] at hs
    refine Nat.le_trans (Nat.le_of_eq (congrArg List.sum (List.map_congr_left ?_)))
      (Nat.le_of_mul_le_mul_right hs hpos)
    intro e he
    obtain ⟨h1, h2⟩ := hmem e he
    simp only [h1, h2, hM, State.balance, hle, ↓reduceIte]

theorem settle_posts (s : State G) (es : List Entry) :
    ∃ b, s.books.postAll (settle s es) = some b :=
  postAll_some (fun _ hx => settle_ne hx) (settle_outflow s es)

end Charter.Proofs
