import Charter.Proofs.Classify

/-!
# When entries post in full

A list of entries posts if no account is asked for more of a resource than it holds, counted over
the whole list, and no entry goes from an account to itself. `settle` makes that true for what laws
ask for, and refunds move each deposit exactly once.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-! ## The harvest always posts -/

theorem baseHarvest_posts (s : State G) (roll : Nat) :
    ∃ b, s.books.postAll (baseHarvest s roll) = some b := settle_posts _ _

theorem harvestEntries_posts (s : State G) (roll : Nat) :
    ∃ b, s.books.postAll (harvestEntries s roll) = some b := by
  obtain ⟨b1, h1⟩ := baseHarvest_posts s roll
  simp only [harvestEntries]
  rw [postAll_append, h1, Option.bind_some]
  have hb := afterPosting_books h1
  have := settle_posts (s.afterPosting (baseHarvest s roll))
    ((baseHarvest s roll).flatMap fun e =>
      match e.dst with
      | .player p => s.laws.flatMap fun x =>
          Law.plan (s.afterPosting (baseHarvest s roll)) (.harvest p e.res e.amount) x.2
      | _ => [])
  rw [hb] at this
  exact this

/-- The whole of a roll always posts: the harvest, then the laws reacting to the roll. -/
theorem rollEntries_posts (s : State G) (roll : Nat) :
    ∃ b, s.books.postAll (rollEntries s roll) = some b := by
  obtain ⟨b1, h1⟩ := harvestEntries_posts s.atRoll roll
  rw [atRoll_books] at h1
  simp only [rollEntries]
  rw [postAll_append, h1, Option.bind_some]
  cases s.nextRoller with
  | none => exact ⟨b1, rfl⟩
  | some a =>
    have := settle_posts (s.atRoll.afterPosting (harvestEntries s.atRoll roll))
      ((s.atRoll.afterPosting (harvestEntries s.atRoll roll)).laws.flatMap fun x =>
        Law.plan (s.atRoll.afterPosting (harvestEntries s.atRoll roll)) (.roll a roll) x.2)
    rw [afterPosting_books (by rw [atRoll_books]; exact h1)] at this
    exact this

/-! ## Refunds always post -/

/-- A valid game names each resource once. -/
theorem nodup_of_eraseDups {α : Type} [BEq α] [LawfulBEq α] (L : List α)
    (h : L.eraseDups.length = L.length) : L.Nodup := by
  have hle : ∀ (n : Nat) (L : List α), L.length ≤ n → L.eraseDups.length ≤ L.length := by
    intro n
    induction n with
    | zero =>
      intro L hL
      cases L with
      | nil => simp
      | cons _ _ => simp at hL
    | succ n ih =>
      intro L hL
      cases L with
      | nil => simp
      | cons a t =>
        rw [List.eraseDups_cons]
        have hf := List.length_filter_le (fun b => !b == a) t
        have := ih (t.filter (fun b => !b == a)) (by simp at hL; omega)
        simp only [List.length_cons]
        omega
  have key : ∀ (n : Nat) (L : List α), L.length ≤ n → L.eraseDups.length = L.length → L.Nodup := by
    intro n
    induction n with
    | zero =>
      intro L hL _
      cases L with
      | nil => simp
      | cons _ _ => simp at hL
    | succ n ih =>
      intro L hL he
      cases L with
      | nil => simp
      | cons a t =>
        rw [List.eraseDups_cons] at he
        simp only [List.length_cons, Nat.add_right_cancel_iff] at he
        have hf := List.length_filter_le (fun b => !b == a) t
        have h1 := hle _ (t.filter (fun b => !b == a)) (Nat.le_refl _)
        have hlen : (t.filter (fun b => !b == a)).length = t.length := by omega
        have hkeep : t.filter (fun b => !b == a) = t := List.filter_eq_self.mpr (by
          intro x hx
          exact List.length_filter_eq_length_iff.mp hlen x hx)
        rw [hkeep] at he
        refine List.nodup_cons.mpr ⟨?_, ih t (by simp at hL; omega) he⟩
        intro hat
        have := List.length_filter_eq_length_iff.mp hlen a hat
        simp at this
  exact key _ L (Nat.le_refl _) h

theorem valid_names (hG : G.Valid) : (G.resources.map (·.name)).Nodup := by
  have hG := valid_shape hG
  simp only [GameDef.shapeChecks, Bool.and_eq_true, beq_iff_eq] at hG
  exact nodup_of_eraseDups _ (by simpa using hG.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2)

theorem filterMap_eq_flatMap {α β : Type} (L : List α) (g : α → Option β) :
    L.filterMap g = L.flatMap fun a => (g a).toList := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filterMap_cons, List.flatMap_cons, ih]
    cases g a <;> simp

/-- One signer's refund from one deal takes at most what the deposit holds. -/
theorem signerRefund_outflow (hG : G.Valid) (s : State G) (d : ActiveDeal) (i : Seat) (a : Account)
    (r : Res) :
    outflow (G.resources.filterMap fun q =>
      let held := s.balance (.deposit d.id i) q.name
      if held = 0 then none
      else some { src := .deposit d.id i, dst := .player i, res := q.name
                  amount := held, reason := .refund }) a r ≤ s.books a r := by
  rw [filterMap_eq_flatMap]
  apply outflow_flatMap_le _ _ (·.name) (valid_names hG)
  · intro q _
    simp only
    split
    · exact Nat.zero_le _
    · simp only [Option.toList_some, outflow_cons, outflow_nil, Nat.add_zero]
      split
      · rename_i hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Nat.le_refl _
      · exact Nat.zero_le _
  · intro q _ q' _ h1 h2
    have name_of : ∀ q : ResourceDef, outflow (Option.toList
        (let held := s.balance (.deposit d.id i) q.name
         if held = 0 then none
         else some { src := .deposit d.id i, dst := .player i, res := q.name
                     amount := held, reason := .refund })) a r ≠ 0 → q.name = r := by
      intro q hq
      obtain ⟨x, hx, _, h3⟩ := exists_of_outflow_ne hq
      simp only at hx
      split at hx
      · cases hx
      · simp only [Option.toList_some, List.mem_singleton] at hx
        subst hx
        exact h3
    exact (name_of q h1).trans (name_of q' h2).symm

/-- A deal's refund takes at most what each deposit holds. -/
theorem refundEntries_outflow (hG : G.Valid) (s : State G) {d : ActiveDeal}
    (hnd : d.deal.signers.Nodup) (a : Account) (r : Res) :
    outflow (s.refundEntries d) a r ≤ s.books a r := by
  unfold State.refundEntries
  apply outflow_flatMap_le _ _ id (by simpa using hnd)
  · intro i _
    exact signerRefund_outflow hG s d i a r
  · intro i _ j _ h1 h2
    have src_of : ∀ i, outflow (G.resources.filterMap fun q =>
        let held := s.balance (.deposit d.id i) q.name
        if held = 0 then none
        else some { src := .deposit d.id i, dst := .player i, res := q.name
                    amount := held, reason := .refund }) a r ≠ 0 → a = .deposit d.id i := by
      intro i hq
      obtain ⟨x, hx, h3, _⟩ := exists_of_outflow_ne hq
      obtain ⟨q, _, hm⟩ := List.mem_filterMap.mp hx
      simp only at hm
      split at hm
      · cases hm
      · simp only [Option.some.injEq] at hm
        subst hm
        exact h3.symm
    have h3 := (src_of i h1).symm.trans (src_of j h2)
    injection h3

/-- Refunds for a list of running deals take at most what each deposit holds. -/
theorem refunds_outflow (hG : G.Valid) (s : State G) (L : List ActiveDeal)
    (hnd : (L.map (·.id)).Nodup) (hsig : ∀ d ∈ L, d.deal.signers.Nodup) (a : Account) (r : Res) :
    outflow (L.flatMap s.refundEntries) a r ≤ s.books a r := by
  apply outflow_flatMap_le _ _ (·.id) hnd
  · intro d hd
    exact refundEntries_outflow hG s (hsig d hd) a r
  · intro d _ d' _ h1 h2
    obtain ⟨x, hx, h3, _⟩ := exists_of_outflow_ne h1
    obtain ⟨y, hy, h4, _⟩ := exists_of_outflow_ne h2
    obtain ⟨_, i, _, h5, _⟩ := refundEntries_form hx
    obtain ⟨_, j, _, h6, _⟩ := refundEntries_form hy
    have h7 : (Account.deposit d.id i) = .deposit d'.id j := by rw [← h5, ← h6, h3, h4]
    injection h7

/-- Refunds always post. -/
theorem refunds_post (hG : G.Valid) (s : State G) (L : List ActiveDeal)
    (hnd : (L.map (·.id)).Nodup) (hsig : ∀ d ∈ L, d.deal.signers.Nodup) :
    ∃ b, s.books.postAll (L.flatMap s.refundEntries) = some b := by
  apply postAll_some
  · intro x hx
    obtain ⟨d, _, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨_, i, _, h1, h2⟩ := refundEntries_form hx
    rw [h1, h2]
    intro h
    cases h
  · exact refunds_outflow hG s L hnd hsig

end Charter.Proofs
