import Charter.Proofs.Basic

/-!
# Posting keeps the total

Posting an entry moves an amount from one account to another. If both accounts are on a list that
has no repeats, the sum over that list does not change.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-- The amount of `r` across the accounts on a list. -/
def sumOver (L : List Account) (b : Books) (r : Res) : Nat := (L.map fun a => b a r).sum

theorem post_some {b b' : Books} {e : Entry} (h : b.post e = some b') :
    e.amount ≤ b e.src e.res ∧ e.src ≠ e.dst ∧
    b' = fun a r =>
      if r = e.res then
        if a = e.src then b a r - e.amount
        else if a = e.dst then b a r + e.amount
        else b a r
      else b a r := by
  unfold Books.post at h
  split at h
  · rename_i hc
    exact ⟨hc.1, hc.2, by simpa using h.symm⟩
  · cases h

theorem postAll_append (b : Books) (xs ys : List Entry) :
    b.postAll (xs ++ ys) = (b.postAll xs).bind fun b' => b'.postAll ys := by
  induction xs generalizing b with
  | nil => simp [Books.postAll]
  | cons x xs ih =>
    simp only [List.cons_append, Books.postAll]
    cases b.post x with
    | none => simp
    | some b' => simpa using ih b'

/-- One posting, counted exactly: what leaves the list on one side comes back on the other. -/
theorem sumOver_post {b b' : Books} {e : Entry} (h : b.post e = some b') (L : List Account)
    (hL : L.Nodup) :
    sumOver L b' e.res + (if e.src ∈ L then e.amount else 0) =
      sumOver L b e.res + (if e.dst ∈ L then e.amount else 0) := by
  obtain ⟨hle, hne, rfl⟩ := post_some h
  induction L with
  | nil => simp [sumOver]
  | cons a t ih =>
    have ih' := ih (List.nodup_cons.mp hL).2
    have hat := (List.nodup_cons.mp hL).1
    simp only [sumOver, List.map_cons, List.sum_cons, List.mem_cons] at ih' ⊢
    by_cases h1 : a = e.src
    · subst h1
      simp [hat, hne.symm] at ih' ⊢
      omega
    · by_cases h2 : a = e.dst
      · subst h2
        have h3 : ¬ e.src = e.dst := hne
        simp [hat, h1, h3] at ih' ⊢
        omega
      · have h3 : ¬ e.src = a := fun x => h1 x.symm
        have h4 : ¬ e.dst = a := fun x => h2 x.symm
        simp [h1, h2, h3, h4] at ih' ⊢
        omega

theorem sumOver_post_same {b b' : Books} {e : Entry} (h : b.post e = some b') (L : List Account)
    (hL : L.Nodup) (hs : e.src ∈ L) (hd : e.dst ∈ L) (r : Res) :
    sumOver L b' r = sumOver L b r := by
  by_cases hr : r = e.res
  · subst hr
    have := sumOver_post h L hL
    simp only [hs, hd, ite_true] at this
    omega
  · obtain ⟨_, _, rfl⟩ := post_some h
    simp [sumOver, hr]

theorem sumOver_postAll {L : List Account} (hL : L.Nodup) {es : List Entry} {b b' : Books}
    (h : b.postAll es = some b') (hes : ∀ x ∈ es, x.src ∈ L ∧ x.dst ∈ L) (r : Res) :
    sumOver L b' r = sumOver L b r := by
  induction es generalizing b with
  | nil =>
    simp only [Books.postAll, Option.some.injEq] at h
    rw [h]
  | cons x xs ih =>
    simp only [Books.postAll] at h
    cases hp : b.post x with
    | none => simp [hp] at h
    | some b1 =>
      rw [hp] at h
      have hx := hes x (by simp)
      rw [ih (by simpa using h) (fun y hy => hes y (by simp [hy])),
        sumOver_post_same hp L hL hx.1 hx.2 r]

/-! ## The accounts of a game -/

/-- This account can exist in a game with these seats. -/
def AcctOk (T : List Seat) : Account → Prop
  | .bank => True
  | .treasury => True
  | .player i => i ∈ T
  | .deposit k i => k < maxDealsPerGame ∧ i ∈ T

/-- Both sides of this entry are accounts of the game. -/
def EntryOk (T : List Seat) (x : Entry) : Prop := AcctOk T x.src ∧ AcctOk T x.dst

theorem mem_accounts (s : State G) (a : Account) : a ∈ s.accounts ↔ AcctOk s.turnOrder a := by
  cases a <;> simp [State.accounts, AcctOk]
  all_goals grind

theorem accounts_nodup (s : State G) (h : s.turnOrder.Nodup) : s.accounts.Nodup := by
  have hmap : ∀ {α : Type} (f : Seat → α), (∀ x y, f x = f y → x = y) → (s.turnOrder.map f).Nodup := by
    intro α f hf
    exact List.Pairwise.map f (fun a b hab he => hab (hf a b he)) h
  have hdep : ((List.range maxDealsPerGame).flatMap fun k => s.turnOrder.map (Account.deposit k)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => hmap _ (by intro x y hxy; simpa using hxy), ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
    intro a b _ _ hab x hx y hy he
    simp only [List.mem_map] at hx hy
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨j, _, rfl⟩ := hy
    simp only [Account.deposit.injEq] at he
    exact hab he.1
  unfold State.accounts
  simp only [List.cons_append, List.nil_append]
  rw [List.nodup_cons, List.nodup_cons, List.nodup_append]
  refine ⟨by simp, by simp, hmap _ (by intro x y hxy; simpa using hxy), hdep, ?_⟩
  intro a ha b hb he
  subst he
  simp only [List.mem_map, List.mem_flatMap] at ha hb
  obtain ⟨_, _, rfl⟩ := ha
  obtain ⟨_, _, _, _, hh⟩ := hb
  cases hh

theorem total_eq_sumOver (s : State G) (r : Res) : s.total r = sumOver s.accounts s.books r := rfl

/-- At the start, all of a resource is in the bank. -/
theorem sumOver_genesis (T : List Seat) (r : Res) :
    sumOver ([.bank, .treasury] ++ T.map .player ++
      (List.range maxDealsPerGame).flatMap fun k => T.map (.deposit k)) (genesisBooks G) r =
      G.stockOf r := by
  have zero : ∀ L : List Account, (∀ a ∈ L, a ≠ .bank) →
      (L.map fun a => genesisBooks G a r).sum = 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a t ih =>
      intro h
      have ha := h a (by simp)
      have := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons, List.sum_cons, this]
      cases a <;> first | exact absurd rfl ha | rfl
  simp only [sumOver, List.cons_append, List.nil_append, List.map_cons, List.sum_cons]
  rw [zero _ (by
    intro a ha he
    subst he
    simp at ha)]
  simp [genesisBooks]

end Charter.Proofs
