import Std.Data.HashMap.Lemmas
import Charter.Words.State

/-!
# Faster code for two definitions

`settle` and `State.afterPosting` say what they mean in the plainest way, and that is slow: `settle` adds
up its requests once per request, and each entry posted to the books makes every later read one step
longer. The limits in `Words/Game.lean` could not be raised with that code.

Each `@[csimp]` theorem here proves that a faster function equals the plain one, for every input, and
tells the compiler to run the faster one. Proofs and promises still read the plain definitions, so a
reader of the constitution can skip this file. `Engine.record` uses `Books.table` in the same way.
-/

namespace Charter

/-- A request from an account to itself moves nothing, so it is dropped and does not count.
If an account is asked for more than it holds, each request from it shrinks in proportion,
rounding down. Requests that shrink to zero vanish, so a shortfall can round down to nobody being
paid, even if the account holds something. Nothing depends on who asked first. -/
def settle {G : GameDef} (s : State G) (es : List Entry) : List Entry :=
  let moving := es.filter fun e => e.src != e.dst
  (moving.map fun e =>
    let demand := ((moving.filter fun x => x.src == e.src && x.res == e.res).map (·.amount)).sum
    let held := s.balance e.src e.res
    { e with amount := if demand ≤ held then e.amount else e.amount * held / demand }).filter
    (·.amount != 0)

deriving instance Hashable for Account

/-! ## `settle` -/

/-- The total asked of each account in each resource. -/
def demandTable (es : List Entry) : Std.HashMap (Account × Res) Nat :=
  es.foldl (fun m e => m.insert (e.src, e.res) (m.getD (e.src, e.res) 0 + e.amount)) {}

private theorem demand_fold (es : List Entry) (m : Std.HashMap (Account × Res) Nat) (k : Account × Res) :
    (es.foldl (fun m e => m.insert (e.src, e.res) (m.getD (e.src, e.res) 0 + e.amount)) m).getD k 0 =
      m.getD k 0 + ((es.filter fun x => x.src == k.1 && x.res == k.2).map (·.amount)).sum := by
  induction es generalizing m with
  | nil => simp
  | cons e es ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getD_insert]
    obtain ⟨a, r⟩ := k
    by_cases h : e.src = a ∧ e.res = r
    · obtain ⟨rfl, rfl⟩ := h
      simp [Nat.add_assoc]
    · have h1 : ((e.src, e.res) == (a, r)) = false := by simpa using h
      have h2 : (e.src == a && e.res == r) = false := by simpa using h
      simp [h1, h2]

theorem demandTable_getD (es : List Entry) (k : Account × Res) :
    (demandTable es).getD k 0 = ((es.filter fun x => x.src == k.1 && x.res == k.2).map (·.amount)).sum := by
  simpa [demandTable] using demand_fold es {} k

/-- `settle`, adding up each account's requests once. -/
def settleFast {G : GameDef} (s : State G) (es : List Entry) : List Entry :=
  let moving := es.filter fun e => e.src != e.dst
  let table := demandTable moving
  (moving.map fun e =>
    let demand := table.getD (e.src, e.res) 0
    let held := s.balance e.src e.res
    { e with amount := if demand ≤ held then e.amount else e.amount * held / demand }).filter
    (·.amount != 0)

@[csimp] theorem settle_eq_settleFast : @settle = @settleFast := by
  funext G s es
  simp only [settle, settleFast, demandTable_getD]

/-! ## Points -/

/-- `State.pointsOf`, working out the rules in force once and not once per piece. -/
def State.pointsOfFast {G : GameDef} (s : State G) (p : Seat) : Nat :=
  let R := s.rules
  ((s.pieces.filter (·.owner == p)).map fun x => ((R.piece? x.kind).map (·.points)).getD 0).sum

@[csimp] theorem pointsOf_eq_fast : @State.pointsOf = @State.pointsOfFast := rfl

/-! ## The books -/

/-- What these books hold in each of these places. -/
def Books.table (b : Books) (keys : List (Account × Res)) : Std.HashMap (Account × Res) Nat :=
  keys.foldl (fun m k => m.insert k (b k.1 k.2)) {}

private theorem table_fold (b : Books) (keys : List (Account × Res))
    (m : Std.HashMap (Account × Res) Nat) (hm : ∀ (k : Account × Res) v, m[k]? = some v → v = b k.1 k.2) :
    ∀ (k : Account × Res) v, (keys.foldl (fun m k => m.insert k (b k.1 k.2)) m)[k]? = some v → v = b k.1 k.2 := by
  induction keys generalizing m with
  | nil => simpa using hm
  | cons x xs ih =>
    refine ih _ ?_
    intro k v hv
    dsimp only at hv
    rw [Std.HashMap.getElem?_insert] at hv
    split at hv
    · rename_i hx
      have : x = k := by simpa using hx
      subst this
      simp only [Option.some.injEq] at hv
      exact hv.symm
    · exact hm k v hv

/-- The same books, read from a table where the table has the answer. -/
def Books.ofTable (t : Std.HashMap (Account × Res) Nat) (b : Books) : Books := fun a r =>
  match t[(a, r)]? with
  | some v => v
  | none => b a r

/-- Reading from a table of these books gives what the books give. -/
theorem Books.ofTable_table (b : Books) (keys : List (Account × Res)) :
    Books.ofTable (b.table keys) b = b := by
  funext a r
  simp only [Books.ofTable]
  split
  · rename_i v hv
    exact table_fold b keys {} (by simp) (a, r) v hv
  · rfl

/-- The places a game reads often: the bank, the treasury, every seat and every running deal's deposits,
in each of the game's resources. -/
def State.tableKeys {G : GameDef} (s : State G) : List (Account × Res) :=
  let accounts : List Account :=
    [.bank, .treasury] ++ s.turnOrder.map .player ++
      s.deals.flatMap fun d => d.deal.signers.map (.deposit d.id)
  accounts.flatMap fun a => G.resources.map fun r => (a, r.name)

/-- One entry, as `Books.post` would post it, written into a table over these books. -/
def Books.postToTable (b : Books) (t : Std.HashMap (Account × Res) Nat) (e : Entry) :
    Option (Std.HashMap (Account × Res) Nat) :=
  let from_ := Books.ofTable t b e.src e.res
  if e.amount ≤ from_ ∧ e.src ≠ e.dst then
    let to_ := Books.ofTable t b e.dst e.res
    some ((t.insert (e.src, e.res) (from_ - e.amount)).insert (e.dst, e.res) (to_ + e.amount))
  else none

theorem Books.ofTable_insert (b : Books) (t : Std.HashMap (Account × Res) Nat) (k : Account × Res)
    (v : Nat) (a : Account) (r : Res) :
    Books.ofTable (t.insert k v) b a r = if k = (a, r) then v else Books.ofTable t b a r := by
  unfold Books.ofTable
  rw [Std.HashMap.getElem?_insert]
  by_cases h : k = (a, r)
  · simp [h]
  · have : (k == (a, r)) = false := by simpa using h
    simp [h, this]

theorem Books.post_ofTable (b : Books) (t : Std.HashMap (Account × Res) Nat) (e : Entry) :
    (Books.ofTable t b).post e = (b.postToTable t e).map (Books.ofTable · b) := by
  unfold Books.post Books.postToTable
  by_cases h : e.amount ≤ Books.ofTable t b e.src e.res ∧ e.src ≠ e.dst
  · simp only [eq_true h, ↓reduceIte, Option.map_some, Option.some.injEq]
    funext a r
    obtain ⟨_, hne⟩ := h
    simp only [Books.ofTable_insert, Prod.mk.injEq]
    by_cases hr : r = e.res
    · subst hr
      by_cases ha : a = e.src
      · subst ha
        have h1 : ¬ e.dst = e.src := fun x => hne x.symm
        simp [h1]
      · by_cases hd : a = e.dst
        · subst hd
          simp [ha]
        · have h1 : ¬ e.dst = a := fun x => hd x.symm
          have h2 : ¬ e.src = a := fun x => ha x.symm
          simp [h1, h2, ha, hd]
    · have h1 : ¬ e.res = r := fun x => hr x.symm
      simp [h1, hr]
  · simp [h]

/-- Post entries into a table over these books, so that a long list stays one step for later reads. -/
def Books.postAllToTable (b : Books) (t : Std.HashMap (Account × Res) Nat) :
    List Entry → Option (Std.HashMap (Account × Res) Nat)
  | [] => some t
  | e :: es => (b.postToTable t e).bind fun t' => Books.postAllToTable b t' es

theorem Books.postAll_ofTable (b : Books) (t : Std.HashMap (Account × Res) Nat) (es : List Entry) :
    (Books.ofTable t b).postAll es = (b.postAllToTable t es).map (Books.ofTable · b) := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    simp only [Books.postAll, Books.postAllToTable, Books.post_ofTable]
    cases b.postToTable t e with
    | none => rfl
    | some t' => simpa using ih t'

/-- `Books.postAll` with the entries written into one table. -/
def Books.postAllFast (b : Books) (es : List Entry) : Option Books :=
  match es with
  | [] => some b
  | _ => (b.postAllToTable {} es).map (Books.ofTable · b)

@[csimp] theorem postAll_eq_fast : @Books.postAll = @Books.postAllFast := by
  funext b es
  simp only [Books.postAllFast]
  split
  · rfl
  · have : Books.ofTable {} b = b := by
      funext a r
      simp [Books.ofTable]
    rw [← Books.postAll_ofTable, this]

/-- `State.afterPosting`, keeping a table of the result, so that reads do not walk back through what was
posted. -/
def State.afterPostingFast {G : GameDef} (s : State G) (es : List Entry) : State G :=
  match es with
  | [] => s
  | _ =>
    let b := (s.books.postAll es).getD s.books
    let t := b.table s.tableKeys
    { s with books := Books.ofTable t b }

@[csimp] theorem afterPosting_eq_fast : @State.afterPosting = @State.afterPostingFast := by
  funext G s es
  simp only [State.afterPostingFast, State.afterPosting]
  split
  · simp [Books.postAll]
  · simp only [Books.ofTable_table]

end Charter
