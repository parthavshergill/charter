import Charter.Proofs.RenameBasic

/-!
# Renaming: what laws do

A law has no seat in it, so a law means the same thing after a renaming. The seats it acts on come
from its environment, and those are renamed. These lemmas follow the rule language from the bottom
up: numbers, conditions, effects, laws, and then the harvest.
-/

namespace Charter.Renaming

open Charter Charter.Engine

variable (σ : Renaming) {G : GameDef}

/-! ## A law's environment -/

/-- An environment with its two seats renamed. -/
def env (E : LawEnv) : LawEnv :=
  { actor := E.actor.map σ.to, each := E.each.map σ.to, harvested := E.harvested, rolled := E.rolled }

/-- A trigger with its seat renamed. -/
def trigger : Trigger → Trigger
  | .harvest a r n => .harvest (σ.to a) r n
  | .build a k => .build (σ.to a) k
  | .roundEnd => .roundEnd
  | .roll a n => .roll (σ.to a) n

theorem party_account (E : LawEnv) (p : Party) :
    p.account (σ.env E) = (p.account E).map σ.account := by
  cases p <;> simp [Party.account, env, Function.comp_def]

theorem resRef_get (E : LawEnv) (r : ResRef) : r.get (σ.env E) = r.get E := by
  cases r <;> rfl

theorem party_seat (E : LawEnv) (p : Party) : p.seat (σ.env E) = (p.seat E).map σ.to := by
  cases p <;> rfl

theorem trigger_env (t : Trigger) : (σ.trigger t).env = σ.env t.env := by
  cases t <;> rfl

theorem bodyFor_trigger (c : Clause) (t : Trigger) : c.bodyFor (σ.trigger t) = c.bodyFor t := by
  cases c <;> cases t <;> rfl

/-! ## Numbers and conditions -/

/-- A law's number is the same in the renamed game. -/
theorem expr_eval (s : State G) (E : LawEnv) (e : Expr) :
    e.eval (σ.state s) (σ.env E) = e.eval s E := by
  induction e with
  | lit n => rfl
  | harvestedAmount => rfl
  | rolled => rfl
  | holding p r =>
    simp only [Expr.eval, party_account, resRef_get]
    cases p.account E <;> cases r.get E <;> simp [balance_rename]
  | points p =>
    simp only [Expr.eval, party_seat]
    cases p.seat E <;> simp
  | count p k =>
    simp only [Expr.eval, party_seat]
    cases p.seat E <;> simp
  | add a b iha ihb => simp only [Expr.eval, iha, ihb]
  | sub a b iha ihb => simp only [Expr.eval, iha, ihb]
  | mul a b iha ihb => simp only [Expr.eval, iha, ihb]
  | div a n iha => simp only [Expr.eval, iha]
  | min a b iha ihb => simp only [Expr.eval, iha, ihb]
  | max a b iha ihb => simp only [Expr.eval, iha, ihb]

/-- A law's condition is the same in the renamed game. -/
theorem cond_eval (s : State G) (E : LawEnv) (c : Cond) :
    c.eval (σ.state s) (σ.env E) = c.eval s E := by
  induction c with
  | yes => rfl
  | lt a b => simp only [Cond.eval, expr_eval]
  | le a b => simp only [Cond.eval, expr_eval]
  | eq a b => simp only [Cond.eval, expr_eval]
  | and a b iha ihb => simp only [Cond.eval, iha, ihb]
  | or a b iha ihb => simp only [Cond.eval, iha, ihb]
  | not c ih => simp only [Cond.eval, ih]
  | harvestedIs r => rfl

/-! ## Effects and laws -/

theorem env_each (E : LawEnv) (p : Seat) :
    ({ σ.env E with each := some (σ.to p) } : LawEnv) = σ.env { E with each := some p } := rfl

mutual
  /-- An effect's transfers in the renamed game are the renamed transfers. -/
  theorem plan_rename (s : State G) :
      (e : Effect) → (E : LawEnv) →
      Effect.plan (σ.state s) e (σ.env E) = (Effect.plan s e E).map σ.entry
    | .transfer src dst r amount, E => by
        simp only [Effect.plan, party_account, resRef_get, expr_eval]
        cases src.account E <;> cases dst.account E <;> cases r.get E <;> rfl
    | .forEach c body, E => by
        simp only [Effect.plan, state_turnOrder, List.flatMap_map, List.map_flatMap, env_each,
          cond_eval, planAll_rename s body]
        congr 1
        funext p
        split <;> simp
    | .when c body, E => by
        simp only [Effect.plan, cond_eval, planAll_rename s body]
        split <;> simp

  /-- The same, for a list of effects. -/
  theorem planAll_rename (s : State G) :
      (es : List Effect) → (E : LawEnv) →
      Effect.planAll (σ.state s) es (σ.env E) = (Effect.planAll s es E).map σ.entry
    | [], _ => rfl
    | e :: es, E => by
        simp only [Effect.planAll, plan_rename s e E, planAll_rename s es E, List.map_append]
end

theorem law_plan (s : State G) (t : Trigger) (L : Law) :
    Law.plan (σ.state s) (σ.trigger t) L = (Law.plan s t L).map σ.entry := by
  simp only [Law.plan, bodyFor_trigger, trigger_env, planAll_rename, List.map_flatMap]

/-! ## Settling shortfalls -/

theorem filter_moving (es : List Entry) :
    (es.map σ.entry).filter (fun e => e.src != e.dst) =
      (es.filter fun e => e.src != e.dst).map σ.entry := by
  simp [List.filter_map, Function.comp_def]

theorem demand_rename (l : List Entry) (e : Entry) :
    (((l.map σ.entry).filter fun x => x.src == σ.account e.src && x.res == e.res).map
      (·.amount)).sum =
    ((l.filter fun x => x.src == e.src && x.res == e.res).map (·.amount)).sum := by
  simp [List.filter_map, Function.comp_def]

/-- One request after shrinking, as `settle` computes it. -/
def settleOne (s : State G) (moving : List Entry) (e : Entry) : Entry :=
  { e with amount :=
      let demand := ((moving.filter fun x => x.src == e.src && x.res == e.res).map (·.amount)).sum
      let held := s.balance e.src e.res
      if demand ≤ held then e.amount else e.amount * held / demand }

theorem settle_eq (s : State G) (es : List Entry) :
    settle s es =
      ((es.filter fun e => e.src != e.dst).map
        (settleOne s (es.filter fun e => e.src != e.dst))).filter (·.amount != 0) := rfl

theorem settleOne_rename (s : State G) (l : List Entry) (e : Entry) :
    settleOne (σ.state s) (l.map σ.entry) (σ.entry e) = σ.entry (settleOne s l e) := by
  simp only [settleOne, demand_rename, entry_src, entry_res, entry_amount, balance_rename]
  rfl

/-- Settling renamed requests gives the renamed result. -/
theorem settle_rename (s : State G) (es : List Entry) :
    settle (σ.state s) (es.map σ.entry) = (settle s es).map σ.entry := by
  simp only [settle_eq, filter_moving]
  generalize (es.filter fun e => e.src != e.dst) = l
  have : (l.map σ.entry).map (settleOne (σ.state s) (l.map σ.entry)) =
      (l.map (settleOne s l)).map σ.entry := by
    simp [List.map_map, Function.comp_def, settleOne_rename]
  rw [this, List.filter_map]
  rfl

theorem lawEntries_rename (s : State G) (t : Trigger) :
    lawEntries (σ.state s) (σ.trigger t) = (lawEntries s t).map σ.entry := by
  unfold lawEntries
  rw [← settle_rename]
  simp only [law_plan, state_laws, List.map_flatMap]

/-! ## Posting, seen from a state -/

/-- `afterPosting` on renamed entries is the renamed `afterPosting`. -/
theorem afterPosting_rename (s : State G) (es : List Entry) :
    (σ.state s).afterPosting (es.map σ.entry) = σ.state (s.afterPosting es) := by
  simp only [State.afterPosting, state_books, postAll_rename]
  cases s.books.postAll es <;> rfl

/-! ## Harvest -/

theorem baseHarvest_rename (s : State G) (roll : Nat) :
    baseHarvest (σ.state s) roll = (baseHarvest s roll).map σ.entry := by
  unfold baseHarvest
  rw [← settle_rename, List.map_flatMap]
  congr 2
  funext region
  simp only [state_pieces, List.filterMap_map, List.map_filterMap, state_rules]
  congr 1
  funext x
  simp only [Function.comp_def, piece_loc, piece_owner, piece_kind]
  cases x.loc with
  | spot v => dsimp only; split <;> rfl
  | link l => rfl

theorem harvestEntries_rename (s : State G) (roll : Nat) :
    harvestEntries (σ.state s) roll = (harvestEntries s roll).map σ.entry := by
  unfold harvestEntries
  simp only [baseHarvest_rename, afterPosting_rename, List.map_append]
  congr 1
  rw [← settle_rename, List.flatMap_map, List.map_flatMap]
  congr 2
  funext e
  simp only [entry_dst, entry_res, entry_amount, state_laws]
  cases e.dst with
  | player p =>
    simp only [account_player, List.map_flatMap]
    congr 1
    funext x
    exact σ.law_plan _ (.harvest p e.res e.amount) x.2
  | deposit k i => rfl
  | bank => rfl
  | treasury => rfl

end Charter.Renaming
