import Charter.Words.Turns
import Charter.Words.Fast

/-!
# What a law does

These definitions are the meaning of the rule language. A harvest is what the bank pays when the
dice roll, plus what the laws do in reaction. A whole roll is the harvest, then what the laws do in
reaction to the roll itself.
-/

namespace Charter

/-- What a law is reacting to. -/
inductive Trigger where
  | harvest (actor : Seat) (r : Res) (amount : Nat)
  | build (actor : Seat) (k : PieceKind)
  | roundEnd
  /-- The dice showed `total`. `actor` is the seat whose turn the roll starts. -/
  | roll (actor : Seat) (total : Nat)
  deriving Repr, DecidableEq

/-- Who and what a law can see while it runs. -/
structure LawEnv where
  actor : Option Seat := none
  each : Option Seat := none
  harvested : Option (Res × Nat) := none
  rolled : Option Nat := none

/-- The account this party means here, if it means one here. -/
def Party.account (env : LawEnv) : Party → Option Account
  | .actor => env.actor.map .player
  | .each => env.each.map .player
  | .treasury => some .treasury
  | .bank => some .bank

/-- The resource this name means here, if it means one here. -/
def ResRef.get (env : LawEnv) : ResRef → Option Res
  | .lit r => some r
  | .harvested => env.harvested.map (·.1)

/-- The seat this party means here, if it means one here. -/
def Party.seat (env : LawEnv) : Party → Option Seat
  | .actor => env.actor
  | .each => env.each
  | _ => none

/-- The values of a number over every seat that passes a test, in turn order. `test` and `value` see each
seat as `each`. -/
def measured {G : GameDef} (s : State G) (env : LawEnv) (test : LawEnv → Bool) (value : LawEnv → Nat) :
    List Nat :=
  s.turnOrder.filterMap fun p =>
    let here := { env with each := some p }
    if test here then some (value here) else none

mutual
  /-- The value of a number in this state. -/
  def Expr.eval {G : GameDef} (s : State G) (env : LawEnv) : Expr → Nat
    | .lit n => n
    | .harvestedAmount => (env.harvested.map (·.2)).getD 0
    | .rolled => env.rolled.getD 0
    | .holding p r =>
        match p.account env, r.get env with
        | some a, some x => s.balance a x
        | _, _ => 0
    | .points p => ((p.seat env).map s.pointsOf).getD 0
    | .count p k => ((p.seat env).map fun x => s.countOf x k).getD 0
    | .add a b => a.eval s env + b.eval s env
    | .sub a b => a.eval s env - b.eval s env
    | .mul a b => a.eval s env * b.eval s env
    | .div a n => a.eval s env / n
    | .divBy a b => a.eval s env / b.eval s env
    | .min a b => Nat.min (a.eval s env) (b.eval s env)
    | .max a b => Nat.max (a.eval s env) (b.eval s env)
    | .round => s.round
    | .totalOver c a => (measured s env (fun e => c.eval s e) (fun e => a.eval s e)).sum
    | .mostOver c a => ((measured s env (fun e => c.eval s e) (fun e => a.eval s e)).max?).getD 0
    | .leastOver c a => ((measured s env (fun e => c.eval s e) (fun e => a.eval s e)).min?).getD 0

  /-- The value of a test in this state. -/
  def Cond.eval {G : GameDef} (s : State G) (env : LawEnv) : Cond → Bool
    | .yes => true
    | .lt a b => decide (a.eval s env < b.eval s env)
    | .le a b => decide (a.eval s env ≤ b.eval s env)
    | .eq a b => a.eval s env == b.eval s env
    | .and a b => a.eval s env && b.eval s env
    | .or a b => a.eval s env || b.eval s env
    | .not c => !c.eval s env
    | .harvestedIs r => (env.harvested.map (·.1)) == some r
end

mutual
  /-- The transfers an effect asks for, before any shortfall is settled. -/
  def Effect.plan {G : GameDef} (s : State G) : Effect → LawEnv → List Entry
    | .transfer src dst r amount, env =>
        match src.account env, dst.account env, r.get env with
        | some a, some b, some x =>
            [{ src := a, dst := b, res := x, amount := amount.eval s env, reason := .lawEffect }]
        | _, _, _ => []
    | .forEach c body, env =>
        s.turnOrder.flatMap fun p =>
          let env' := { env with each := some p }
          if c.eval s env' then Effect.planAll s body env' else []
    | .when c body, env => if c.eval s env then Effect.planAll s body env else []

  /-- The transfers a list of effects asks for, in order. -/
  def Effect.planAll {G : GameDef} (s : State G) : List Effect → LawEnv → List Entry
    | [], _ => []
    | e :: es, env => Effect.plan s e env ++ Effect.planAll s es env
end

/-- The bodies of a law that respond to a trigger. -/
def Clause.bodyFor : Clause → Trigger → List Effect
  | .onHarvest b, .harvest .. => b
  | .onBuild k b, .build _ k' => if k == k' then b else []
  | .onRoundEnd b, .roundEnd => b
  | .onRoll b, .roll .. => b
  | _, _ => []

/-- Who and what a law can see when it reacts to this trigger. -/
def Trigger.env : Trigger → LawEnv
  | .harvest a r n => { actor := some a, harvested := some (r, n) }
  | .build a _ => { actor := some a }
  | .roundEnd => {}
  | .roll a n => { actor := some a, rolled := some n }

/-- The transfers one law asks for on this trigger, in clause order. -/
def Law.plan {G : GameDef} (s : State G) (t : Trigger) (L : Law) : List Entry :=
  L.clauses.flatMap fun c => Effect.planAll s (c.bodyFor t) t.env

/-- What every law in force does for a trigger, all planned from the same moment. -/
def lawEntries {G : GameDef} (s : State G) (t : Trigger) : List Entry :=
  settle s (s.laws.flatMap fun x => Law.plan s t x.2)

/-- What the bank pays out for a roll: each piece on a producing region collects its yield.
If the bank is short, everyone's payment shrinks in proportion, and it can round down to nothing. -/
def baseHarvest {G : GameDef} (s : State G) (roll : Nat) : List Entry :=
  settle s ((G.map.regions.filter (·.number == roll)).flatMap fun region =>
    s.pieces.filterMap fun x =>
      match x.loc with
      | .spot v =>
          if region.spots.contains v then
            some { src := .bank, dst := .player x.owner, res := region.res
                   amount := ((s.rules.piece? x.kind).map (·.yield)).getD 0, reason := .harvest }
          else none
      | .link _ => none)

/-- The whole harvest of a roll: the bank's payments, then every law reacting to each payment,
all planned from the moment after the bank paid. -/
def harvestEntries {G : GameDef} (s : State G) (roll : Nat) : List Entry :=
  let base := baseHarvest s roll
  let after := s.afterPosting base
  base ++ settle after (base.flatMap fun e =>
    match e.dst with
    | .player p => s.laws.flatMap fun x => Law.plan after (.harvest p e.res e.amount) x.2
    | _ => [])

/-- The seat whose turn the next roll starts. There is none if no roll comes next. -/
def State.nextRoller {G : GameDef} (s : State G) : Option Seat :=
  match nextStage s with
  | .firstRound | .newRound => s.turnOrder[0]?
  | .sameRound i => s.turnOrder[i]?
  | _ => none

/-- What a roll reads. If the roll starts a new round, the round has already changed. -/
def State.atRoll {G : GameDef} (s : State G) : State G :=
  match nextStage s with
  | .newRound => { s with round := s.round + 1 }
  | _ => s

/-- The whole of a roll: the harvest, then every law reacting to the roll itself, all planned from
the moment after the harvest posted. If no law reacts to a roll, this is the harvest alone. A roll that
starts a new round reads that new round. -/
def rollEntries {G : GameDef} (s : State G) (roll : Nat) : List Entry :=
  let harvest := harvestEntries s.atRoll roll
  harvest ++
    match s.nextRoller with
    | some a => lawEntries (s.atRoll.afterPosting harvest) (.roll a roll)
    | none => []

end Charter
