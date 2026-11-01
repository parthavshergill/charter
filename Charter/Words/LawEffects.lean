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
  /-- A law just passed. Nobody is the actor. -/
  | now
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
    | .declared p r =>
        match p.seat env, r.get env with
        | some q, some x => s.declared q x
        | _, _ => 0
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

/-- A law asks a seat to give up its newest piece of this kind. `dst = none` means the bank, which destroys
it. -/
structure PieceOrder where
  src : Seat
  dst : Option Seat
  kind : PieceKind
  deriving Repr, DecidableEq

mutual
  /-- The transfers an effect asks for, before any shortfall is settled. -/
  def Effect.plan {G : GameDef} (s : State G) : Effect → LawEnv → List Entry
    | .transfer src dst r amount, env =>
        match src.account env, dst.account env, r.get env with
        | some a, some b, some x =>
            [{ src := a, dst := b, res := x, amount := amount.eval s env, reason := .lawEffect }]
        | _, _, _ => []
    | .movePiece .., _ => []
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

mutual
  /-- The pieces an effect asks to move. -/
  def Effect.planOrders {G : GameDef} (s : State G) : Effect → LawEnv → List PieceOrder
    | .transfer .., _ => []
    | .movePiece src dst k, env =>
        match src.seat env, dst, dst.seat env with
        | some a, .bank, _ => [⟨a, none, k⟩]
        | some a, _, some b => [⟨a, some b, k⟩]
        | _, _, _ => []
    | .forEach c body, env =>
        s.turnOrder.flatMap fun p =>
          let env' := { env with each := some p }
          if c.eval s env' then Effect.planOrdersAll s body env' else []
    | .when c body, env => if c.eval s env then Effect.planOrdersAll s body env else []

  /-- The pieces a list of effects asks to move, in order. -/
  def Effect.planOrdersAll {G : GameDef} (s : State G) : List Effect → LawEnv → List PieceOrder
    | [], _ => []
    | e :: es, env => Effect.planOrders s e env ++ Effect.planOrdersAll s es env
end

/-- The bodies of a law that respond to a trigger. -/
def Clause.bodyFor : Clause → Trigger → List Effect
  | .onHarvest b, .harvest .. => b
  | .onBuild k b, .build _ k' => if k == k' then b else []
  | .onRoundEnd b, .roundEnd => b
  | .onRoll b, .roll .. => b
  | .now b, .now => b
  | _, _ => []

/-- Who and what a law can see when it reacts to this trigger. -/
def Trigger.env : Trigger → LawEnv
  | .harvest a r n => { actor := some a, harvested := some (r, n) }
  | .build a _ => { actor := some a }
  | .roundEnd => {}
  | .roll a n => { actor := some a, rolled := some n }
  | .now => {}

/-- The transfers one law asks for on this trigger, in clause order. -/
def Law.plan {G : GameDef} (s : State G) (t : Trigger) (L : Law) : List Entry :=
  L.clauses.flatMap fun c => Effect.planAll s (c.bodyFor t) t.env

/-- This kind of piece sits on one of these kinds. -/
def Rules.attachesTo (R : Rules) (k : PieceKind) (onto : List PieceKind) : Bool :=
  match ((R.piece? k).map (·.placement) : Option Placement) with
  | some (Placement.attach j) => onto.contains j
  | _ => false

/-- A piece and what sits on it: the same owner's pieces in the same place, attached to it, directly or
through each other. -/
def carriedWith (R : Rules) (ps : List Piece) (x : Piece) : List Piece :=
  ps.foldl (fun acc y =>
    if y.owner == x.owner && y.loc == x.loc && !acc.contains y && R.attachesTo y.kind (acc.map (·.kind))
    then acc ++ [y] else acc) [x]

/-- Where a moved piece ends up. It goes to the seat if that seat is under its limit for that kind, and
is destroyed otherwise. The bank destroys it. -/
def landing (R : Rules) (ps : List Piece) (dst : Option Seat) (y : Piece) : Option Piece :=
  match dst with
  | some q =>
    if (ps.filter fun z => z.owner == q && z.kind == y.kind).length <
        ((R.piece? y.kind).map (·.limit)).getD 0
    then some { y with owner := q } else none
  | none => none

/-- Carry out one order. It takes the seat's newest piece of that kind, and what sits on it. A seat always
keeps its last piece, because a seat with no pieces could never build again. So an order that would take
everything a seat has does nothing. -/
def applyOrder (R : Rules) (ps : List Piece) (o : PieceOrder) : List Piece :=
  if o.dst == some o.src then ps else
  match (ps.filter fun y => y.owner == o.src && y.kind == o.kind).getLast? with
  | none => ps
  | some x =>
    let going := carriedWith R ps x
    if (ps.filter fun y => y.owner == o.src && !going.contains y).isEmpty then ps
    else ps.filterMap fun y => if going.contains y then landing R ps o.dst y else some y

/-- Carry out orders, in order. -/
def applyOrders (R : Rules) (orders : List PieceOrder) (ps : List Piece) : List Piece :=
  orders.foldl (applyOrder R) ps

/-- What every law in force does for a trigger, all planned from the same moment. -/
def lawEntries {G : GameDef} (s : State G) (t : Trigger) : List Entry :=
  settle s (s.laws.flatMap fun x => Law.plan s t x.2)

/-- The pieces every law in force asks to move for a trigger, all planned from the same moment. -/
def lawOrders {G : GameDef} (s : State G) (t : Trigger) : List PieceOrder :=
  s.laws.flatMap fun x => x.2.clauses.flatMap fun c => Effect.planOrdersAll s (c.bodyFor t) t.env

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

/-- What a roll reads. If the roll starts a new round, the round has already changed and the declarations
have cleared. -/
def State.atRoll {G : GameDef} (s : State G) : State G :=
  match nextStage s with
  | .newRound => { s with round := s.round + 1, declared := fun _ _ => 0 }
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
