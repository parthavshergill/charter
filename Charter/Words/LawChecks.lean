import Charter.Words.LawEffects

/-!
# Which laws can pass

A law must pass these checks when it is proposed, and again at the vote that decides it. A law's
`title` is free text. It has no meaning in the game, and no check reads it.
-/

namespace Charter

mutual
  /-- How many nodes a number has. -/
  def Expr.size : Expr → Nat
    | .add a b | .sub a b | .mul a b | .min a b | .max a b | .divBy a b => a.size + b.size + 1
    | .div a _ => a.size + 1
    | .totalOver c a | .mostOver c a | .leastOver c a => c.size + a.size + 1
    | _ => 1

  /-- How many nodes a condition has. -/
  def Cond.size : Cond → Nat
    | .lt a b | .le a b | .eq a b => a.size + b.size + 1
    | .and a b | .or a b => a.size + b.size + 1
    | .not c => c.size + 1
    | _ => 1
end

mutual
  /-- How many nodes an effect has, counting its numbers and conditions. -/
  def Effect.size : Effect → Nat
    | .transfer _ _ _ amount => amount.size + 1
    | .movePiece .. => 1
    | .forEach c body => c.size + Effect.sizeAll body + 1
    | .when c body => c.size + Effect.sizeAll body + 1

  /-- How many nodes a list of effects has. -/
  def Effect.sizeAll : List Effect → Nat
    | [] => 0
    | e :: es => e.size + Effect.sizeAll es
end

/-- The effects inside a clause. -/
def Clause.effects : Clause → List Effect
  | .onHarvest b | .onBuild _ b | .onRoundEnd b | .onRoll b => b
  | _ => []

/-- How many nodes a clause has. -/
def Clause.size (c : Clause) : Nat := Effect.sizeAll c.effects + 1

/-- How many nodes a law has. A law bigger than `maxLawSize` cannot pass. -/
def Law.size (L : Law) : Nat := (L.clauses.map Clause.size).sum

/-- The piece names this law defines. -/
def Law.definedPieces (L : Law) : List PieceKind :=
  L.clauses.filterMap fun
    | .newPiece p => some p.name
    | _ => none

/-- This piece kind exists now, or this law defines it. -/
def State.knownKind {G : GameDef} (s : State G) (L : Law) (k : PieceKind) : Bool :=
  (s.rules.piece? k).isSome || L.definedPieces.contains k

/-- Why one clause cannot pass. -/
def clauseProblems {G : GameDef} (s : State G) (L : Law) : Clause → List String
  | .onHarvest _ => []
  | .onRoundEnd _ => []
  | .onRoll _ => []
  | .onBuild k _ => if s.knownKind L k then [] else [s!"there is no piece named {k}"]
  | .setCost k b =>
      (if s.knownKind L k then [] else [s!"there is no piece named {k}"]) ++
      (if G.bundleOk b then [] else ["a cost must name real resources, each once"])
  | .setPoints k _ => if s.knownKind L k then [] else [s!"there is no piece named {k}"]
  | .setBankRate n => if 2 ≤ n then [] else ["the bank rate must be at least 2"]
  | .setWorth r _ => if G.isRes r then [] else [s!"there is no resource called {r}"]
  | .newPiece p =>
      (if (s.rules.piece? p.name).isSome then [s!"the piece {p.name} already exists"] else []) ++
      (if G.bundleOk p.cost then [] else ["a cost must name real resources, each once"]) ++
      (match p.placement with
       | .upgrade k | .attach k =>
           if s.knownKind L k then [] else [s!"there is no piece named {k}"]
       | _ => [])
  | .repeal n =>
      if s.laws.any (·.1 == n) then [] else [s!"law {n} is not in force"]

mutual
  /-- The most entries an effect can ask for, when every condition is true. -/
  def Effect.plannedEntries (seats : Nat) : Effect → Nat
    | .transfer .. => 1
    | .movePiece .. => 1
    | .forEach _ body => seats * Effect.plannedAll seats body
    | .when _ body => Effect.plannedAll seats body

  /-- The most entries a list of effects can ask for. -/
  def Effect.plannedAll (seats : Nat) : List Effect → Nat
    | [] => 0
    | e :: es => e.plannedEntries seats + Effect.plannedAll seats es
end

/-- The most entries a law can ask for on one trigger, counting all its clauses. -/
def Law.plannedEntries (L : Law) (seats : Nat) : Nat :=
  (L.clauses.map fun c => Effect.plannedAll seats c.effects).sum

/-- The most entries a list of laws can ask for together on one trigger. -/
def plannedTotal (laws : List (Nat × Law)) (seats : Nat) : Nat :=
  (laws.map fun x => x.2.plannedEntries seats).sum

mutual
  /-- How many numbers and tests this number reads when it runs. A measure reads what is inside it once
  per seat. -/
  def Expr.reads (seats : Nat) : Expr → Nat
    | .add a b | .sub a b | .mul a b | .min a b | .max a b | .divBy a b =>
        a.reads seats + b.reads seats + 1
    | .div a _ => a.reads seats + 1
    | .totalOver c a | .mostOver c a | .leastOver c a => seats * (c.reads seats + a.reads seats) + 1
    | _ => 1

  /-- How many numbers and tests this test reads when it runs. -/
  def Cond.reads (seats : Nat) : Cond → Nat
    | .lt a b | .le a b | .eq a b => a.reads seats + b.reads seats + 1
    | .and a b | .or a b => a.reads seats + b.reads seats + 1
    | .not c => c.reads seats + 1
    | _ => 1
end

mutual
  /-- How many numbers and tests an effect reads when it runs, when every condition is true. A
  `forEach` reads what is inside it once per seat. -/
  def Effect.reads (seats : Nat) : Effect → Nat
    | .transfer _ _ _ amount => amount.reads seats + 1
    | .movePiece .. => 1
    | .forEach c body => seats * (c.reads seats + Effect.readsAll seats body) + 1
    | .when c body => c.reads seats + Effect.readsAll seats body + 1

  /-- How many numbers and tests a list of effects reads. -/
  def Effect.readsAll (seats : Nat) : List Effect → Nat
    | [] => 0
    | e :: es => e.reads seats + Effect.readsAll seats es
end

/-- How many numbers and tests a law reads on one trigger, counting all its clauses. -/
def Law.reads (L : Law) (seats : Nat) : Nat :=
  (L.clauses.map fun c => Effect.readsAll seats c.effects).sum

/-- How many numbers and tests a list of laws reads together on one trigger. -/
def readsTotal (laws : List (Nat × Law)) (seats : Nat) : Nat :=
  (laws.map fun x => x.2.reads seats).sum

mutual
  /-- This number divides by zero somewhere, in its own words. A computed number that turns out to be
  zero is not caught here: dividing by it gives 0. -/
  def Expr.dividesByZero : Expr → Bool
    | .add a b | .sub a b | .mul a b | .min a b | .max a b => a.dividesByZero || b.dividesByZero
    | .div a n => n == 0 || a.dividesByZero
    | .divBy a b => b == .lit 0 || a.dividesByZero || b.dividesByZero
    | .totalOver c a | .mostOver c a | .leastOver c a => c.dividesByZero || a.dividesByZero
    | _ => false

  /-- This condition divides by zero somewhere, in its own words. -/
  def Cond.dividesByZero : Cond → Bool
    | .lt a b | .le a b | .eq a b => a.dividesByZero || b.dividesByZero
    | .and a b | .or a b => a.dividesByZero || b.dividesByZero
    | .not c => c.dividesByZero
    | _ => false
end

mutual
  /-- Why an effect is wrong where it runs. `env` says who and what exists there. A transfer that
  names a missing party, or the same party twice, can never move anything. Transfers between two
  different parties that may turn out to be one seat are allowed, and `settle` drops them. -/
  def Effect.problems (env : LawEnv) : Effect → List String
    | .transfer src dst r amount =>
        (if (src.account env).isNone || (dst.account env).isNone || (r.get env).isNone
         then ["a transfer names someone or something that does not exist where this rule runs"]
         else []) ++
        (if src == dst then ["a transfer from an account to itself moves nothing"] else []) ++
        (if amount.dividesByZero then ["a law cannot divide by zero"] else [])
    | .movePiece src dst _ =>
        (if (src.seat env).isNone then ["a piece can be moved only from a seat where this rule runs"] else []) ++
        (if dst == .bank || (dst.seat env).isSome then [] else ["a piece can go only to the bank or a seat"]) ++
        (if src == dst then ["a move from a seat to itself moves nothing"] else [])
    | .forEach c body =>
        (if c.dividesByZero then ["a law cannot divide by zero"] else []) ++
        Effect.problemsAll { env with each := some 0 } body
    | .when c body =>
        (if c.dividesByZero then ["a law cannot divide by zero"] else []) ++
        Effect.problemsAll env body

  /-- Why a list of effects is wrong where it runs. -/
  def Effect.problemsAll (env : LawEnv) : List Effect → List String
    | [] => []
    | e :: es => Effect.problems env e ++ Effect.problemsAll env es
end

mutual
  /-- The kinds of piece this effect moves. -/
  def Effect.kindsMoved : Effect → List PieceKind
    | .transfer .. => []
    | .movePiece _ _ k => [k]
    | .forEach _ body | .when _ body => Effect.kindsMovedAll body

  /-- The kinds of piece these effects move. -/
  def Effect.kindsMovedAll : List Effect → List PieceKind
    | [] => []
    | e :: es => e.kindsMoved ++ Effect.kindsMovedAll es
end

/-- This clause can move a piece. -/
def Clause.movesPieces (c : Clause) : Bool := !(Effect.kindsMovedAll c.effects).isEmpty

/-- Who and what exists where this clause's effects run. -/
def Clause.env : Clause → LawEnv
  | .onHarvest _ => (Trigger.harvest 0 "" 0).env
  | .onBuild k _ => (Trigger.build 0 k).env
  | .onRoll _ => (Trigger.roll 0 0).env
  | _ => {}

/-- Why a clause would do nothing, or is wrong where it runs. `R` is the rules at the moment this
clause applies, and `final` is the rules after the whole law applies. -/
def Clause.noEffect (G : GameDef) (R final : Rules) (c : Clause) : List String :=
  Effect.problemsAll c.env c.effects ++
  (match c with
   | .onHarvest b | .onBuild _ b =>
     if (Effect.kindsMovedAll b).isEmpty then []
     else ["a law can move a piece only at a round's end or on a roll"]
   | _ => []) ++
  ((Effect.kindsMovedAll c.effects).flatMap fun k =>
    if (final.piece? k).isSome then [] else [s!"no piece named {k} will exist"]) ++
  match c with
  | .onHarvest b | .onRoundEnd b | .onRoll b =>
      if Effect.plannedAll 2 b == 0 then ["this rule has no effects"] else []
  | .onBuild k b =>
      (if Effect.plannedAll 2 b == 0 then ["this rule has no effects"] else []) ++
      (if (final.piece? k).isSome then [] else [s!"no piece named {k} will exist"])
  | .setCost k _ | .setPoints k _ =>
      if (R.piece? k).isSome then [] else [s!"the piece {k} does not exist when this clause applies"]
  | .newPiece p =>
      if G.canBuild final.pieces p then [] else [s!"the piece {p.name} could never be built"]
  | _ => []

/-- Run `Clause.noEffect` on each clause in order, with the rules as they stand at that clause. -/
def Clause.noEffectAll (G : GameDef) (final : Rules) : Rules → List Clause → List String
  | _, [] => []
  | R, c :: cs => c.noEffect G R final ++ Clause.noEffectAll G final (c.applyTo R) cs

/-- The rule a clause sets, if it sets one. A later clause that sets the same rule replaces it. -/
def Clause.ruleSet : Clause → Option String
  | .setCost k _ => some s!"cost of {k}"
  | .setPoints k _ => some s!"points of {k}"
  | .setBankRate _ => some "bank rate"
  | .setWorth r _ => some s!"worth of {r}"
  | _ => none

/-- Why a law cannot pass in this state. An empty list means it can. -/
def lawProblems (G : GameDef) (s : State G) (L : Law) : List String :=
  (if L.clauses.isEmpty then ["a law needs at least one clause"] else []) ++
  (if L.size ≤ maxLawSize then [] else ["this law is too big"]) ++
  (if L.plannedEntries s.turnOrder.length ≤ maxPlannedEntries then []
   else ["this law could make too many payments at once"]) ++
  (if plannedTotal (enact s.laws 0 L) s.turnOrder.length ≤ maxPlannedTotal then []
   else ["the laws in force could make too many payments at once"]) ++
  (if readsTotal (enact s.laws 0 L) s.turnOrder.length ≤ maxReadsTotal then []
   else ["the laws in force would read too many numbers at once"]) ++
  (if decide (L.clauses.filterMap Clause.ruleSet).Nodup then []
   else ["this law sets the same rule twice, so the first would do nothing"]) ++
  (if decide L.repeals.Nodup then [] else ["this law repeals a law twice"]) ++
  Clause.noEffectAll G (rulesFrom G (enact s.laws 0 L)) (rulesFrom G (enact s.laws 0 L).dropLast)
    L.clauses ++
  (if (enact s.laws 0 L).length ≤ maxLawsInForce then [] else ["too many laws are in force"]) ++
  (if decide L.definedPieces.Nodup then [] else ["this law defines a piece twice"]) ++
  (if (rulesFrom G (enact s.laws 0 L)).pieces.length ≤ maxPieceKinds then []
   else ["there would be too many kinds of piece"]) ++
  L.clauses.flatMap (clauseProblems s L)

end Charter
