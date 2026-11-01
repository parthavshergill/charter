import Server.MoveJson
import Server.Spec

/-!
# The bot's policy

A bot is a function from a game state to the events it would like, best first. The engine has the final
word on every event. This file needs only the engine and the game list, so the arena and evolved
strategies can import it without the constitution or the proofs. `Server/Bots.lean` joins it to the
server's tables.

The policy is simple. On its own turn a bot places where the dice pay most, upgrades, builds, trades with
the bank to complete a build, and ends its turn. It votes yes on a law when the law would not cost it
resources on the next turn change and hands no other seat the win. It signs a deal that pays it at least
what it pays, and it accepts an offer that gives it at least what it gives. A good that counts as points
stays out of its bank trades and offers, and an offer that costs it points must pay for them in goods.
Where a law reads declarations at a round's end, it declares a number when that pays.

Every constant of the policy is a field of `Weights`, and `Weights.default` is the bot at real tables.
-/

namespace CharterServer.Bots
open Lean Charter CharterServer.Game

variable {G : GameDef}

/-! ## Weights -/

/-- The bot's constants. A rewritten strategy keeps its own constants in `extra`. -/
structure Weights where
  /-- What one pip of a spot is worth when placing. -/
  pipValue : Int := 10
  /-- What each kind of resource a spot touches is worth. -/
  resourceBonus : Int := 5
  /-- What each step between a road and a free site costs. -/
  roadStepPenalty : Int := 40
  /-- The order of builds: the highest of these four goes first. An equal value keeps the order here. -/
  prioUpgrade : Int := 4
  /-- See `prioUpgrade`. A new piece on a spot, such as a settlement. -/
  prioSpot : Int := 3
  /-- See `prioUpgrade`. A piece that attaches to another, which only laws or packs make. -/
  prioAttach : Int := 2
  /-- See `prioUpgrade`. A piece on a link, such as a road. -/
  prioRoad : Int := 1
  /-- 1 to build roads even when the seat can already reach a free site. Today's bot does not. -/
  roadWithSite : Int := 0
  /-- 0 to stop trading with the bank. -/
  bankTradeOn : Int := 1
  /-- Accepting an offer: the weight of the goods got less the goods given. -/
  acceptGoods : Int := 1
  /-- The weight of how much closer the offer brings the next build. -/
  acceptNeed : Int := 0
  /-- The weight of how rarely the dice pay this seat the goods it gets, less those it gives. -/
  acceptScarcity : Int := 0
  /-- The penalty per point of the seat that made the offer. -/
  acceptOtherPoints : Int := 0
  /-- The score an offer must beat by this much. -/
  acceptMargin : Int := 0
  /-- How many offers a seat makes in a turn. -/
  offerLimit : Int := 0
  /-- How many of a surplus good an offer gives, for 1 of a good the seat is missing. 1 or 2. -/
  offerGive : Int := 1
  /-- A law gets a yes if it costs the seat at most this much at the next turn change. -/
  voteMargin : Int := 0
  /-- A deal gets a signature if each round costs the seat at most this much. -/
  dealMargin : Int := 0
  /-- 1 to keep goods that count as points out of bank trades and offers, and to count points when
  accepting an offer. 0 plays as the bot did before it knew about such goods. -/
  keepPoints : Int := 1
  /-- How many goods one point is worth, when accepting an offer and when declaring. -/
  pointValue : Int := 100
  /-- 1 to declare on its own turn when the round's end pays for it. 0 never declares. -/
  declareOn : Int := 1
  /-- Constants that a rewritten strategy adds. -/
  extra : List (String × Int) := []
  deriving Inhabited

/-- The weights of the bot at real tables. -/
def Weights.default : Weights := {}

/-- A constant from `extra`, or this default. -/
def Weights.extraOr (W : Weights) (name : String) (dflt : Int) : Int :=
  ((W.extra.find? (·.1 == name)).map (·.2)).getD dflt

/-- A weight that the arena and the evolution loop can see. -/
structure Param where
  name : String
  /-- The evolution loop stays between these two. -/
  min : Int
  max : Int
  get : Weights → Int
  set : Int → Weights → Weights

/-- Every named weight. -/
def params : List Param :=
  [ ⟨"pipValue", 0, 40, (·.pipValue), fun v w => { w with pipValue := v }⟩
  , ⟨"resourceBonus", 0, 40, (·.resourceBonus), fun v w => { w with resourceBonus := v }⟩
  , ⟨"roadStepPenalty", 0, 200, (·.roadStepPenalty), fun v w => { w with roadStepPenalty := v }⟩
  , ⟨"prioUpgrade", 0, 8, (·.prioUpgrade), fun v w => { w with prioUpgrade := v }⟩
  , ⟨"prioSpot", 0, 8, (·.prioSpot), fun v w => { w with prioSpot := v }⟩
  , ⟨"prioAttach", 0, 8, (·.prioAttach), fun v w => { w with prioAttach := v }⟩
  , ⟨"prioRoad", 0, 8, (·.prioRoad), fun v w => { w with prioRoad := v }⟩
  , ⟨"roadWithSite", 0, 1, (·.roadWithSite), fun v w => { w with roadWithSite := v }⟩
  , ⟨"bankTradeOn", 0, 1, (·.bankTradeOn), fun v w => { w with bankTradeOn := v }⟩
  , ⟨"acceptGoods", 0, 5, (·.acceptGoods), fun v w => { w with acceptGoods := v }⟩
  , ⟨"acceptNeed", 0, 10, (·.acceptNeed), fun v w => { w with acceptNeed := v }⟩
  , ⟨"acceptScarcity", 0, 5, (·.acceptScarcity), fun v w => { w with acceptScarcity := v }⟩
  , ⟨"acceptOtherPoints", 0, 5, (·.acceptOtherPoints), fun v w => { w with acceptOtherPoints := v }⟩
  , ⟨"acceptMargin", -10, 10, (·.acceptMargin), fun v w => { w with acceptMargin := v }⟩
  , ⟨"offerLimit", 0, 4, (·.offerLimit), fun v w => { w with offerLimit := v }⟩
  , ⟨"offerGive", 1, 2, (·.offerGive), fun v w => { w with offerGive := v }⟩
  , ⟨"voteMargin", -20, 20, (·.voteMargin), fun v w => { w with voteMargin := v }⟩
  , ⟨"dealMargin", -5, 5, (·.dealMargin), fun v w => { w with dealMargin := v }⟩
  , ⟨"keepPoints", 0, 1, (·.keepPoints), fun v w => { w with keepPoints := v }⟩
  , ⟨"pointValue", 0, 200, (·.pointValue), fun v w => { w with pointValue := v }⟩
  , ⟨"declareOn", 0, 1, (·.declareOn), fun v w => { w with declareOn := v }⟩ ]

/-- These weights with one changed. A name that is not a weight goes in `extra`. -/
def Weights.withValue (W : Weights) (name : String) (v : Int) : Weights :=
  match params.find? (·.name == name) with
  | some p => p.set v W
  | none => { W with extra := (name, v) :: W.extra.filter (·.1 != name) }

/-! ## The map, worked out once -/

/-- How often the dice pay this number. -/
def pips (G : GameDef) (n : Nat) : Nat := Scene.chanceOf G n

/-- Facts about a game's map, so that a decision does not walk the map's lists again. -/
structure Board (G : GameDef) where
  /-- Every spot, in order. -/
  spots : List Nat
  /-- The spots one link away, by spot. -/
  neighbours : Array (List Nat)
  /-- The spots at most 0, 1, 2 and 3 links away, by spot. -/
  balls : Array (Array (List Nat))
  /-- The pips of the regions that touch each spot. -/
  spotPips : Array Nat
  /-- How many kinds of goods touch each spot. -/
  spotGoods : Array Nat
  deriving Inhabited

/-- The spots at most `steps` links from a spot. -/
def ballOf (nbrs : Array (List Nat)) (v : Nat) : Nat → List Nat
  | 0 => [v]
  | k + 1 => ((ballOf nbrs v k).flatMap fun w => w :: nbrs.getD w []).eraseDups

/-- Work out a game's board. -/
def Board.of (G : GameDef) : Board G :=
  let high := G.map.links.foldl (fun m l => max m (max (l.1 + 1) (l.2 + 1))) G.map.spotCount
  let all := List.range high
  let links := G.map.links
  let nbrs := (all.map fun v => links.filterMap fun l =>
    if l.1 == v then some l.2 else if l.2 == v then some l.1 else none).toArray
  let touching (v : Nat) := (paidRegions G).filter (·.spots.contains v)
  { spots := List.range G.map.spotCount
    neighbours := nbrs
    balls := (all.map fun v => ([0, 1, 2, 3].map (ballOf nbrs v)).toArray).toArray
    spotPips := (all.map fun v => ((touching v).map fun r => pips G r.number).sum).toArray
    spotGoods := (all.map fun v => ((touching v).map (·.res)).eraseDups.length).toArray }

/-- What a strategy reads besides the state. -/
structure Ctx (G : GameDef) where
  weights : Weights
  board : Board G
  /-- How many offers the current seat has made this turn. The state does not say, because an accepted
  offer leaves it. -/
  offersThisTurn : Nat := 0
  deriving Inhabited

/-- A context with these weights, or the default ones. -/
def Ctx.of (G : GameDef) (W : Weights := .default) : Ctx G := { weights := W, board := Board.of G }

/-! ## What a seat can see -/

def bal (s : State G) (p : Nat) (r : Res) : Nat := s.balance (.player p) r

/-- The points one unit of this good is worth under these rules. Most goods are worth 0. -/
def worthIn (R : Rules) (r : Res) : Nat := ((R.worth.find? (·.1 == r)).map (·.2)).getD 0

/-- The points these goods are worth under these rules. -/
def bundleWorth (R : Rules) (b : Bundle) : Nat := (b.map fun x => x.2 * worthIn R x.1).sum

/-- The seat keeps all of this good when it gives `n` of it in a trade or an offer toward a build that
costs `cost` and is worth `gain` points. That is so when the good counts as points, unless the build is
worth more points than its cost and the `n` given together. With `keepPoints` 0 it keeps nothing. -/
def keeps (ctx : Ctx G) (R : Rules) (cost : Bundle) (gain n : Nat) (r : Res) : Bool :=
  ctx.weights.keepPoints != 0 && decide (worthIn R r > 0) &&
    !decide (gain > bundleWorth R cost + n * worthIn R r)

/-- What a spot is worth under these weights. -/
def spotValue (ctx : Ctx G) (v : Nat) : Int :=
  ctx.weights.pipValue * (ctx.board.spotPips.getD v 0 : Int) +
    ctx.weights.resourceBonus * (ctx.board.spotGoods.getD v 0 : Int)

/-- Which spots hold a piece, by spot. -/
def occupied (ctx : Ctx G) (s : State G) : Array Bool :=
  s.pieces.foldl (fun a x => match x.loc with
    | .spot v => a.setIfInBounds v true
    | .link _ => a) (Array.replicate ctx.board.neighbours.size false)

/-- Which spots have no piece, and none next to them, by spot. -/
def freeMap (ctx : Ctx G) (s : State G) : Array Bool :=
  let occ := occupied ctx s
  ctx.board.neighbours.mapIdx fun v ns => !occ.getD v true && ns.all fun w => !occ.getD w true

/-- The free sites, in order. -/
def freeSites (ctx : Ctx G) (s : State G) : List Nat :=
  let free := freeMap ctx s
  ctx.board.spots.filter (free.getD · false)

/-- Which spots this seat reaches with a piece or a link, by spot. -/
def reachMap (ctx : Ctx G) (s : State G) (p : Nat) : Array Bool :=
  s.pieces.foldl (fun a x =>
    if x.owner == p then
      match x.loc with
      | .spot w => a.setIfInBounds w true
      | .link l => (a.setIfInBounds l.1 true).setIfInBounds l.2 true
    else a) (Array.replicate ctx.board.neighbours.size false)

/-- Some spot is both free and reached. `free` is `freeMap` and `reach` is `reachMap`. -/
def siteIn (ctx : Ctx G) (free reach : Array Bool) : Bool :=
  ctx.board.spots.any fun v => free.getD v false && reach.getD v false

/-- This seat reaches a free site. -/
def hasFreeSite (ctx : Ctx G) (s : State G) (p : Nat) : Bool :=
  siteIn ctx (freeMap ctx s) (reachMap ctx s p)

/-- A road is worth the best free site near its ends, less for each step away. `free` is `freeMap`. -/
def roadValue (ctx : Ctx G) (free : Array Bool) (l : Nat × Nat) : Int :=
  let ballsA := ctx.board.balls.getD l.1 #[]
  let ballsB := ctx.board.balls.getD l.2 #[]
  let isFree (v : Nat) := free.getD v false
  [0, 1, 2, 3].foldl (fun b d =>
    match (ballsA.getD d []).filter isFree ++ (ballsB.getD d []).filter isFree with
    | [] => b
    | near =>
      max b ((near.foldl (fun m v => max m (spotValue ctx v)) 0) - ctx.weights.roadStepPenalty * (d : Int))) (-100)

def bestBy {α : Type} (xs : List α) (f : α → Int) : Option α :=
  xs.foldl (fun b x => match b with
    | none => some x
    | some y => if f x > f y then some x else some y) none

/-! ## Which moves the engine takes -/

/-- The engine accepts this move from this seat now. With no deal running, nothing that happens after the
move can fail, because a win has nothing to refund. So in that case this leaves out the look for a winner,
which costs more than the rest of `step`. -/
def isLegal (s : State G) (p : Nat) (m : Move) : Bool :=
  match m with
  | .endTurn => (Engine.step G s (.move p m)).toOption.isSome
  | _ =>
    if s.deals.isEmpty && s.phase != .ended then
      match Engine.act s p (Engine.moveBody s p m) with
      | .ok _ => true
      | .error _ => false
    else (Engine.step G s (.move p m)).toOption.isSome

/-- The best of these moves that `ok` allows. It tests the best first, so it seldom tests more. -/
def bestOk (ok : Move → Bool) (xs : List (Move × Int)) : Option Move :=
  match bestBy xs (·.2) with
  | none => none
  | some (m, _) => if ok m then some m else (bestBy (xs.filter (ok ·.1)) (·.2)).map (·.1)

/-- The best of these moves that the engine accepts. -/
def bestLegal (s : State G) (p : Nat) (xs : List (Move × Int)) : Option Move :=
  bestOk (isLegal s p) xs

/-- The spots where this seat has a piece of this kind. -/
def spotsOfKind (s : State G) (p : Nat) (k : PieceKind) : List Nat :=
  s.pieces.filterMap fun x =>
    match x.loc with
    | .spot v => if x.owner == p && x.kind == k then some v else none
    | .link _ => none

/-- Place moves of the kinds that `test` picks, in the order of `Engine.legalMoves`. It holds every such
move the engine accepts in the actions phase, and maybe some that it does not: this is the cheap part of
`canPlace`. So a pick from it still goes to `isLegal`. `free` is `freeMap` and `reach` is `reachMap`. -/
def placesWith (ctx : Ctx G) (s : State G) (p : Nat) (free reach : Thunk (Array Bool))
    (test : Placement → Bool) : List Move :=
  if !(s.phase == .actions && s.isTurnOf p && decide (s.actionsThisTurn p < maxActionsPerTurn)) then [] else
  let rules := s.rules
  rules.pieces.flatMap fun d =>
    match rules.piece? d.name with
    | none => []
    | some e =>
      if !(test e.placement && s.affords p e.cost && decide (s.countOf p d.name < e.limit)) then [] else
      let onSpots (ok : Nat → Bool) : List Move :=
        ctx.board.spots.filterMap fun v =>
          if ok v && !s.blockedByDeal p d.name (.spot v) then some (.place d.name (.spot v)) else none
      match e.placement with
      | .link =>
        let reach := reach.get
        let taken := s.pieces.filterMap fun x => match x.loc with
          | .link l => some l
          | .spot _ => none
        G.map.links.filterMap fun l =>
          if (reach.getD l.1 false || reach.getD l.2 false) && !taken.contains l
              && !s.blockedByDeal p d.name (.link l) then
            some (.place d.name (.link l))
          else none
      | .spot =>
        let free := free.get
        let reach := reach.get
        onSpots fun v => free.getD v false && reach.getD v false
      | .upgrade k =>
        let mine := spotsOfKind s p k
        onSpots mine.contains
      | .attach k =>
        let mine := spotsOfKind s p k
        let done_ := spotsOfKind s p d.name
        onSpots fun v => mine.contains v && !done_.contains v

/-- Place moves of the kinds that `test` picks. See `placesWith`. -/
def placesOf (ctx : Ctx G) (s : State G) (p : Nat) (test : Placement → Bool) : List Move :=
  placesWith ctx s p (Thunk.mk fun _ => freeMap ctx s) (Thunk.mk fun _ => reachMap ctx s p) test

/-- The place moves of a setup turn, in the order of `Engine.legalMoves`. As with `placesOf`, a pick still
goes to `isLegal`. -/
def setupPlaces (ctx : Ctx G) (s : State G) (p : Nat) : List Move :=
  match G.setupPieces[s.actionsThisTurn p]? with
  | none => []
  | some k =>
    if !s.isTurnOf p then [] else
    let rules := s.rules
    match rules.piece? k with
    | none => []
    | some e =>
      if !(decide (s.countOf p k < e.limit)) then [] else
      match e.placement with
      | .link =>
        let reach := reachMap ctx s p
        G.map.links.filterMap fun l =>
          if (reach.getD l.1 false || reach.getD l.2 false) && s.setupPlacementOk p e (.link l) then
            some (.place k (.link l))
          else none
      | .spot =>
        let free := freeMap ctx s
        ctx.board.spots.filterMap fun v =>
          if free.getD v false then some (.place k (.spot v)) else none
      | _ =>
        ctx.board.spots.filterMap fun v =>
          if s.setupPlacementOk p e (.spot v) then some (.place k (.spot v)) else none

/-! ## Declaring -/

mutual
  /-- The resources whose declared numbers this number reads. -/
  def exprDeclared : Expr → List ResRef
    | .declared _ r => [r]
    | .add a b | .sub a b | .mul a b | .min a b | .max a b | .divBy a b => exprDeclared a ++ exprDeclared b
    | .div a _ => exprDeclared a
    | .totalOver c a | .mostOver c a | .leastOver c a => condDeclared c ++ exprDeclared a
    | _ => []

  /-- The resources whose declared numbers this test reads. -/
  def condDeclared : Cond → List ResRef
    | .lt a b | .le a b | .eq a b => exprDeclared a ++ exprDeclared b
    | .and a b | .or a b => condDeclared a ++ condDeclared b
    | .not c => condDeclared c
    | _ => []
end

mutual
  /-- The resources whose declared numbers this effect reads. -/
  def effectDeclared : Effect → List ResRef
    | .transfer _ _ _ amount => exprDeclared amount
    | .movePiece .. => []
    | .forEach c body | .when c body => condDeclared c ++ effectsDeclared body

  /-- The resources whose declared numbers these effects read. -/
  def effectsDeclared : List Effect → List ResRef
    | [] => []
    | e :: es => effectDeclared e ++ effectsDeclared es
end

/-- The resources whose declared numbers a law in force reads at a round's end, in the game's order. Most
packs have none. -/
def declaredAtRoundEnd (s : State G) : List Res :=
  let refs := s.laws.flatMap fun x => x.2.clauses.flatMap fun
    | .onRoundEnd body => effectsDeclared body
    | _ => []
  if refs.isEmpty then [] else
  (G.resources.map (·.name)).filter fun r => refs.contains .harvested || refs.contains (.lit r)

/-- What a seat has, for comparing declarations: `pointValue` for each point, and 1 for each good. -/
def holdingValue (ctx : Ctx G) (s : State G) (p : Nat) : Int :=
  ctx.weights.pointValue * (s.pointsOf p : Int) + ((G.resources.map fun r => bal s p r.name).sum : Int)

/-- A declaration that raises what this seat will have after this round's end, if one does. It tries
0, 1 and what it holds, for each resource that a law reads at a round's end. It predicts the round's end
as if this were the round's last turn, with every other seat's declarations as they are now. -/
def declareMove (ctx : Ctx G) (s : State G) (p : Nat) : Option Move :=
  if ctx.weights.declareOn == 0 || !(s.phase == .actions && s.isTurnOf p) then none else
  match declaredAtRoundEnd s with
  | [] => none
  | names =>
    let last : State G := { s with turnIndex := s.turnOrder.length - 1 }
    let valueAfter (x : State G) : Int := holdingValue ctx x.afterRoundEnd p
    let now := valueAfter last
    let tries := names.flatMap fun r =>
      let cur := s.declared p r
      ([0, 1, bal s p r].eraseDups.filter (· != cur)).map fun n =>
        let x : State G := { last with declared := fun q y => if q == p && y == r then n else s.declared q y }
        (Move.declare r n, valueAfter x)
    bestOk (isLegal s p) (tries.filter fun x => decide (x.2 > now))

/-! ## Choosing a move -/

/-- A bank trade toward paying `cost`, if trades can cover all of it. `ok` says which moves can happen. The
seat gives none of a good that `keep` picks. -/
def tradeToward (s : State G) (p : Nat) (cost : Bundle) (ok : Move → Bool)
    (keep : Res → Bool := fun _ => false) : Option Move :=
  let rate := s.rules.bankRate
  let need (r : Res) : Nat := ((cost.find? (·.1 == r)).map (·.2)).getD 0
  let names := G.resources.map (·.name)
  let surplus (r : Res) : Nat := if keep r then 0 else bal s p r - need r
  let short := names.filter fun r => need r > bal s p r
  let missing := (short.map fun r => need r - bal s p r).sum
  if missing == 0 || rate == 0 then none else
  if (names.map fun r => surplus r / rate).sum < missing then none else
  match short.head?, bestBy (names.filter fun r => surplus r ≥ rate) (fun r => (surplus r : Int)) with
  | some m, some g =>
    let mv := Move.bankTrade g m
    if ok mv then some mv else none
  | _, _ => none

/-- An offer to anyone toward paying `cost`: 1 or 2 of the good the seat has most spare, for 1 of the
first good it is short of. The build is worth `gain` points, and the seat offers no good that it `keeps`. -/
def offerToward (ctx : Ctx G) (s : State G) (p : Nat) (cost : Bundle) (gain : Nat := 0) : Option Move :=
  let give := (max 1 (min 2 ctx.weights.offerGive)).toNat
  let need (r : Res) : Nat := ((cost.find? (·.1 == r)).map (·.2)).getD 0
  let names := goodsOf G
  let R := s.rules
  let spare (r : Res) : Nat := if keeps ctx R cost gain give r then 0 else bal s p r - need r
  match (names.filter fun r => need r > bal s p r).head?,
      bestBy (names.filter fun r => spare r ≥ give) (fun r => (spare r : Int)) with
  | some m, some g => some (.offer none [(g, give)] [(m, 1)])
  | _, _ => none

/-- The points a piece of this kind is worth under the rules in force. -/
def piecePoints (s : State G) (k : PieceKind) : Nat := ((s.rules.piece? k).map (·.points)).getD 0

/-- What the seat is saving for, each with the points it is worth: an upgrade if it has something to
upgrade, then the spot piece if it reaches a free site, and otherwise the link piece. The first that exists
is its next build. -/
def buildGoals (ctx : Ctx G) (s : State G) (p : Nat) : List (Bundle × Nat) :=
  let goal (d : PieceDef) : Bundle × Nat := (s.costOf d.name, piecePoints s d.name)
  let up := match upgradePiece G with
    | some (d, old) => if s.countOf p old > 0 && (s.rules.piece? d.name).isSome then [goal d] else []
    | none => []
  let rest :=
    if hasFreeSite ctx s p then ((spotPiece G).map goal).toList
    else ((linkPiece G).map goal).toList
  up ++ rest

/-- The costs of `buildGoals`. -/
def buildTargets (ctx : Ctx G) (s : State G) (p : Nat) : List Bundle := (buildGoals ctx s p).map (·.1)

/-- Noise on a spot's value at setup, fixed by the game's seed and the spot, up to the weight `setupJitter`.
That weight is 0 unless a test sets it. It makes bots open differently from game to game. -/
def setupNoise (ctx : Ctx G) (s : State G) (v : Nat) : Int :=
  let most := ctx.weights.extraOr "setupJitter" 0
  if most ≤ 0 then 0 else
  ((scramble (s.seed + UInt64.ofNat v * 0x9E3779B97F4A7C15)).toNat % (most.toNat + 1) : Nat)

/-- The setup move: the best spot, then the road toward the best site. `ok` says which moves can happen. -/
def setupFrom (ctx : Ctx G) (s : State G) (moves : List Move) (ok : Move → Bool) : Move :=
  let spotMoves := moves.filterMap fun m => match m with
    | .place _ (.spot v) => some (m, spotValue ctx v + setupNoise ctx s v)
    | _ => none
  match bestOk ok spotMoves with
  | some m => m
  | none =>
    let free := freeMap ctx s
    let roads := moves.filterMap fun m => match m with
      | .place _ (.link l) => some (m, roadValue ctx free l)
      | _ => none
    match bestOk ok roads with
    | some m => m
    | none => .endTurn

/-- The kinds of build, in the order the weights say. Equal weights keep the order listed here. -/
def buildOrder (W : Weights) : List (Int × Nat) :=
  let kinds : List (Int × Nat) :=
    [(W.prioUpgrade, 0), (W.prioSpot, 1), (W.prioAttach, 2), (W.prioRoad, 3)]
  (kinds.toArray.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 < b.2)).toList

/-- The move on a bot's turn: builds in the order of the weights (upgrade, settle, law-made piece, road),
then an offer if the weights allow one, then a bank trade, then a declaration, then end. -/
def actionMove (ctx : Ctx G) (s : State G) (p : Nat) : Move := Id.run do
  let W := ctx.weights
  let spotOf (m : Move) : Int := match m with
    | .place _ (.spot v) => spotValue ctx v
    | _ => 0
  let scored (ms : List Move) (f : Move → Int) : List (Move × Int) := ms.map fun m => (m, f m)
  let free : Thunk (Array Bool) := Thunk.mk fun _ => freeMap ctx s
  let reach : Thunk (Array Bool) := Thunk.mk fun _ => reachMap ctx s p
  let hasSite : Thunk Bool := Thunk.mk fun _ => siteIn ctx free.get reach.get
  let places := placesWith ctx s p free reach
  for (_, kind) in buildOrder W do
    match kind with
    | 0 =>
      if let some m := bestLegal s p (scored (places fun | .upgrade _ => true | _ => false) spotOf) then
        return m
    | 1 =>
      if let some m := bestLegal s p (scored (places fun | .spot => true | _ => false) spotOf) then
        return m
    | 2 =>
      if let some m := (places fun | .attach _ => true | _ => false).find? (isLegal s p) then
        return m
    | _ =>
      if W.roadWithSite != 0 || !hasSite.get then
        let roads := (places fun | .link => true | _ => false).filterMap fun m => match m with
          | .place _ (.link l) => some (m, roadValue ctx free.get l)
          | _ => none
        if let some m := bestLegal s p roads then return m
  if (ctx.offersThisTurn : Int) < W.offerLimit then
    for (cost, gain) in buildGoals ctx s p do
      if let some m := offerToward ctx s p cost gain then
        if isLegal s p m then return m
  if W.bankTradeOn != 0 then
    let R := s.rules
    let trade (d : PieceDef) :=
      let cost := s.costOf d.name
      tradeToward s p cost (isLegal s p) (keeps ctx R cost (piecePoints s d.name) R.bankRate)
    if let some (d, old) := upgradePiece G then
      if s.countOf p old > 0 && (s.rules.piece? d.name).isSome then
        if let some m := trade d then return m
    if hasSite.get then
      if let some d := spotPiece G then
        if let some m := trade d then return m
    else
      if let some d := linkPiece G then
        if let some m := trade d then return m
  if let some m := declareMove ctx s p then return m
  return .endTurn

/-- The move of this seat if it is its turn, whatever the phase. -/
def turnMove (ctx : Ctx G) (s : State G) (p : Nat) : Move :=
  if s.phase == .setup then setupFrom ctx s (setupPlaces ctx s p) (isLegal s p)
  else actionMove ctx s p

/-! ## Reacting to others -/

/-- A seat's resources, after a list of entries. -/
def netFor (p : Nat) (es : List Entry) : Int :=
  es.foldl (fun acc e =>
    let gain : Int := if e.dst == .player p then e.amount else 0
    let loss : Int := if e.src == .player p then e.amount else 0
    acc + gain - loss) 0

/-- Yes if the law costs nothing at the next turn change, over every roll, and gives no other seat
the win now. The vote margin moves that line. -/
def lawOk (ctx : Ctx G) (s : State G) (p id : Nat) (L : Law) : Bool :=
  let s' := s.withLaw id L
  let rolls := Scene.rollsOf G
  let total (x : State G) : Int :=
    (rolls.map fun r => (pips G r : Int) * netFor p (Engine.predictNextTurn G x r)).foldl (· + ·) 0
  let handsOthersTheWin :=
    s.turnOrder.any fun q => q != p && decide (G.targetPoints ≤ s'.pointsOf q)
  -- A law that ends the game now is good only for the seat that would win.
  let endsAgainstUs := L.clauses.any Clause.isEndGame && Engine.bestSeat s' s'.turnOrder != some p
  !handsOthersTheWin && !endsAgainstUs && decide (total s' + ctx.weights.voteMargin ≥ total s)

/-- Yes if each round of the deal pays this seat at least what it pays. The deal margin moves that line. -/
def dealOk (ctx : Ctx G) (p : Nat) (d : Deal) : Bool :=
  let net (ps : List Pay) : Int := ps.foldl (fun acc x =>
    let inn : Int := match x.dst with
      | .seat q => if q == p then x.amount else 0
      | .treasury => 0
    let out : Int := if x.src == p then x.amount else 0
    acc + inn - out) 0
  decide (net d.allPays + ctx.weights.dealMargin ≥ 0)

def bundleTotal (b : Bundle) : Nat := (b.map (·.2)).sum

/-- How much a seat's holdings fall short of a price. -/
def shortBy (cost : Bundle) (held : Res → Int) : Int :=
  (cost.map fun x => max 0 ((x.2 : Int) - held x.1)).foldl (· + ·) 0

/-- How much closer an offer brings this seat to its next build. -/
def offerNeed (ctx : Ctx G) (s : State G) (b : Nat) (o : Offer) : Int :=
  let amount (bd : Bundle) (r : Res) : Int := ((bd.find? (·.1 == r)).map (fun x => (x.2 : Int))).getD 0
  match (buildTargets ctx s b).head? with
  | none => 0
  | some cost =>
    let now (r : Res) : Int := (bal s b r : Int)
    let after (r : Res) : Int := now r + amount o.give r - amount o.get r
    shortBy cost now - shortBy cost after

/-- What the dice pay this seat of a good, in pips times yield. -/
def incomeOf (s : State G) (p : Nat) (r : Res) : Nat :=
  let rules := s.rules
  let mine := s.pieces.filter (·.owner == p)
  ((paidRegions G).filter (·.res == r)).foldl (fun acc reg =>
    acc + pips G reg.number * (mine.foldl (fun n x => match x.loc with
      | .spot v =>
        if reg.spots.contains v then n + ((rules.piece? x.kind).map (·.yield)).getD 0 else n
      | .link _ => n) 0)) 0

/-- How rarely the dice pay this seat what it gets, less what it gives. -/
def offerScarcity (s : State G) (b : Nat) (o : Offer) : Int :=
  let rarity (r : Res) : Int := max 0 (12 - (incomeOf s b r : Int))
  let worth (bd : Bundle) : Int := (bd.map fun x => (x.2 : Int) * rarity x.1).foldl (· + ·) 0
  worth o.give - worth o.get

/-- A seat's score for an offer. It takes the offer when this is at least 0. By default that means it
gets at least as many goods as it gives, counting each point that the goods are worth as `pointValue` goods. -/
def offerScore (ctx : Ctx G) (s : State G) (b : Nat) (o : Offer) : Int :=
  let W := ctx.weights
  let goods := W.acceptGoods * ((bundleTotal o.give : Int) - (bundleTotal o.get : Int))
  let need := if W.acceptNeed == 0 then 0 else W.acceptNeed * offerNeed ctx s b o
  let scarce := if W.acceptScarcity == 0 then 0 else W.acceptScarcity * offerScarcity s b o
  let rival := if W.acceptOtherPoints == 0 then 0 else W.acceptOtherPoints * (s.pointsOf o.src : Int)
  let points := if W.keepPoints == 0 then 0 else
    let R := s.rules
    W.pointValue * ((bundleWorth R o.give : Int) - (bundleWorth R o.get : Int))
  goods + need + scarce - rival + points - W.acceptMargin

/-- Votes, signatures and accepted offers from these seats. `mayVote` says which laws can be voted on now. -/
def reactions (ctx : Ctx G) (s : State G) (bots : List Nat) (mayVote : Nat → Bool := fun _ => true) :
    List Event := Id.run do
  let mut out : Array Event := #[]
  for p in s.openProposals do
    for b in bots do
      match p.body with
      | .law L =>
        if mayVote p.id && !(p.votes.any (·.1 == b)) then
          out := out.push (.vote b p.id (lawOk ctx s b p.id L))
      | .deal d =>
        if d.signers.contains b && !p.signed.contains b && dealOk ctx b d then
          out := out.push (.sign b p.id)
  if s.phase == .actions then
    for o in s.offers do
      for b in bots do
        if o.src != b && (o.to.isNone || o.to == some b) && decide (offerScore ctx s b o ≥ 0) then
          out := out.push (.move b (.accept o.id))
  return out.toList

/-- This seat's move and then ending its turn, if it is its turn. -/
def turnEvents (ctx : Ctx G) (s : State G) (seat : Nat) : List Event :=
  if s.currentSeat != some seat then [] else
  let m := turnMove ctx s seat
  if m != .endTurn then [.move seat m, .move seat .endTurn] else [.move seat m]

/-- Today's bot: candidate events for these seats, best first. -/
def handEvents (ctx : Ctx G) (s : State G) (bots : List Nat) (mayVote : Nat → Bool := fun _ => true) :
    List Event :=
  if bots.isEmpty || s.phase == .ended then [] else
  let moves := match s.currentSeat with
    | some p => if bots.contains p then turnEvents ctx s p else []
    | none => []
  reactions ctx s bots mayVote ++ moves

/-! ## Strategies -/

/-- A way to play. `decide` gives the events these seats want, best first. The engine tries them in order,
and the first it accepts happens. -/
structure Strategy where
  name : String
  decide : {G : GameDef} → Ctx G → State G → (bots : List Nat) → List Event

instance : Inhabited Strategy := ⟨{ name := "", decide := fun _ _ _ => [] }⟩

/-- A strategy from what it does for one seat. Several seats' events join in seat order. -/
def Strategy.ofSeat (name : String) (f : {G : GameDef} → Ctx G → State G → Nat → List Event) : Strategy :=
  { name, decide := fun ctx s bots => bots.flatMap (f ctx s) }

/-- Today's hand-written bot. -/
def hand : Strategy := { name := "hand", decide := fun ctx s bots => handEvents ctx s bots }

/-! ## The order of events from several seats

Reactions come before moves: votes and signatures by proposal, then accepted offers by offer, then the
current seat's move. Seats are in order within each. This is `Player.merged`, for events. -/

/-- Where an event goes in that order. -/
def orderKey : Event → Nat × Nat
  | .vote _ id _ | .sign _ id => (0, id)
  | .move _ (.accept id) => (1, id)
  | _ => (2, 0)

/-- The seat an event speaks for. The timer's event speaks for none. -/
def seatOf : Event → Option Nat
  | .move p _ | .propose p _ | .vote p _ _ | .sign p _ | .exit p _ => some p
  | .forceEndTurn => none

/-- Join several seats' candidates in that order. The sort is stable, so seats stay in order. -/
def merged (lists : List (List Event)) : List Event :=
  let keyed := lists.flatten.zipIdx
  ((keyed.toArray.qsort fun a b =>
      let ka := orderKey a.1
      let kb := orderKey b.1
      ka.1 < kb.1 || (ka.1 == kb.1 && (ka.2 < kb.2 || (ka.2 == kb.2 && a.2 < b.2)))).toList).map (·.1)

/-! ## Events as JSON -/

def moveEvent (p : Nat) (m : Move) : Json :=
  Json.mkObj [("t", "move"), ("seat", toJson p), ("move", moveJson m)]

/-- The log's form of an event a bot makes. The hand bot makes moves, votes and signatures only. -/
def eventJson? : Event → Option Json
  | .move p m => some (moveEvent p m)
  | .vote seat id yes =>
    some (Json.mkObj [("t", "vote"), ("seat", toJson seat), ("id", toJson id), ("yes", toJson yes)])
  | .sign seat id => some (Json.mkObj [("t", "sign"), ("seat", toJson seat), ("id", toJson id)])
  | _ => none

end CharterServer.Bots
