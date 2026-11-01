import Server.BotCore

namespace Evolved.S9x0
open Charter CharterServer CharterServer.Bots CharterServer.Game

def evNeed (cost : Bundle) (r : Res) : Nat := ((cost.find? (·.1 == r)).map (·.2)).getD 0

def evAmt (bd : Bundle) (r : Res) : Int := ((bd.find? (·.1 == r)).map (fun x => (x.2 : Int))).getD 0

def evIsUp : Placement → Bool
  | .upgrade _ => true
  | _ => false

def evIsSpot : Placement → Bool
  | .spot => true
  | _ => false

def evIsAttach : Placement → Bool
  | .attach _ => true
  | _ => false

def evIsLink : Placement → Bool
  | .link => true
  | _ => false

def evTouch {G : GameDef} (_ctx : Ctx G) (v : Nat) : List (Res × Nat) :=
  (paidRegions G).filterMap fun r =>
    if r.spots.contains v then some (r.res, CharterServer.Bots.pips G r.number) else none

def evSupply {G : GameDef} (_ctx : Ctx G) (r : Res) : Nat :=
  ((paidRegions G).filter (·.res == r)).foldl (fun a reg => a + CharterServer.Bots.pips G reg.number) 0

def evScoreTable {G : GameDef} (ctx : Ctx G) (s : State G) (p : Nat) : Array Int :=
  let W := ctx.weights
  let newB := W.extraOr "newKindBonus" 6
  let rareW := W.extraOr "rareWeight" 3
  let demW := W.extraOr "demandWeight" 3
  let names := G.resources.map (·.name)
  let inc : List (Res × Nat) := names.map fun r => (r, incomeOf s p r)
  let incOf (r : Res) : Nat := ((inc.find? (·.1 == r)).map (·.2)).getD 0
  let sup : List (Res × Nat) := names.map fun r => (r, evSupply ctx r)
  let total := (sup.map (·.2)).sum
  let mean := total / (max 1 names.length)
  let supOf (r : Res) : Nat := ((sup.find? (·.1 == r)).map (·.2)).getD 0
  let rarity (r : Res) : Int := ((10 * mean : Nat) : Int) / ((max 1 (supOf r) : Nat) : Int)
  let dcosts : List Bundle :=
    ((spotPiece G).map fun d => s.costOf d.name).toList ++
    ((upgradePiece G).map fun x => s.costOf x.1.name).toList ++
    ((linkPiece G).map fun d => s.costOf d.name).toList
  let dOf (r : Res) : Nat := (dcosts.map fun c => evNeed c r).sum
  let dTot : Nat := (names.map dOf).sum
  let dem (r : Res) : Int := ((10 * dOf r * names.length : Nat) : Int) / ((max 1 dTot : Nat) : Int)
  (List.range ctx.board.neighbours.size).toArray.map fun v =>
    let ts := evTouch ctx v
    let base := ts.foldl (fun (acc : Int) x =>
      let fresh : Int := if incOf x.1 == 0 then newB else 0
      acc + (x.2 : Int) * (W.pipValue + fresh) + rareW * (x.2 : Int) * rarity x.1 / 10
        + demW * (x.2 : Int) * (dem x.1 - 10) / 10) (0 : Int)
    base + W.extraOr "myResBonus" 8 * ((ts.map (·.1)).eraseDups.length : Int)

def evRoadValue {G : GameDef} (ctx : Ctx G) (sc : Nat → Int) (free : Array Bool) (l : Nat × Nat) : Int :=
  let ballsA := ctx.board.balls.getD l.1 #[]
  let ballsB := ctx.board.balls.getD l.2 #[]
  let isFree (v : Nat) : Bool := free.getD v false
  ([0, 1, 2, 3] : List Nat).foldl (fun (b : Int) d =>
    match (ballsA.getD d []).filter isFree ++ (ballsB.getD d []).filter isFree with
    | [] => b
    | near => max b ((near.foldl (fun m v => max m (sc v)) (0 : Int)) - ctx.weights.roadStepPenalty * (d : Int))) (-100 : Int)

def evRoads {G : GameDef} (ctx : Ctx G) (sc : Nat → Int) (free : Array Bool) (ms : List Move) : List (Move × Int) :=
  (ms.filterMap fun m => match m with
    | .place _ (.link l) => some (m, evRoadValue ctx sc free l)
    | _ => none).filter fun x => decide (x.2 > -100)

def evScoreSpots (ms : List Move) (f : Nat → Int) : List (Move × Int) :=
  ms.map fun m => match m with
    | .place _ (.spot v) => (m, f v)
    | _ => (m, 0)

def evRoadUseful {G : GameDef} (ctx : Ctx G) (s : State G) (reach free : Array Bool) (sc : Nat → Int) : Bool :=
  let taken := s.pieces.filterMap fun x => match x.loc with
    | .link l => some l
    | .spot _ => none
  G.map.links.any fun l =>
    (reach.getD l.1 false || reach.getD l.2 false) && !taken.contains l && decide (evRoadValue ctx sc free l > -100)

def evRoom {G : GameDef} (s : State G) (p : Nat) (k : PieceKind) : Bool :=
  match s.rules.piece? k with
  | some d => decide (s.countOf p k < d.limit)
  | none => false

def evTargets {G : GameDef} (s : State G) (p : Nat) (hasSite useRoad : Bool) : List Bundle :=
  let up : List Bundle := match upgradePiece G with
    | some (d, old) => if decide (s.countOf p old > 0) && evRoom s p d.name then [s.costOf d.name] else []
    | none => []
  let sp : List Bundle := match spotPiece G with
    | some d => if hasSite && evRoom s p d.name then [s.costOf d.name] else []
    | none => []
  let rd : List Bundle := match linkPiece G with
    | some d => if !hasSite && useRoad && evRoom s p d.name then [s.costOf d.name] else []
    | none => []
  up ++ sp ++ rd

def evSpotKeep {G : GameDef} (s : State G) (p : Nat) (hasSite : Bool) : List Bundle :=
  if hasSite then [] else
  match spotPiece G with
  | some d => if evRoom s p d.name then [s.costOf d.name] else []
  | none => []

def evSort (on : Bool) (ts : List Bundle) (held : Res → Int) : List Bundle :=
  if !on then ts else
  let keyed := ts.zipIdx.map fun x => (x.1, shortBy x.1 held, x.2)
  ((keyed.toArray.qsort fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)).toList).map (·.1)

def evTrade {G : GameDef} (s : State G) (p : Nat) (cost : Bundle) (protect : Res → Nat) (ok : Move → Bool) : Option Move :=
  let rate := s.rules.bankRate
  let names := G.resources.map (·.name)
  let keep (r : Res) : Nat := max (evNeed cost r) (protect r)
  let surplus (r : Res) : Nat := bal s p r - keep r
  let short := names.filter fun r => decide (evNeed cost r > bal s p r)
  let missing := (short.map fun r => evNeed cost r - bal s p r).sum
  if missing == 0 || rate == 0 then none else
  if (names.map fun r => surplus r / rate).sum < missing then none else
  match bestBy short (fun r => -(incomeOf s p r : Int)), bestBy (names.filter fun r => decide (surplus r ≥ rate)) (fun r => (surplus r : Int)) with
  | some m, some g =>
    let mv := Move.bankTrade g m
    if ok mv then some mv else none
  | _, _ => none

def evOffer {G : GameDef} (ctx : Ctx G) (s : State G) (p : Nat) (targets : List Bundle) (protect : Res → Nat) : Option Move :=
  let names := goodsOf G
  let k := ctx.offersThisTurn
  let twoOn := ctx.weights.extraOr "twoForOne" 1 != 0
  let tryCost (cost : Bundle) : Option Move :=
    let short := names.filter fun r => decide (evNeed cost r > bal s p r)
    let missing := (short.map fun r => evNeed cost r - bal s p r).sum
    let keep (r : Res) : Nat := max (evNeed cost r) (protect r)
    let spare (r : Res) : Nat := bal s p r - keep r
    let gives := names.filter fun r => decide (spare r ≥ 1)
    match bestBy short (fun r => -(incomeOf s p r : Int)), gives with
    | some m, _ :: _ =>
      let sorted := (gives.toArray.qsort fun a b => decide (spare a > spare b)).toList
      let g := sorted.getD (k % sorted.length) m
      let two := twoOn && decide (k ≥ 1) && missing == 1 && decide (spare g ≥ 2)
      let n : Nat := if two then 2 else 1
      some (Move.offer none [(g, n)] [(m, 1)])
    | _, _ => none
  targets.findSome? fun c => match tryCost c with
    | some mv => if isLegal s p mv then some mv else none
    | none => none

def evSetup {G : GameDef} (ctx : Ctx G) (s : State G) (p : Nat) : Move :=
  let moves := setupPlaces ctx s p
  let ok := isLegal s p
  let tbl := evScoreTable ctx s p
  let sc : Nat → Int := fun v => tbl.getD v 0
  let free := freeMap ctx s
  let expW := ctx.weights.extraOr "expandWeight" 2
  let grow (v : Nat) : Int :=
    let bs := ctx.board.balls.getD v #[]
    let b1 := bs.getD 1 []
    let b2 := bs.getD 2 []
    (b2.filter fun w => free.getD w false && !b1.contains w).foldl (fun m w => max m (sc w)) (0 : Int)
  let spotMoves := moves.filterMap fun m => match m with
    | .place _ (.spot v) => some (m, sc v + expW * grow v / 10)
    | _ => none
  match bestOk ok spotMoves with
  | some m => m
  | none =>
    let roads := moves.filterMap fun m => match m with
      | .place _ (.link l) => some (m, evRoadValue ctx sc free l)
      | _ => none
    match bestOk ok roads with
    | some m => m
    | none => Move.endTurn

def evAction {G : GameDef} (ctx : Ctx G) (s : State G) (p : Nat) : Move := Id.run do
  let W := ctx.weights
  let free := freeMap ctx s
  let reach := reachMap ctx s p
  let hasSite := siteIn ctx free reach
  let tbl := evScoreTable ctx s p
  let sc : Nat → Int := fun v => tbl.getD v 0
  let places := placesWith ctx s p (Thunk.mk fun _ => free) (Thunk.mk fun _ => reach)
  let ups := evScoreSpots (places evIsUp) (fun v => (ctx.board.spotPips.getD v 0 : Int))
  let sps := evScoreSpots (places evIsSpot) sc
  if W.extraOr "spotFirst" 1 != 0 then
    if let some m := bestLegal s p sps then return m
  if let some m := bestLegal s p ups then return m
  if let some m := bestLegal s p sps then return m
  if let some m := (places evIsAttach).find? (isLegal s p) then return m
  let useRoad := !hasSite && evRoadUseful ctx s reach free sc
  if W.roadWithSite != 0 || !hasSite then
    let roads := evRoads ctx sc free (places evIsLink)
    if let some m := bestLegal s p roads then return m
  let held : Res → Int := fun r => (bal s p r : Int)
  let rawT := evTargets s p hasSite useRoad
  let sorted := evSort (W.extraOr "sortTargets" 1 != 0) rawT held
  let keepT := rawT ++ evSpotKeep s p hasSite
  let protect : Res → Nat := fun r => (keepT.map fun c => evNeed c r).foldl max 0
  let gap := W.extraOr "leaderGap" 0
  let leaderNear := s.turnOrder.any fun q => q != p && decide ((s.pointsOf q : Int) + gap ≥ (G.targetPoints : Int))
  if decide ((ctx.offersThisTurn : Int) < W.extraOr "myOfferLimit" 4) && !leaderNear then
    if let some m := evOffer ctx s p sorted protect then return m
  if W.bankTradeOn != 0 then
    for c in sorted do
      if let some m := evTrade s p c protect (isLegal s p) then return m
    for c in sorted do
      if let some m := evTrade s p c (fun _ => 0) (isLegal s p) then return m
  return Move.endTurn

def evImp (cost : Bundle) (now after : Res → Int) : Int := shortBy cost now - shortBy cost after

def evAccepts {G : GameDef} (ctx : Ctx G) (s : State G) (b : Nat) : List Event :=
  if s.phase != .actions || s.offers.isEmpty then [] else
  let W := ctx.weights
  let needW := W.extraOr "accNeedW" 1
  let goodsW := W.extraOr "accGoodsW" 1
  let margin := W.extraOr "accMargin" 3
  let gap := W.extraOr "leaderGap" 0
  let now : Res → Int := fun r => (bal s b r : Int)
  let ts := evSort true (evTargets s b (hasFreeSite ctx s b) true) now
  let scoreOf (o : Offer) : Int × Int :=
    let after : Res → Int := fun r => now r + evAmt o.give r - evAmt o.get r
    match ts with
    | [] => (0, 0)
    | t :: rest =>
      let first := evImp t now after
      (first, 2 * first + (rest.map fun c => evImp c now after).foldl (· + ·) 0)
  s.offers.filterMap fun o =>
    if o.src != b && (o.to.isNone || o.to == some b) && s.affords b o.get then
      let sc := scoreOf o
      let goods : Int := (bundleTotal o.give : Int) - (bundleTotal o.get : Int)
      let leader := decide ((s.pointsOf o.src : Int) + gap ≥ (G.targetPoints : Int))
      if !leader && decide (sc.1 ≥ 0) && decide (needW * sc.2 + goodsW * goods - margin ≥ 0) then
        some (Event.move b (Move.accept o.id))
      else none
    else none

def evTurn {G : GameDef} (ctx : Ctx G) (s : State G) (seat : Nat) : List Event :=
  if s.currentSeat != some seat then [] else
  let m := if s.phase == .setup then evSetup ctx s seat else evAction ctx s seat
  if m != Move.endTurn then [Event.move seat m, Event.move seat Move.endTurn] else [Event.move seat Move.endTurn]

def evDecide {G : GameDef} (ctx : Ctx G) (s : State G) (seat : Nat) : List Event :=
  if s.phase == .ended then [] else
  let props := (reactions ctx s [seat]).filter fun e => match e with
    | .move _ (.accept _) => false
    | _ => true
  props ++ evAccepts ctx s seat ++ evTurn ctx s seat

def strategy : Strategy :=
  Strategy.ofSeat "s9x0" fun ctx s seat => evDecide ctx s seat

end Evolved.S9x0
