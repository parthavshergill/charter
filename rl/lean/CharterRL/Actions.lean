import CharterRL.Tables

/-!
# Actions and the mask

An action is a number. `decode` turns it into an event, and `encode` turns an event back. The mask is exactly
the actions of `legal`, and `legal` asks the engine about each one. The only help it takes is `placesWith` and
`setupPlaces`, which skip places no piece could go. `charter-rl-check` tests the result against `Engine.step` on
every action of many states.
-/

namespace CharterRL
open Charter CharterServer CharterServer.Bots

variable {G : GameDef}

/-- What the environment waits for. -/
inductive Decision where
  /-- The game is over, or nothing can happen. -/
  | none
  /-- This seat votes on this law. -/
  | vote (seat id : Nat) (L : Law)
  /-- It is this seat's turn. -/
  | turn (seat : Nat)
  deriving Inhabited

/-- The seat that must decide. -/
def Decision.seat? : Decision → Option Nat
  | .none => Option.none
  | .vote seat _ _ => some seat
  | .turn seat => some seat

/-! ## Placements

A placement has no fixed action. The legal placements of a decision are put in `placeOrder` and the first
`maxPlaceRows` of them get rows of `places`, and actions `actPlace + i`. The order does not depend on names or on
the order a game lists things in, so it is the same under renaming:
1. by placement: replacing a piece, then attaching to one, then a new piece on a spot, then a piece on a link;
2. then by the pips of the spot (for a link, its better free end), most first;
3. then by the spot, or the link's ends, and then by the kind's row. -/

/-- What a placement is, for the order: its placement, its value, where, and its kind's row. -/
def placeKey (ctx : Ctx G) (ep : Episode) (rules : Rules) (free : Array Bool) : Move → Nat × Nat × Nat × Nat × Nat
  | .place k loc =>
    let row := (ep.kindRow? k).getD maxKinds
    let pipsAt (v : Nat) := ctx.board.spotPips.getD v 0
    let cls := match (rules.piece? k).map (·.placement) with
      | some (Placement.upgrade _) => 0
      | some (Placement.attach _) => 1
      | some Placement.spot => 2
      | _ => 3
    match loc with
    | .spot v => (cls, 1000 - pipsAt v, v, 0, row)
    | .link (a, b) =>
      let end_ (v : Nat) := if free.getD v false then pipsAt v else 0
      (cls, 1000 - max (end_ a) (end_ b), min a b, max a b, row)
  | _ => (9, 0, 0, 0, 0)

private def keyLt (a b : Nat × Nat × Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && (a.2.2.1 < b.2.2.1 ||
    (a.2.2.1 == b.2.2.1 && (a.2.2.2.1 < b.2.2.2.1 || (a.2.2.2.1 == b.2.2.2.1 && a.2.2.2.2 < b.2.2.2.2)))))))

/-- Every legal placement of this seat now, in `placeOrder`. Rows of `places` are the first `maxPlaceRows`. -/
def placeList (ctx : Ctx G) (ep : Episode) (s : State G) (seat : Nat) (free reach : Array Bool) : Array Move :=
  let cands := if s.phase == .setup then setupPlaces ctx s seat
    else placesWith ctx s seat (Thunk.pure free) (Thunk.pure reach) fun _ => true
  let ok := (cands.filter fun m => (match m with | .place .. => true | _ => false) && isLegal s seat m).toArray
  let keyed := ok.map fun m => (placeKey ctx ep s.rules free m, m)
  (keyed.qsort fun x y => keyLt x.1 y.1).map (·.2)

/-- The action for this move, if it has one. Offers, accepts and cancels do not, nor a placement without a row. -/
def encodeMove (ep : Episode) (places : Array Move) : Move → Option Nat
  | .endTurn => some actEnd
  | .bankTrade g h => do
    let i ← ep.resRow? g
    let j ← ep.resRow? h
    pure (actBank + i * maxRes + j)
  | .declare r n => do
    let i ← ep.resRow? r
    let l ← declareLevels.findIdx? (· == n)
    pure (actDeclare + i * declareLevels.size + l)
  | m@(.place ..) => do
    let i ← places.findIdx? (· == m)
    if i < maxPlaceRows then pure (actPlace + i) else Option.none
  | _ => Option.none

/-- The action for this event, for this decision. -/
def encode (ep : Episode) (places : Array Move) (d : Decision) : Event → Option Nat
  | .move _ m => match d with
    | .turn _ => encodeMove ep places m
    | _ => Option.none
  | .vote _ id yes => match d with
    | .vote _ want _ => if id == want then some (if yes then actVoteYes else actVoteNo) else Option.none
    | _ => Option.none
  | _ => Option.none

/-- The event for this action, for this decision. `places` is the decision's `placeList`. `none` means this action
is not on offer now, whatever the engine would say: a vote when no vote is due, a move while a vote is due, a
declaration in a game where no law reads one, or a row with nothing in it. -/
def decode (T : Tables) (ep : Episode) (places : Array Move) (d : Decision) (a : Nat) : Option Event :=
  match d with
  | .none => Option.none
  | .vote seat id _ =>
    if a == actVoteNo then some (.vote seat id false)
    else if a == actVoteYes then some (.vote seat id true)
    else Option.none
  | .turn seat =>
    let some' (m : Move) : Option Event := some (.move seat m)
    if a == actEnd then some' .endTurn
    else if a < actBank then Option.none
    else if a < actDeclare then
      let i := a - actBank
      match ep.rowRes[i / maxRes]?, ep.rowRes[i % maxRes]? with
      | some g, some h => some' (.bankTrade g h)
      | _, _ => Option.none
    else if a < actPlace then
      if !T.declares then Option.none else
      let i := a - actDeclare
      match ep.rowRes[i / declareLevels.size]?, declareLevels[i % declareLevels.size]? with
      | some r, some n => some' (.declare r n)
      | _, _ => Option.none
    else if a < actSize then (places[a - actPlace]?).map (.move seat ·)
    else Option.none

/-- Every action on offer now, with its event, by asking the engine. Ending the turn needs no asking: the rules
accept it on a seat's own turn, and theorem `endTurnNow_some` says that it cannot fail. Placements come from
`places`, which `placeList` made by asking the engine about each. -/
def legal (T : Tables) (ep : Episode) (places : Array Move) (s : State G) (d : Decision) : List (Nat × Event) :=
  match d with
  | .none => []
  | .vote seat id _ =>
    [(actVoteNo, Event.vote seat id false), (actVoteYes, Event.vote seat id true)].filter fun x =>
      (Engine.step G s x.2).toOption.isSome
  | .turn seat =>
    let end_ : List (Nat × Event) := if s.isTurnOf seat then [(actEnd, .move seat .endTurn)] else []
    let rows := ((places.toList.take maxPlaceRows).zipIdx).map fun (m, i) => (actPlace + i, Event.move seat m)
    -- In setup, end turn is offered only when nothing can be placed: the engine allows ending a setup turn early,
    -- but that gives up a free opening piece, and policies kept doing it.
    if s.phase == .setup then (if rows.isEmpty then end_ else []) ++ rows else
    let names := ep.rowRes.toList
    let trades := names.flatMap fun g => names.filterMap fun h =>
      if g == h then Option.none else some (Move.bankTrade g h)
    let declares := if T.declares then names.flatMap fun r => declareLevels.toList.map (Move.declare r) else []
    let others := (trades ++ declares).filterMap fun m =>
      if isLegal s seat m then (encodeMove ep places m).map (·, .move seat m) else Option.none
    end_ ++ others ++ rows

/-- The mask of these actions. -/
def maskOf (acts : List (Nat × Event)) : ByteArray :=
  acts.foldl (fun m x => m.set! x.1 1) (ByteArray.mk (Array.replicate actSize 0))

end CharterRL
