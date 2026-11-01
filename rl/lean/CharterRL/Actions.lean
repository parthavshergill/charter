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

/-- The action for this move, if it has one. Offers, accepts and cancels do not. -/
def encodeMove (T : Tables) (ep : Episode) : Move → Option Nat
  | .endTurn => some actEnd
  | .bankTrade g h => do
    let i ← ep.resRow? g
    let j ← ep.resRow? h
    pure (actBank + i * maxRes + j)
  | .declare r n => do
    let i ← ep.resRow? r
    let l ← declareLevels.findIdx? (· == n)
    pure (actDeclare + i * declareLevels.size + l)
  | .place k (.spot v) => do
    let row ← ep.kindRow? k
    if row < maxLinkKinds || maxSpots ≤ v then Option.none
    else pure (actSpot + (row - maxLinkKinds) * maxSpots + v)
  | .place k (.link l) => do
    let row ← ep.kindRow? k
    let (_, at_) ← (T.linkFrom.getD l.1 []).find? (·.1 == l.2)
    if maxLinkKinds ≤ row then Option.none else pure (actLink + row * maxLinks + at_)
  | _ => Option.none

/-- The action for this event, for this decision. -/
def encode (T : Tables) (ep : Episode) (d : Decision) : Event → Option Nat
  | .move _ m => match d with
    | .turn _ => encodeMove T ep m
    | _ => Option.none
  | .vote _ id yes => match d with
    | .vote _ want _ => if id == want then some (if yes then actVoteYes else actVoteNo) else Option.none
    | _ => Option.none
  | _ => Option.none

/-- The event for this action, for this decision. `none` means this action is not on offer now, whatever the engine
would say: a vote when no vote is due, a move while a vote is due, a declaration in a game where no law reads one,
or a row with nothing in it. -/
def decode (T : Tables) (ep : Episode) (d : Decision) (a : Nat) : Option Event :=
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
    else if a < actLink then
      if !T.declares then Option.none else
      let i := a - actDeclare
      match ep.rowRes[i / declareLevels.size]?, declareLevels[i % declareLevels.size]? with
      | some r, some n => some' (.declare r n)
      | _, _ => Option.none
    else if a < actSpot then
      let i := a - actLink
      match ep.rowKind[i / maxLinks]?, T.links[i % maxLinks]? with
      | some k, some l => if k == "" then Option.none else some' (.place k (.link l))
      | _, _ => Option.none
    else if a < actSize then
      let i := a - actSpot
      let v := i % maxSpots
      match ep.rowKind[maxLinkKinds + i / maxSpots]? with
      | some k => if k == "" || T.G.map.spotCount ≤ v then Option.none else some' (.place k (.spot v))
      | none => Option.none
    else Option.none

/-- Keep the moves the engine takes, with their actions. -/
private def keep (T : Tables) (ep : Episode) (s : State G) (seat : Nat) (ms : List Move) : List (Nat × Event) :=
  ms.filterMap fun m =>
    if isLegal s seat m then (encodeMove T ep m).map (·, .move seat m) else Option.none

/-- Every action on offer now, with its event, by asking the engine. Ending the turn needs no asking: the rules
accept it on a seat's own turn, and theorem `endTurnNow_some` says that it cannot fail. -/
def legal (T : Tables) (ep : Episode) (ctx : Ctx G) (s : State G) (d : Decision) : List (Nat × Event) :=
  match d with
  | .none => []
  | .vote seat id _ =>
    [(actVoteNo, Event.vote seat id false), (actVoteYes, Event.vote seat id true)].filter fun x =>
      (Engine.step G s x.2).toOption.isSome
  | .turn seat =>
    let end_ : List (Nat × Event) := if s.isTurnOf seat then [(actEnd, .move seat .endTurn)] else []
    if s.phase == .setup then
      end_ ++ keep T ep s seat (setupPlaces ctx s seat)
    else
      let places := placesOf ctx s seat fun _ => true
      let names := ep.rowRes.toList
      let trades := names.flatMap fun g => names.filterMap fun h =>
        if g == h then Option.none else some (Move.bankTrade g h)
      let declares := if T.declares then
          names.flatMap fun r => declareLevels.toList.map (Move.declare r)
        else []
      end_ ++ keep T ep s seat (places ++ trades ++ declares)

/-- The mask of these actions. -/
def maskOf (acts : List (Nat × Event)) : ByteArray :=
  acts.foldl (fun m x => m.set! x.1 1) (ByteArray.mk (Array.replicate actSize 0))

end CharterRL
