import Charter.Engine.Turn
import Charter.Engine.Moves
import Charter.Engine.Proposals

/-!
# The whole game: one event at a time

`step` applies one event or rejects it. Nothing else changes a game.
-/

namespace Charter.Engine

/-- The whole game: apply one event, or reject it. -/
def step (G : GameDef) (s : State G) (e : Event) : Except String (State G) :=
  if s.phase == .ended then .error "the game has ended"
  else
    match e with
    | .forceEndTurn => endTurnNow s
    | .move p .endTurn =>
        if s.isTurnOf p then endTurnNow s else .error "only the current seat can end its turn"
    | .move p m => actThenCheckWin s p (moveBody s p m)
    | .propose seat body => act s seat (proposeBody s seat body)
    | .vote seat id yes => actThenCheckWin s seat (voteBody s seat id yes)
    | .sign seat id => act s seat (signBody s seat id)
    | .exit seat dealId => act s seat (exitBody s seat dealId)

/-- Run a list of events from a new game. A game needs a legal number of seats and at least one
player's nonce, as `Reachable.start` requires. -/
def replay (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (events : List Event) : Except String (State G) :=
  if !(decide (minSeats ≤ seats) && decide (seats ≤ maxSeats)) then
    .error "a game has too few or too many seats"
  else if nonces.isEmpty then .error "a game needs at least one player's nonce"
  else events.foldlM (step G) (initialState G seats serverSeed nonces)

/-! ## Legal moves, for the screen -/

/-- Every place a piece could go on this map. -/
def allLocs (G : GameDef) : List Loc :=
  (List.range G.map.spotCount).map .spot ++ G.map.links.map .link

/-- Moves worth testing for a seat. Offers have free-form contents, so they are not listed. -/
def candidateMoves {G : GameDef} (s : State G) : List Move :=
  let resources := G.resources.map (·.name)
  [Move.endTurn] ++
  (s.rules.pieces.flatMap fun d => (allLocs G).map (.place d.name)) ++
  (resources.flatMap fun give => resources.map (.bankTrade give)) ++
  s.offers.map (fun o => .accept o.id) ++
  s.offers.map (fun o => .cancel o.id)

/-- The moves `step` accepts from this seat now, except offers. `step` adds to the journal and never reads
it, so these tries leave it out. Otherwise each one would copy the whole journal. -/
def legalMoves (G : GameDef) (s : State G) (p : Seat) : List Move :=
  let probe : State G := { s with journal := [] }
  (candidateMoves s).filter fun m => (step G probe (.move p m)).toOption.isSome

end Charter.Engine
