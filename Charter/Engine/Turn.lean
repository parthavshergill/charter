import Charter.Engine.Basic

/-!
# The turn change

This file is written once and used twice: by `step` when a turn really ends, and by
`predictNextTurn` for the preview shown at a vote.

The work has two parts:

1. `turnEntries` computes every payment of the turn change, in order. At a round's end those are
   `State.roundEndEntries`. If a new action turn starts, they end with the whole of that roll.
2. `startNextTurn` changes everything else: who plays, the round, and the dice counters.

`nextStage` says what comes next. It is in the spec, in `Charter/Words/Turns.lean`.
-/

namespace Charter.Engine

variable {G : GameDef}

/-- Every payment of the turn change, if the dice show `roll`. The roll comes last. -/
def turnEntries (s : State G) (roll : Nat) : List Entry :=
  let before := s.entriesBeforeRoll
  if (nextStage s).rolls then before ++ rollEntries (s.afterPosting before) roll else before

/-- Start an action turn: the seat's open proposals expire, and the dice roll. -/
def beginActionTurn (s : State G) (index roll : Nat) : State G :=
  { s with
    phase := .actions
    turnIndex := index
    openProposals := s.openProposals.filter fun p => some p.by_ != s.turnOrder[index]?
    rollsMade := s.rollsMade + 1
    lastRoll := some roll }

/-- Everything a turn change does except the books. `s` already has its entries recorded. -/
def startNextTurn (s : State G) (roll : Nat) : State G :=
  let base : State G :=
    { s with
      turnsTaken := s.turnsTaken + 1
      eventsApplied := s.eventsApplied + 1
      actionsThisTurn := fun _ => 0
      offers := [] }
  match nextStage s with
  | .setupTurn i => { base with turnIndex := i }
  | .firstRound => beginActionTurn base 0 roll
  | .sameRound i => beginActionTurn base i roll
  | .newRound =>
      beginActionTurn
        { base with
          round := s.round + 1
          builtThisRound := []
          declared := fun _ _ => 0
          deals := s.deals.filter fun d => decide (s.round < d.lastRound) }
        0 roll
  | .gameOver =>
      { base with
        phase := .ended
        winner := bestSeat s s.turnOrder
        declared := fun _ _ => 0
        deals := []
        openProposals := [] }

/-- End the current turn. The roll depends only on the seed and on how many rolls came before. -/
def endTurnNow (s : State G) : Except String (State G) :=
  let roll := rollAt G s.seed s.rollsMade
  match record s (turnEntries s roll) with
  | .ok s1 => .ok (startNextTurn s1 roll)
  | .error m => .error m

/-- Every payment the next turn change will make, if the dice show `roll`. -/
def predictNextTurn (_G : GameDef) (s : State _G) (roll : Nat) : List Entry :=
  turnEntries s roll

end Charter.Engine
