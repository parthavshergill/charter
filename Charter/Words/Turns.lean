import Charter.Words.State

/-!
# What comes after a turn, and how long a game can be

`nextStage` is the single place that says what follows the current turn.
-/

namespace Charter

/-- What comes after the current turn. -/
inductive NextStage where
  /-- Another setup turn, at this position in turn order. -/
  | setupTurn (index : Nat)
  /-- Setup is over, and the first action turn of round 1 starts. -/
  | firstRound
  /-- The next seat plays in the same round, at this position in turn order. -/
  | sameRound (index : Nat)
  /-- The round is over, and the next one starts. -/
  | newRound
  /-- The last round is over. -/
  | gameOver
  deriving Repr, DecidableEq

/-- Setup is two passes in snake order: first to last, then last to first. -/
def setupStage (seats turnsDone : Nat) : NextStage :=
  if turnsDone < seats then .setupTurn turnsDone
  else if turnsDone < 2 * seats then .setupTurn (2 * seats - 1 - turnsDone)
  else .firstRound

/-- What comes after the current turn. -/
def nextStage {G : GameDef} (s : State G) : NextStage :=
  match s.phase with
  | .setup => setupStage s.turnOrder.length (s.turnsTaken + 1)
  | .actions =>
      if s.isLastTurn then
        if G.rounds ≤ s.round then .gameOver else .newRound
      else .sameRound (s.turnIndex + 1)
  | .ended => .gameOver

/-- A new action turn starts after this stage, so the dice roll. -/
def NextStage.rolls : NextStage → Bool
  | .firstRound | .sameRound _ | .newRound => true
  | .setupTurn _ | .gameOver => false

/-- Every turn of a game: two setup passes, then each seat once per round. -/
def maxTurns (G : GameDef) (seats : Nat) : Nat := 2 * seats + G.rounds * seats

/-- Each seat can act a limited number of times per turn, and each turn ends once. -/
def maxEvents (G : GameDef) (seats : Nat) : Nat :=
  maxTurns G seats * (seats * maxActionsPerTurn + 1)

end Charter
