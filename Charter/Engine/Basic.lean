import Charter.Words

/-!
# Engine basics

Small helpers that the rest of the engine shares. Each one has one job, so a proof can use one
lemma per helper.

The most important helper is `record`. It is the only place where the books or the journal
change. It posts every entry in full and appends the same entries to the journal, or it rejects
the event. It never moves less than an entry says.
-/

namespace Charter.Engine

variable {G : GameDef}

/-- Post entries in order and write them in the journal. Reject if one cannot be posted. -/
def record (s : State G) (es : List Entry) : Except String (State G) :=
  match s.books.postAll es with
  | some b => .ok { s with books := b, journal := s.journal ++ es }
  | none => .error "an entry cannot be posted in full"

/-- `record`, keeping a table of the books each time the journal passes a multiple of 128. So a read never
walks back through more than a few dozen steps, however long the game has run. -/
def recordFast (s : State G) (es : List Entry) : Except String (State G) :=
  match s.books.postAll es with
  | some b =>
    let n := s.journal.length
    if n / 128 == (n + es.length) / 128 then .ok { s with books := b, journal := s.journal ++ es }
    else
      let t := b.table s.tableKeys
      .ok { s with books := Books.ofTable t b, journal := s.journal ++ es }
  | none => .error "an entry cannot be posted in full"

/-- The faster `record` gives the same result, so the compiler can run it instead. -/
@[csimp] theorem record_eq_recordFast : @record = @recordFast := by
  funext G s es
  simp only [record, recordFast]
  split
  · simp only [Books.ofTable_table]; split <;> rfl
  · rfl

/-- Count an accepted event against the seat that sent it. -/
def countAction (s : State G) (seat : Seat) : State G :=
  { s with
    actionsThisTurn := fun q =>
      if q = seat then s.actionsThisTurn q + 1 else s.actionsThisTurn q
    eventsApplied := s.eventsApplied + 1 }

/-- The seat can act now: it plays in this game, and it has actions left this turn. -/
def canAct (s : State G) (seat : Seat) : Bool :=
  s.turnOrder.contains seat && decide (s.actionsThisTurn seat < maxActionsPerTurn)

/-- The seat with the most points in a list. The earliest in the list wins a tie. -/
def bestSeat (s : State G) (seats : List Seat) : Option Seat :=
  seats.foldl
    (fun best c =>
      match best with
      | none => some c
      | some b => if s.pointsOf b < s.pointsOf c then some c else some b)
    none

/-- End the game early: refund every running deal and clear what is still open. -/
def endGame (s : State G) (w : Seat) : Except String (State G) := do
  let s1 ← record s (s.deals.flatMap s.refundEntries)
  pure { s1 with
    phase := .ended
    winner := some w
    deals := []
    offers := []
    openProposals := [] }

/-- Seats at or above the target, in turn order. -/
def seatsAtTarget (s : State G) : List Seat :=
  s.turnOrder.filter fun p => decide (G.targetPoints ≤ s.pointsOf p)

/-- A seat at or above the target wins at once. Most points wins a tie, then earlier turn order. -/
def checkWin (s : State G) : Except String (State G) :=
  match bestSeat s (seatsAtTarget s) with
  | some w => endGame s w
  | none => .ok s

/-- Run an action for a seat and count it. Reject if the seat cannot act now. -/
def act (s : State G) (seat : Seat) (body : Except String (State G)) : Except String (State G) :=
  if canAct s seat then
    match body with
    | .ok s1 => .ok (countAction s1 seat)
    | .error m => .error m
  else .error "this seat cannot act now"

/-- Like `act`, then look for a winner. Used for moves and votes. -/
def actThenCheckWin (s : State G) (seat : Seat) (body : Except String (State G)) :
    Except String (State G) :=
  match act s seat body with
  | .ok s1 => checkWin s1
  | .error m => .error m

end Charter.Engine
