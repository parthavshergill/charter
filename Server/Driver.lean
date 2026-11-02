import Server.Table
import Server.Player
import Server.Seat
import Server.View

/-!
# The driver

One thread per table plays every seat that is not a person. It treats them all as `Player`s. Rule-based
seats answer at once. Claude seats take time, so those with something to answer out of turn are asked
together, and the seat whose turn it is is asked after them. Every event goes through `commitRaw`, so
through `Engine.step`.

**Vote pacing.** A person must get a say. While any person at the table has not voted on an open law,
and the time limit has not passed, no other seat acts at all. So a law cannot pass before that person
has voted, and it cannot lapse while they read it. This changes when events are sent, and it changes
no rule. A table with no people, or a limit of 0, does not wait.

**Pausing.** A table whose people have all gone away waits for them: see `isPaused`. No seat acts and
no clock runs, and the turn in progress gets a whole new deadline when someone returns. If even one
person is there the table is not paused, and the timer ends the turn of a seat that is idle.

**The turn timer.** Each turn has a deadline, kept by the server, and only `timerLoop` sends
`forceEndTurn`. No client can send it. So "the timer ended the turn" in the chronicle is true, and a
rival cannot end your turn. Commandment IX says the timer can always end a turn, and
`Charter/Constitution.lean` lists who may send this event as something the server must get right. The
clock is not in the log, so a restart gives the turn in progress a full new deadline.

Nothing can stall a table. A Claude seat is asked a bounded number of times in a turn, and then a safe
action is chosen for it. The timer ends the turn of any seat that passes its deadline, and it stops
that seat's running request.
-/

namespace CharterServer
open Lean Charter CharterServer.Game CharterServer.Player

/-- How long a bot waits before this action, in steps of the base delay. A person must be able to see
each vote land. Pacing only: it changes no rule. -/
def pauseSteps (ev : Option Json) : Nat :=
  match ev with
  | some j =>
    match jStr j "t" with
    | some "vote" => 3
    | some "sign" => 4
    | some "move" =>
      match (jField j "move").bind (jStr · "t") with
      | some "endTurn" => 2
      | _ => 1
    | _ => 1
  | _ => 1

/-- The player in a seat. -/
def playerOf (ctx : Ctx) (code : String) (g : Game) (seat : Nat) : Player :=
  if g.isClaude seat then Seat.claudePlayer ctx code seat
  else if g.isBot seat then Player.botSeat
  else Player.human

/-- Which open laws are being held for the people at the table. The clock for a law starts when the
driver first sees it. -/
def heldLaws (ctx : Ctx) (code : String) (g : Game) : IO (List Nat) := do
  if ctx.voteHoldMs == 0 then return []
  let humans := g.humanSeats
  if humans.isEmpty then return []
  let some s := g.state | return []
  let now ← IO.monoMsNow
  let mut held : List Nat := []
  for p in s.openProposals do
    match p.body with
    | .deal _ => pure ()
    | .law _ =>
      if humans.any fun h => !(p.votes.any (·.1 == h)) then
        let since := (← ctx.holdSince.get).getD (code, p.id) now
        ctx.holdSince.modify (·.insert (code, p.id) since)
        if now - since < ctx.voteHoldMs then held := p.id :: held
  return held

/-- Claude seats, other than the one whose turn it is, with something new to answer. -/
def reactors (ctx : Ctx) (code : String) (g : Game) : IO (List Nat) := do
  let some s := g.state | return []
  if s.phase == .ended then return []
  let mut out : List Nat := []
  for seat in g.claudeSeats do
    if s.currentSeat != some seat then
      if Seat.hasNews (situation g s seat) (← Seat.getMind ctx code seat) then
        out := out ++ [seat]
  return out

/-- Claude seats still to be asked what they thought, once the game is over. -/
def toInterview (ctx : Ctx) (code : String) (g : Game) : IO (List Nat) := do
  let some s := g.state | return []
  if s.phase != .ended then return []
  if (← Formalize.settings ctx.root).key.isNone then return []
  let mut out : List Nat := []
  for seat in g.claudeSeats do
    if !(← Seat.getMind ctx code seat).interviewed then out := out ++ [seat]
  return out

/-- Is there anything for the driver to do at this table? -/
def hasWork (ctx : Ctx) (code : String) (g : Game) : IO Bool := do
  if ← isPaused ctx code g then return false
  let some s := g.state | return false
  if s.phase == .ended then return !(← toInterview ctx code g).isEmpty
  if !(← heldLaws ctx code g).isEmpty then return true
  if (nextRuleEvent g).isSome then return true
  if !(← reactors ctx code g).isEmpty then return true
  match s.currentSeat with
  | some p => return g.isClaude p
  | none => return false

/-- Commit one event chosen by a player, and tell the player what the engine said. -/
def commitFor (ctx : Ctx) (code : String) (player : Player) (ev : Json) : IO Bool := do
  let before ← findEntry ctx code
  match ← commitRaw ctx code fun _ => .ok ev with
  | .ok _ =>
    player.told ev none
    return true
  | .error err =>
    let why := match before with
      | some e => View.explain e.game ev err
      | none => err
    player.told ev (some why)
    return false

/-- Ask one slow seat, commit what it chose, and let it finish up. A move chosen for a turn that has
since ended is not carried out: it could land on a later turn of the same seat. -/
def askSeat (ctx : Ctx) (code : String) (seat : Nat) : IO Unit := do
  let some e ← findEntry ctx code | return
  let some s := e.game.state | return
  let player := playerOf ctx code e.game seat
  let turn := s.turnsTaken
  match ← player.choose (situation e.game s seat) with
  | .wait => pure ()
  | .act events =>
    for ev in events do
      let now := (← findEntry ctx code).bind fun x => x.game.state.map (·.turnsTaken)
      if jStr ev "t" == some "move" && now != some turn then
        player.told ev (some "That turn was over before this reached the table.")
      else
        discard <| commitFor ctx code player ev
  player.after

/-- Ask several slow seats at once, and wait for all of them. -/
def askTogether (ctx : Ctx) (code : String) (seats : List Nat) : IO Unit := do
  let tasks ← seats.mapM fun seat =>
    IO.asTask (prio := .dedicated) (askSeat ctx code seat)
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error err => IO.eprintln s!"[{code}] seat: {err}"

/-- Ask the seat whose turn it is. A seat that has been asked too often has its turn ended for it. -/
def askTurnSeat (ctx : Ctx) (code : String) (seat : Nat) : IO Unit := do
  let some e ← findEntry ctx code | return
  let some s := e.game.state | return
  let m ← Seat.getMind ctx code seat
  let calls := if m.turn == s.turnsTaken then m.callsThisTurn else 0
  Seat.modifyMind ctx code seat fun x => { x with turn := s.turnsTaken, callsThisTurn := calls + 1 }
  if calls < ctx.seat.callsPerTurn then
    askSeat ctx code seat
  else
    seatNote ctx code <| Json.mkObj
      [("k", "fallback"), ("seat", toJson seat), ("event", toJson e.game.events), ("why", "asked too often this turn")]
    let player := playerOf ctx code e.game seat
    let fallback := Seat.fallbackEvents (situation e.game s seat)
    for ev in fallback do
      discard <| commitFor ctx code player ev
    -- If the engine refused all of that, wait a moment. The turn timer ends the turn in the end.
    if let some e' ← findEntry ctx code then
      if let some s' := e'.game.state then
        if s'.turnsTaken == s.turnsTaken && s'.phase != .ended then IO.sleep 1000

/-- The driver for one table. It stops, inside the lock, only when there is nothing to do. -/
partial def driverLoop (ctx : Ctx) (code : String) : IO Unit := do
  let some e ← findEntry ctx code | return
  let g := e.game
  let again : IO Unit := driverLoop ctx code
  -- A paused table falls through to the check at the end. That check takes the lock, as `kickBots`
  -- does, so a person who returns just as this thread stops still gets a driver.
  if !(← isPaused ctx code g) then
    match g.state with
    | none => pure ()
    | some s =>
      if s.phase == .ended then
        let seats ← toInterview ctx code g
        if !seats.isEmpty then
          let tasks ← seats.mapM fun seat => IO.asTask (prio := .dedicated) (Seat.interview ctx code seat)
          for t in tasks do discard <| IO.wait t
          return ← again
      else if !(← heldLaws ctx code g).isEmpty then
        IO.sleep 100
        return ← again
      else
        let mem ← Policy.memoryOf code
        let rule := nextRuleEvent g mem
        let commitRule : IO Bool := do
          if ctx.botDelayMs > 0 then
            IO.sleep (ctx.botDelayMs * pauseSteps rule).toUInt32
          if ← isPaused ctx code g then return false
          let before ← findEntry ctx code
          let r ← commitRaw ctx code fun e => match nextRuleEvent e.game mem with
            | some ev => .ok ev
            | none => .error "no bot move"
          -- The policy bot's memory moves on only for the move it chose in the game it saw.
          if let (.ok _, some b) := (r, before) then
            if let some ev := nextRuleEvent b.game mem then Policy.recordCommit code b.game ev
          return r.isOk
        match rule with
        | some ev =>
          if isReaction ev then
            if ← commitRule then return ← again
        | none => pure ()
        let seats ← reactors ctx code g
        if !seats.isEmpty then
          askTogether ctx code seats
          return ← again
        match rule with
        | some _ =>
          if ← commitRule then return ← again
        | none =>
          match s.currentSeat with
          | some p =>
            if g.isClaude p then
              askTurnSeat ctx code p
              return ← again
          | none => pure ()
  let stop ← ctx.table.atomically do
    let more ← match (← get).get? code with
      | some e => hasWork ctx code e.game
      | none => pure false
    if !more then ctx.botRunning.modify (·.erase code)
    return !more
  if !stop then again

/-- Start the driver for a table, unless it is running or there is nothing to do. -/
def kickBots (ctx : Ctx) (code : String) : IO Unit := do
  if ctx.noDrivers then return
  let go ← ctx.table.atomically do
    if (← ctx.botRunning.get).contains code then return false
    let some e := (← get).get? code | return false
    if !(← hasWork ctx code e.game) then return false
    ctx.botRunning.modify (·.insert code)
    return true
  if go then
    discard <| IO.asTask (prio := .dedicated) do
      try driverLoop ctx code
      catch err =>
        IO.eprintln s!"[{code}] driver: {err}"
        ctx.table.atomically do ctx.botRunning.modify (·.erase code)

/-! ## People coming and going -/

/-- One of this table's people has a page open. If they were away, the table plays again, and its
spending counts against them. -/
def markPresent (ctx : Ctx) (code : String) (g : Game) (ip : IO UInt64) : IO Unit := do
  let paused ← isPaused ctx code g
  ctx.lastHuman.modify (·.insert code (← IO.monoMsNow))
  if paused then
    Spend.setPayer code (← ip)
    ctx.stopped.modify (·.erase code)
    kickBots ctx code

/-- Waking up must not start spending, so a table with Claude seats waits to be visited. A table with
people waits for one of them, and a table with none waits for anyone watching: see the `view` route.
Other tables with people wait too, because nobody has been at them since this server started, and
`isPaused` says so. A game that is over gets no interview: that belongs to the session it ended in, and
nobody may be there to read it. -/
def holdClaudeTables (ctx : Ctx) : IO Unit := do
  let tables ← ctx.table.atomically do return (← get).toList
  for (code, e) in tables do
    if e.game.claudeSeats.isEmpty then continue
    if e.game.state.any (·.phase == .ended) then
      for seat in e.game.claudeSeats do
        Seat.modifyMind ctx code seat fun m => { m with interviewed := true }
    else
      ctx.stopped.modify (·.insert code)

/-! ## The turn timer -/

/-- How long this seat has for a turn. 0 means no limit. -/
def turnLimitMs (ctx : Ctx) (g : Game) (seat : Nat) : Nat :=
  if g.isHuman seat then ctx.humanTurnMs else ctx.claudeTurnMs

/-- How long the current turn has left, if it has a deadline. For the screen only. -/
def turnLeftMs (ctx : Ctx) (g : Game) (code : String) : IO (Option Nat) := do
  let some s := g.state | return none
  if s.phase == .ended then return none
  let some seat := s.currentSeat | return none
  let limit := turnLimitMs ctx g seat
  if limit == 0 then return none
  match (← ctx.turnClock.get).get? code with
  | some (turn, since) =>
    if turn == s.turnsTaken then return some (limit - min limit ((← IO.monoMsNow) - since))
    return some limit
  | none => return some limit

/-- Look at every table once: start the clock on a new turn, and end a turn past its deadline. The
event is built inside the lock, for the turn that is still running then. -/
def timerTick (ctx : Ctx) : IO Unit := do
  let tables ← ctx.table.atomically do return (← get).toList.map fun (c, e) => (c, e.game)
  let now ← IO.monoMsNow
  for (code, g) in tables do
    if ← isPaused ctx code g then
      -- No clock runs while a table waits. A turn or a vote gets its whole time when someone returns.
      if (← ctx.turnClock.get).contains code then
        ctx.turnClock.modify (·.erase code)
        ctx.holdSince.modify (·.filter fun k _ => k.1 != code)
      continue
    let some s := g.state | continue
    if s.phase == .ended then
      ctx.turnClock.modify (·.erase code)
      continue
    let some seat := s.currentSeat | continue
    match (← ctx.turnClock.get).get? code with
    | some (turn, since) =>
      if turn != s.turnsTaken then
        ctx.turnClock.modify (·.insert code (s.turnsTaken, now))
      else
        let limit := turnLimitMs ctx g seat
        if limit != 0 && now - since ≥ limit then
          let r ← commitRaw ctx code fun e =>
            match e.game.state with
            | some s' =>
              if s'.turnsTaken == turn && s'.phase != .ended then .ok (Json.mkObj [("t", "forceEndTurn")])
              else .error "the turn moved on"
            | none => .error "the game has not started"
          if r.isOk then
            if let some job := (← ctx.running.get).get? (code, seat) then
              job.cancelled.set true
              (← job.stop.get)
            kickBots ctx code
    | none => ctx.turnClock.modify (·.insert code (s.turnsTaken, now))

/-- The server's own timer. It is the only thing that ever sends `forceEndTurn`. -/
partial def timerLoop (ctx : Ctx) : IO Unit := do
  let limits := [ctx.humanTurnMs, ctx.claudeTurnMs].filter (· != 0)
  let tick := min 250 (limits.foldl min 250)
  IO.sleep (max tick 20).toUInt32
  try timerTick ctx
  catch err => IO.eprintln s!"turn timer: {err}"
  timerLoop ctx

/-- Start the turn timer, unless this process only shows saved games. -/
def startTurnTimer (ctx : Ctx) : IO Unit := do
  if ctx.noDrivers then return
  discard <| IO.asTask (prio := .dedicated) (timerLoop ctx)

def commit (ctx : Ctx) (code : String) (ev : Json) : IO (Except String Entry) := do
  let r ← commitRaw ctx code fun _ => .ok ev
  if r.isOk then kickBots ctx code
  return r

/-- Start a game once every seat is taken. -/
def startIfFull (ctx : Ctx) (code : String) : IO Unit := do
  let some e ← findEntry ctx code | return
  if e.game.room.isFull && !e.game.room.started then
    discard <| commit ctx code (Json.mkObj [("t", "start")])

end CharterServer
