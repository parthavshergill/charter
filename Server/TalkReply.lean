import Server.Seat

/-!
# Replies in table talk

When a person says something, the Claude seats read it and may answer in character. Talk is not a game
event: nothing here sends an event, and nothing here reaches `Engine.step`. A reply request has only a
`say` field (`Seat.talkSchema`), so it has no way to act.

**Who answers, and in what order.**

* Only a person's line starts replies. A Claude seat's line never does, so seats cannot talk in a loop.
* A public line asks the Claude seats one at a time, in turn order, from the seat after the current seat.
  A seat that the line names goes first.
* A private line asks only the seat it was sent to, if that seat is Claude. The answer is private, to the
  sender.
* A seat may stay quiet by answering null. Asking stops when 2 seats have said something public since
  the line. A seat that has already said something public since the line, for example in a game decision,
  is not asked.

**One writer for each table.** Each table has one talk worker thread, and it asks one seat at a time. It
does not wait for the driver, and the driver does not wait for it. When a person says something new, the
seats not yet asked are dropped and the asking starts again from the new line. A request in flight
finishes. Each prompt reads the talk as it is when it is built.

**Limits.** No calls with no API key, after the API refused the key, while the table is paused or when
the game is over. A table makes at most `talkCallsPerRound` reply calls in one round. Each call goes
through `Seat.request`, so spending, the rate limit and the shared slots apply as for a game decision. A
failed reply is quiet: no line, and the writing sign clears.

What a reply prompt holds: the talk rules and the map (`Seat.talkFacts`), the persona, and in
`Seat.talkMessage` the public board as a game decision shows it (round, last roll, each seat's points, hand
and pieces, where the pieces are, laws, deals and proposals), the public talk and this seat's own private
lines. It never holds another seat's private lines, a seat's memory or a private goal.
-/

namespace CharterServer.TalkReply
open Lean Charter CharterServer.Game CharterServer.Player

/-- Asking stops for a public line when this many seats have said something since it. -/
def maxSpeakers : Nat := 2

/-- The Claude seats to ask about line `l`, in order. A private line asks only the seat it went to. A
public line asks every Claude seat but the writer, in turn order from the seat after the current one; seats
that the line names go first. -/
def replyOrder (g : Game) (s : State g.spec.G) (l : Talk.Line) : List Nat :=
  match l.kind, l.to with
  | "private", some t => if g.isClaude t && t != l.by_ then [t] else []
  | "public", _ =>
    let order := s.turnOrder
    let start := ((order.findIdx? (some · == s.currentSeat)).map (· + 1)).getD 0
    let claude := (order.drop start ++ order.take start).filter fun p => g.isClaude p && p != l.by_
    let named := claude.filter fun p => Talk.names l.text (g.nameOf p)
    named ++ claude.filter (!named.contains ·)
  | _, _ => []

/-- May this table make a reply call now? -/
def mayReply (ctx : Ctx) (code : String) : IO Bool := do
  if ctx.noDrivers then return false
  if (← Formalize.settings ctx.root).key.isNone then return false
  if (← ctx.fatal.get).isSome then return false
  let some e ← findEntry ctx code | return false
  let some s := e.game.state | return false
  if s.phase == .ended then return false
  return !(← isPaused ctx code e.game)

/-- Stop asking about line `idx`. If a newer line has taken its place, that line's seats are kept. -/
def stopAsking (ctx : Ctx) (code : String) (idx : Nat) : IO Unit :=
  ctx.talkWork.modify fun all => match all.get? code with
    | some w => if w.line == idx then all.insert code { w with pending := [] } else all
    | none => all

/-- Ask one seat for its answer to line `idx`. It gives the words, or none if the seat stays quiet or the
request fails. -/
def askReply (ctx : Ctx) (code : String) (seat idx : Nat) : IO (Option String) := do
  let some e ← findEntry ctx code | return none
  let g := e.game
  let some s := g.state | return none
  let some l := e.talk[idx]? | return none
  let some persona := (g.personas[seat]?).join | return none
  let rules ← try IO.FS.readFile (ctx.root / "Server" / "talk_rules.md") catch _ => pure ""
  if rules.trimAscii.isEmpty then return none
  let st := { ctx.seat with maxTokens := ctx.seat.talkMaxTokens, effort := ctx.seat.talkEffort }
  let model := ctx.seat.talkModel.getD ctx.seat.model
  let user := Seat.talkMessage (situation g s seat) (← bookOf ctx code) e.talk l
  -- The rules and the map are the same for every seat at the table, so they share one cached block.
  let body := Seat.requestBody st model (rules ++ "\n\n" ++ Seat.talkFacts g.spec) (Seat.personaText persona seat) user Seat.talkSchema
  markSeen ctx code seat e.talk.size
  -- The same context, with the shorter time limits of a talk reply.
  let limit := min ctx.seat.timeoutS ctx.seat.talkTimeoutS
  let quick := { ctx with seat := { ctx.seat with timeoutS := limit, budgetS := min ctx.seat.budgetS ctx.seat.talkTimeoutS } }
  match ← Seat.request quick code seat "talk" body (track := false) with
  | .error _ => return none
  | .ok a => return (Seat.parseSay a.text).toOption.join

/-- Ask one seat about line `idx`, if it should still be asked, and add its answer to the talk. -/
def replyOnce (ctx : Ctx) (code : String) (seat idx : Nat) : IO Unit := do
  if !(← mayReply ctx code) then return ← stopAsking ctx code idx
  let some e ← findEntry ctx code | return
  let g := e.game
  let some s := g.state | return
  let some l := e.talk[idx]? | return
  if l.kind == "public" then
    let since := e.talk.toList.drop (idx + 1)
    let spoke := ((since.filter fun x => x.kind == "public" && g.isClaude x.by_).map (·.by_)).eraseDups
    if spoke.length ≥ maxSpeakers then return ← stopAsking ctx code idx
    if spoke.contains seat then return
  let allowed ← ctx.talkWork.modifyGet fun all =>
    let w := all.getD code {}
    let w := if w.round == s.round then w else { w with round := s.round, calls := 0 }
    let to := if l.kind == "private" then some l.by_ else none
    if w.calls < ctx.seat.talkCallsPerRound then
      (true, all.insert code { w with calls := w.calls + 1, talking := some seat, talkingTo := to })
    else (false, all.insert code w)
  if !allowed then return ← stopAsking ctx code idx
  bumpTalkTick ctx code
  try
    if let some text ← askReply ctx code seat idx then
      if l.kind == "private" then addTalk ctx code "private" seat (some l.by_) text
      else addTalk ctx code "public" seat none text
  finally
    ctx.talkWork.modify fun all => match all.get? code with
      | some w => all.insert code { w with talking := none, talkingTo := none }
      | none => all
    bumpTalkTick ctx code

/-- The talk worker for one table. It asks the pending seats one at a time, and it stops when none is left.
It stops inside the same update that a new line uses to see whether a worker runs, so a line is never left
with no worker. -/
partial def worker (ctx : Ctx) (code : String) : IO Unit := do
  let next ← ctx.talkWork.modifyGet fun all =>
    let w := all.getD code {}
    match w.pending with
    | [] => (none, all.insert code { w with running := false })
    | p :: rest => (some (p, w.line), all.insert code { w with pending := rest })
  let some (seat, idx) := next | return
  try replyOnce ctx code seat idx
  catch err => IO.eprintln s!"[{code}] talk: {err}"
  worker ctx code

/-- A line was added at place `idx` in the talk. If a person said it, the seats that should answer are
queued in place of any still waiting, and the worker starts if it is not running. -/
def onLine (ctx : Ctx) (code : String) (idx : Nat) : IO Unit := do
  let some e ← findEntry ctx code | return
  let some l := e.talk[idx]? | return
  if !e.game.isHuman l.by_ then return
  let some s := e.game.state | return
  let order := if ← mayReply ctx code then replyOrder e.game s l else []
  let start ← ctx.talkWork.modifyGet fun all =>
    let w := all.getD code {}
    let w := { w with line := idx, pending := order }
    if w.running || order.isEmpty then (false, all.insert code w)
    else (true, all.insert code { w with running := true })
  if start then
    discard <| IO.asTask (prio := .dedicated) do
      try worker ctx code
      catch err =>
        IO.eprintln s!"[{code}] talk worker: {err}"
        ctx.talkWork.modify fun all => match all.get? code with
          | some w => all.insert code { w with running := false, pending := [], talking := none, talkingTo := none }
          | none => all

end CharterServer.TalkReply
