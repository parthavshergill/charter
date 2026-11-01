import Lean.Data.Json
import EventLog
import Server.Util
import Server.Game
import Server.Talk
import Server.Clerk
import Server.Formalize
import Server.Suggest
import Server.Describe

/-!
# The tables this server holds

Each game is a log of JSON events, stored with `lean-eventlog` in `<data>/<code>.db`, and its state is
a fold of `Game.apply` over that log. An event is stored only after the engine accepts it. On start,
every game is replayed from its log. The web server and the headless runner share this file.

Next to each game's log are three others, none of which reaches `Engine.step`:

* `<code>.talk`: table talk (`Server/Talk.lean`).
* `<code>.clerk`: the clerk's memory (`Server/Clerk.lean`), and the laws' descriptions (`Server/Describe.lean`).
* `<code>.seats`: what the Claude seats noted and spent (`Server/Seat.lean`). No route serves it.

A container's disk does not last, so `Server/Mirror.lean` copies all of these to object storage.
-/

namespace CharterServer
open Lean Charter

structure Entry where
  code : String
  log : EventLog.Log String
  events : Array Json := #[]
  game : Game.Game
  talk : Array Talk.Line := #[]
  talkLog : EventLog.Log String

/-- What a Claude seat keeps between its turns. It is private to that seat. -/
structure Mind where
  /-- Notes the seat wrote to itself, oldest first. -/
  notes : Array String := #[]
  /-- The seat's latest draft: its words, what to show it, and the formal text if there is one. -/
  draftWords : String := ""
  draftResult : String := ""
  draftFormal : Option String := none
  /-- The seat has not yet been shown this draft. -/
  draftFresh : Bool := false
  /-- Words to send to the clerk once its other actions have gone to the engine. -/
  pendingDraft : Option String := none
  /-- What became of the seat's latest actions, to tell it next time. -/
  results : List String := []
  /-- The votes, signatures and offers it has already been asked about. -/
  asked : List String := []
  /-- How much of the chronicle it has been shown. -/
  chronicleSeen : Nat := 0
  /-- The turn it last acted in, and how many times it was asked in that turn. -/
  turn : Nat := 0
  callsThisTurn : Nat := 0
  interviewed : Bool := false
  deriving Inhabited

/-- How much the Claude seats at a table have used, for progress lines. -/
structure Usage where
  calls : Nat := 0
  input : Nat := 0
  cacheRead : Nat := 0
  cacheWrite : Nat := 0
  output : Nat := 0
  fallbacks : Nat := 0
  retries : Nat := 0
  deriving Inhabited

/-- Settings for Claude seats. -/
structure SeatSettings where
  model : String := "claude-opus-5-5"
  effort : String := "medium"
  maxTokens : Nat := 12000
  /-- The longest one request can take. -/
  timeoutS : Nat := 120
  /-- The longest one decision can take, with its retries. After this the seat falls back. -/
  budgetS : Nat := 300
  /-- The most requests running at once, across all tables. -/
  concurrency : Nat := 4
  /-- The most times a seat is asked in one turn. After this its turn ends. -/
  callsPerTurn : Nat := 8

structure Ctx where
  table : Std.Mutex (Std.HashMap String Entry)
  webRoot : System.FilePath
  dataDir : System.FilePath
  /-- Games whose driver is running. Used only under the table lock. -/
  botRunning : IO.Ref (Std.HashSet String)
  /-- Pause before each bot action, so humans can watch. -/
  botDelayMs : Nat
  /-- How long the other seats hold their votes on a law, waiting for the people at the table. -/
  voteHoldMs : Nat := 0
  /-- When each open law was first seen by the driver. -/
  holdSince : IO.Ref (Std.HashMap (String × Nat) Nat)
  root : System.FilePath
  /-- The newest draft for each table and seat. A draft never touches the game. -/
  drafts : IO.Ref (Std.HashMap (String × Nat) Formalize.Job)
  nextDraft : IO.Ref Nat
  /-- Each table's clerk log, opened when first used. Draft threads share them, so this lock covers
  every use of a log. -/
  clerkLogs : Std.Mutex (Std.HashMap String (EventLog.Log String))
  /-- Each table's seat log, opened when first used. -/
  seatLogs : Std.Mutex (Std.HashMap String (EventLog.Log String))
  /-- The descriptions of each table's laws. The clerk log holds the finished ones for good. -/
  descriptions : IO.Ref (Std.HashMap String Describe.Book)
  /-- What each Claude seat keeps, by table and seat. -/
  minds : IO.Ref (Std.HashMap (String × Nat) Mind)
  /-- What each table has used. -/
  usage : IO.Ref (Std.HashMap String Usage)
  seat : SeatSettings := {}
  /-- Requests running now. -/
  inFlight : IO.Ref Nat
  /-- No new request before this time: a rate limit was hit. -/
  coolUntil : IO.Ref Nat
  /-- Tables to stop driving, such as one that ran out of time, or one with Claude seats that has just
  come back from a restart and has nobody at it yet. -/
  stopped : IO.Ref (Std.HashSet String)
  /-- Stop driving a table once this round has ended. `charter-sim --stop-round` sets it. -/
  stopRound : Option Nat := none
  /-- The API refused the key or the model, so asking again cannot help. The message says why. -/
  fatal : IO.Ref (Option String)
  /-- Run no drivers at all: this process only shows saved games. -/
  noDrivers : Bool := false
  /-- How long a person has for a turn. 0 means no limit. -/
  humanTurnMs : Nat := 300000
  /-- How long a Claude seat or a bot has for a turn. 0 means no limit. -/
  claudeTurnMs : Nat := 600000
  /-- For each table: the turn the clock is on, and when that turn began. -/
  turnClock : IO.Ref (Std.HashMap String (Nat × Nat))
  /-- The request each Claude seat has running, so the timer can stop a stalled one. -/
  running : IO.Ref (Std.HashMap (String × Nat) Formalize.Job)
  /-- When a person last had a page open at each table. -/
  lastHuman : IO.Ref (Std.HashMap String Nat)
  /-- A table with people pauses after this long with none of them there. 0 turns this off. -/
  awayMs : Nat := 180000

/-- A new context. -/
def Ctx.new (tbl : Std.HashMap String Entry) (root dataDir : System.FilePath) (botDelayMs voteHoldMs : Nat)
    (seat : SeatSettings) (noDrivers : Bool := false) : IO Ctx :=
  return {
    table := ← Std.Mutex.new tbl
    webRoot := root / "web"
    dataDir
    botRunning := ← IO.mkRef {}
    botDelayMs, voteHoldMs
    holdSince := ← IO.mkRef {}
    root
    drafts := ← IO.mkRef {}
    nextDraft := ← IO.mkRef 1
    clerkLogs := ← Std.Mutex.new {}
    seatLogs := ← Std.Mutex.new {}
    descriptions := ← IO.mkRef {}
    minds := ← IO.mkRef {}
    usage := ← IO.mkRef {}
    seat
    inFlight := ← IO.mkRef 0
    coolUntil := ← IO.mkRef 0
    stopped := ← IO.mkRef {}
    fatal := ← IO.mkRef none
    noDrivers
    humanTurnMs := ((← IO.getEnv "CHARTER_TURN_MS").bind String.toNat?).getD 300000
    claudeTurnMs := ((← IO.getEnv "CHARTER_CLAUDE_TURN_MS").bind String.toNat?).getD 600000
    turnClock := ← IO.mkRef {}
    running := ← IO.mkRef {}
    lastHuman := ← IO.mkRef {}
    awayMs := ((← IO.getEnv "CHARTER_TABLE_AWAY_MS").bind String.toNat?).getD 180000 }

/-- Seat settings from the environment. -/
def seatSettingsFromEnv : IO SeatSettings := do
  let num (k : String) (d : Nat) : IO Nat := do return ((← IO.getEnv k).bind String.toNat?).getD d
  return {
    model := (← IO.getEnv "CHARTER_SEAT_MODEL").getD "claude-opus-5-5"
    effort := (← IO.getEnv "CHARTER_SEAT_EFFORT").getD "medium"
    maxTokens := ← num "CHARTER_SEAT_MAX_TOKENS" 12000
    timeoutS := ← num "CHARTER_SEAT_TIMEOUT_S" 120
    budgetS := ← num "CHARTER_SEAT_BUDGET_S" 300
    concurrency := ← num "CHARTER_SEAT_CONCURRENCY" 4
    callsPerTurn := ← num "CHARTER_SEAT_CALLS_PER_TURN" 8 }

/-- Validate one event and store it. -/
def commitRaw (ctx : Ctx) (code : String) (mk : Entry → Except String Json) : IO (Except String Entry) :=
  ctx.table.atomically do
    let tbl ← get
    match tbl.get? code with
    | none => return .error s!"no game {code}"
    | some e =>
      match mk e >>= fun ev => (Game.apply e.game ev).map (ev, ·) with
      | .error err => return .error err
      | .ok (ev, g') =>
        discard <| e.log.append ev.compress
        let e' := { e with game := g', events := e.events.push ev }
        set (tbl.insert code e')
        return .ok e'

def findEntry (ctx : Ctx) (code : String) : IO (Option Entry) :=
  ctx.table.atomically do return (← get).get? code

/-- Has this running game finished the round it was told to stop at? -/
def Ctx.pastStopRound (ctx : Ctx) (g : Game.Game) : Bool :=
  match ctx.stopRound, g.state with
  | some n, some s => s.phase != .ended && n < s.round
  | _, _ => false

/-- Is this table waiting for someone? A table pauses when it has people and none of them has been here
for a while, or has never been here since the server started. While it waits, no seat acts and no clock
runs. Friends can stop for an evening and come back. This changes when events are sent, and it changes
no rule, and pausing goes in no log. A table with no people does not pause this way. -/
def isPaused (ctx : Ctx) (code : String) (g : Game.Game) : IO Bool := do
  if (← ctx.stopped.get).contains code then return true
  if ctx.pastStopRound g then return true
  if ctx.awayMs == 0 || g.humanSeats.isEmpty then return false
  match (← ctx.lastHuman.get).get? code with
  | some t => return (← IO.monoMsNow) - t ≥ ctx.awayMs
  | none => return true

def seatOf (e : Entry) (token? : Option String) : Option Nat :=
  token?.bind fun t => (e.game.room.seatOf? t).map (·.1)

/-- The game after its first `n` log entries, for a replay. -/
def gameAt (e : Entry) (n : Nat) : Except String Game.Game := do
  let some first := e.events[0]? | throw "the log is empty"
  let g0 ← Game.create first
  (e.events.toList.drop 1 |>.take (n - 1)).foldlM Game.apply g0

/-- Rebuild a game by replaying its log. -/
def loadGame (dataDir path : System.FilePath) (code : String) : IO (Option Entry) := do
  let log : EventLog.Log String ← EventLog.Log.open path
  let lines ← log.readFrom 0
  let some first := lines[0]? | return none
  let .ok createEv := Json.parse first
    | IO.eprintln s!"[{code}] this saved game was not loaded. Its first event cannot be read."
      return none
  let g0 ← match Game.create createEv with
    | .ok g => pure g
    | .error err =>
      IO.eprintln s!"[{code}] this saved game was not loaded. It could not be created: {err}"
      return none
  let talkLog : EventLog.Log String ← EventLog.Log.open (Talk.logPath dataDir code)
  let talk ← Talk.readAll talkLog
  let mut e : Entry := { code, log, game := g0, events := #[createEv], talk, talkLog }
  for l in lines.toList.drop 1 do
    match Json.parse l >>= fun ev => (Game.apply e.game ev).map (ev, ·) with
    | .error err =>
      IO.eprintln s!"[{code}] this saved game was not loaded. Its log does not replay under the current rules, at event {e.events.size}: {err}"
      return none
    | .ok (ev, g') => e := { e with game := g', events := e.events.push ev }
  return some e

def loadAll (dataDir : System.FilePath) : IO (Std.HashMap String Entry) := do
  let mut tbl : Std.HashMap String Entry := {}
  for f in ← dataDir.readDir do
    if f.fileName.endsWith ".db" then
      let code := (f.fileName.dropEnd 3).toString
      if let some e ← loadGame dataDir f.path code then
        tbl := tbl.insert code e
  return tbl

def randomNat64 : IO Nat := do
  let bs ← randomBytes 8
  return bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Create a table from its first event, and add it. -/
def addGame (ctx : Ctx) (ev : Json) : IO (Except String Entry) := do
  match Game.create ev with
  | .error err => return .error err
  | .ok g =>
    let code := g.room.code
    let log : EventLog.Log String ← EventLog.Log.open (ctx.dataDir / s!"{code}.db")
    discard <| log.append ev.compress
    let talkLog : EventLog.Log String ← EventLog.Log.open (Talk.logPath ctx.dataDir code)
    let e : Entry := { code, log, events := #[ev], game := g, talkLog }
    ctx.table.atomically do modify (·.insert code e)
    return .ok e

/-! ## Table talk -/

/-- Add a line of talk to a table's log. Talk touches nothing in the game. -/
def addTalk (ctx : Ctx) (code kind : String) (by_ : Nat) (to : Option Nat) (text : String) : IO Unit := do
  let text := Talk.clean text
  if text.isEmpty then return
  ctx.table.atomically do
    let tbl ← get
    let some e := tbl.get? code | return
    let l : Talk.Line := { event := e.game.events, kind, by_, to, text }
    discard <| e.talkLog.append (Talk.lineJson l).compress
    set (tbl.insert code { e with talk := e.talk.push l })

/-! ## A table's seat log -/

def seatLogPath (dataDir : System.FilePath) (code : String) : System.FilePath :=
  dataDir / s!"{code}.seats"

/-- Use a table's seat log, opening it first if needed. -/
def withSeatLog {α : Type} (ctx : Ctx) (code : String) (f : EventLog.Log String → IO α) : IO α :=
  ctx.seatLogs.atomically do
    let logs ← get
    match logs.get? code with
    | some log => f log
    | none =>
      let log : EventLog.Log String ← EventLog.Log.open (seatLogPath ctx.dataDir code)
      set (logs.insert code log)
      f log

/-- Add a record to a table's seat log. The record never holds the key. A failure here must not stop
a game. -/
def seatNote (ctx : Ctx) (code : String) (j : Json) : IO Unit := do
  try withSeatLog ctx code fun log => discard <| log.append j.compress
  catch err => IO.eprintln s!"[{code}] seat log: {err}"

/-- Every record in a table's seat log. -/
def seatRecords (ctx : Ctx) (code : String) : IO (Array Json) := do
  let lines ← withSeatLog ctx code fun log => log.readFrom 0
  return lines.filterMap fun l => (Json.parse l).toOption

/-! ## Drafts: English to formal text. Nothing here reaches the engine. -/

def draftingSeats (ctx : Ctx) (code : String) : IO (List Nat) := do
  let all ← ctx.drafts.get
  let mut out : List Nat := []
  for ((c, seat), job) in all.toList do
    if c == code then
      if (← job.state.get).final.isNone then out := seat :: out
  return out

def stopDraft (job : Formalize.Job) : IO Unit := do
  job.cancelled.set true
  (← job.stop.get)

/-- Use a table's clerk log, opening it first if needed. -/
def withClerkLog {α : Type} (ctx : Ctx) (code : String) (f : EventLog.Log String → IO α) : IO α :=
  ctx.clerkLogs.atomically do
    let logs ← get
    match logs.get? code with
    | some log => f log
    | none =>
      let log : EventLog.Log String ← EventLog.Log.open (Clerk.logPath ctx.dataDir code)
      set (logs.insert code log)
      f log

/-- Write down how a draft ended. A draft that was cancelled, or that never got a reply, is left out:
it told the clerk nothing the seat would refer back to. Memory only helps, so a failure to read or
write it never stops a draft. -/
def remember (ctx : Ctx) (code : String) (job : Formalize.Job) : IO Unit := do
  let cancelled ← job.cancelled.get
  let st ← job.state.get
  let some final := st.final | return
  let current ← findEntry ctx code
  let round := match current with
    | some e => (e.game.state.map (·.round)).getD 0
    | none => 0
  let parse (t : String) : Except String Proposal := match current with
    | some e => e.game.parse t
    | none => Rules.parseProposal t
  let note : Option Clerk.Note := match final with
    | .ready formal difference _ =>
      let printed := match parse formal with
        | .ok p => Rules.printProposal p
        | .error _ => formal
      some { seat := job.seat, round, words := st.suggestedWords.getD job.words, formal := some printed, difference
             suggested := job.suggest, why := st.why }
    | .refused why =>
      -- A suggestion that came to nothing has no words to remember.
      if job.suggest then none else some { seat := job.seat, round, words := job.words, refused := some why }
    | .failed _ | .strike _ | .cancelled => none
  if cancelled then return
  if let some n := note then
    try withClerkLog ctx code (Clerk.append · n)
    catch err => IO.eprintln s!"[{code}] clerk log: {err}"

/-! ## Descriptions of laws -/

/-- What is known about the descriptions of this table's laws, with its pack's own words. -/
def bookOf (ctx : Ctx) (code : String) : IO Describe.Book := do
  let book := (← ctx.descriptions.get).getD code {}
  match ← findEntry ctx code with
  | some e => return Describe.withPack e.game.spec book
  | none => return book

private def setDescription (ctx : Ctx) (code key : String) (st : Describe.Status) : IO Unit :=
  ctx.descriptions.modify fun all => all.insert code ((all.getD code {}).insert key st)

/-- Read back what a table's clerk log holds, after a restart. -/
def restoreDescriptions (ctx : Ctx) (code : String) : IO Unit := do
  if !(← (Clerk.logPath ctx.dataDir code).pathExists) then return
  let lines ← withClerkLog ctx code fun log => log.readFrom 0
  for line in lines do
    if let some (key, text) := Describe.recordOfLine line then
      setDescription ctx code key (.ready text)

/-- Ask for a description of a rule Claude wrote, unless it is a deal or the law has one or is getting
one. The law is marked before this returns, so the screen shows it as being written from the start. The
thread reads only the law, and it touches no game. -/
def startDescription (ctx : Ctx) (code formal : String) : IO Unit := do
  let some e ← findEntry ctx code | return
  let .ok (.law L) := e.game.parse formal | return
  let key := Describe.lawKey L
  if (Describe.packWords e.game.spec).any (·.1 == key) then return
  let isNew ← ctx.descriptions.modifyGet fun all =>
    let book := all.getD code {}
    match book.get? key with
    | some .writing | some (.ready _) => (false, all)
    | _ => (true, all.insert code (book.insert key .writing))
  if !isNew then return
  let cfg ← Describe.settings ctx.root
  discard <| IO.asTask (prio := .dedicated) do
    try
      match ← Describe.run cfg code L with
      | .ok text =>
        -- A description that cannot be saved still shows until the server restarts.
        try
          withClerkLog ctx code fun log =>
            discard <| log.append (Describe.recordJson key text cfg.api.model cfg.effort).compress
        catch err => IO.eprintln s!"[{code}] clerk log: {err}"
        setDescription ctx code key (.ready text)
      | .error status => setDescription ctx code key status
    catch err =>
      IO.eprintln s!"[{code}] description: {err}"
      setDescription ctx code key .strike

/-- Start a clerk job for a seat, replacing any it has running. The thread only reads the game. -/
private def startJob (ctx : Ctx) (code : String) (seat : Nat) (words : String) (suggest : Bool)
    (work : Formalize.Job → Formalize.Settings → IO (Option Game.Game) → List Clerk.Note → IO Unit) :
    IO Formalize.Job := do
  if let some old := (← ctx.drafts.get).get? (code, seat) then stopDraft old
  let id ← ctx.nextDraft.modifyGet fun n => (n, n + 1)
  let now ← IO.monoMsNow
  let job : Formalize.Job :=
    { id, seat, words, startedMs := now, table := code
      state := ← IO.mkRef { lastEventMs := now }
      stop := ← IO.mkRef (pure ())
      cancelled := ← IO.mkRef false
      suggest
      onReady := startDescription ctx code }
  ctx.drafts.modify (·.insert (code, seat) job)
  let cfg ← Formalize.settings ctx.root
  let current : IO (Option Game.Game) := do return (← findEntry ctx code).map (·.game)
  discard <| IO.asTask (prio := .dedicated) do
    try
      let notes ← try withClerkLog ctx code Clerk.readNotes
        catch err =>
          IO.eprintln s!"[{code}] clerk log: {err}"
          pure []
      work job cfg current notes
      remember ctx code job
    catch err =>
      -- The message is about a process or a file, and it never holds the key.
      Formalize.strike job s!"{err}"
  return job

/-- Start a draft of a seat's words. -/
def startDraft (ctx : Ctx) (code : String) (seat : Nat) (words : String) : IO Formalize.Job :=
  startJob ctx code seat words false Formalize.run

/-- Ask the clerk to suggest a rule to a seat. This is a draft in every other way: the same state, the
same checks, the same "drafting" signal to the table, and it reaches no engine event. -/
def startSuggest (ctx : Ctx) (code : String) (seat : Nat) : IO Formalize.Job := do
  let talk := match ← findEntry ctx code with
    | some e => e.talk.toList
    | none => []
  startJob ctx code seat "" true fun job cfg current notes => Suggest.run job cfg current talk notes

end CharterServer
