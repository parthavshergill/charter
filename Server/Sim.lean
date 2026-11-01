import Lean.Data.Json
import EventLog
import Server.Util
import Server.Table
import Server.Driver
import Server.Persona
import Server.PreviewCheck

/-!
`charter-sim`: complete games with no browser.

It uses the same tables and the same driver as the server, with no HTTP. Each run has its own folder,
which is a normal data folder, so `make spectate` can open it. For each game the folder holds the event
log, talk, clerk memory and seat log, as they were written during play. At the end of a game it also
writes them as `.jsonl` files, and a `.summary.json`.

Every event is on disk when it is accepted. So a run that stops, for any reason, can go on with
`--resume <folder>`. A game that runs out of wall-clock time stops cleanly, with status `stopped`.
-/

namespace CharterServer.Sim
open Lean Charter CharterServer.Game

structure Options where
  games : Nat := 1
  seats : Nat := 4
  game : String := islandSpec.id
  seed : Option Nat := none
  out : String := "results"
  /-- The kind of each seat, repeated as needed: `claude` or `bot`. -/
  kinds : List String := ["claude"]
  /-- The styles to seat, in order. Empty means the seed chooses. -/
  personas : List String := []
  maxMinutes : Nat := 360
  resume : Option String := none
  /-- Check that the bots still choose what this saved game's bots chose. -/
  checkBotLog : Option String := none
  /-- Check law previews against what the engine does, in real games. -/
  checkPreviews : Bool := false

def parseArgs : List String → Options → Except String Options
  | [], o => .ok o
  | "--games" :: n :: r, o => parseArgs r { o with games := n.toNat?.getD o.games }
  | "--seats" :: n :: r, o => parseArgs r { o with seats := n.toNat?.getD o.seats }
  | "--game" :: g :: r, o => parseArgs r { o with game := g }
  | "--seed" :: n :: r, o => parseArgs r { o with seed := n.toNat? }
  | "--out" :: d :: r, o => parseArgs r { o with out := d }
  | "--kinds" :: k :: r, o => parseArgs r { o with kinds := k.splitOn "," }
  | "--personas" :: k :: r, o => parseArgs r { o with personas := k.splitOn "," }
  | "--max-minutes" :: n :: r, o => parseArgs r { o with maxMinutes := n.toNat?.getD o.maxMinutes }
  | "--resume" :: d :: r, o => parseArgs r { o with resume := some d }
  | "--check-bot-log" :: f :: r, o => parseArgs r { o with checkBotLog := some f }
  | "--check-previews" :: r, o => parseArgs r { o with checkPreviews := true }
  | x :: _, _ => .error s!"unknown option {x}"

/-- A number fixed by the seed and an index. -/
def derive (seed : Nat) (i : Nat) : Nat :=
  (scramble (UInt64.ofNat seed + UInt64.ofNat i * 0x9E3779B97F4A7C15)).toNat

/-- The time now, for a folder name. -/
def stamp : IO String := do
  let r ← IO.Process.output { cmd := "date", args := #["+%Y%m%d-%H%M%S"] }
  return r.stdout.trimAscii.toString

/-! ## Setting a table -/

/-- Create a table and seat it. Everything random comes from the seed, and goes in the log. -/
def seatTable (ctx : Ctx) (o : Options) (seed : Nat) : IO (Except String String) := do
  let code ← randomCode
  let personaSeed := derive seed 1
  let create := Json.mkObj
    [ ("t", "create"), ("code", code), ("seats", toJson o.seats), ("game", o.game)
    , ("_serverSeed", toJson (derive seed 0)), ("_personaSeed", toJson personaSeed)
    , ("_runSeed", toJson seed) ]
  match ← addGame ctx create with
  | .error err => return .error err
  | .ok _ =>
    let personas := Persona.pick (UInt64.ofNat personaSeed) o.seats o.personas
    let botNames := Bots.botNames
    for i in List.range o.seats do
      let kind := o.kinds.getD (i % o.kinds.length) "claude"
      let persona := personas.getD i default
      let name := if kind == "claude" then persona.name else s!"Bot {botNames.getD i s!"{i}"}"
      let base : List (String × Json) :=
        [ ("t", "join"), ("name", name), ("kind", kind), ("_token", toString (derive seed (100 + i)))
        , ("nonce", toJson (derive seed (200 + i))) ]
      let extra : List (String × Json) := if kind == "claude" then [("_persona", Persona.toJson' persona)] else []
      match ← commitRaw ctx code fun _ => .ok (Json.mkObj (base ++ extra)) with
      | .error err => return .error err
      | .ok _ => pure ()
    match ← commitRaw ctx code fun _ => .ok (Json.mkObj [("t", "start")]) with
    | .error err => return .error err
    | .ok _ => return .ok code

/-! ## Writing a game out -/

def writeLines (path : System.FilePath) (lines : List String) : IO Unit :=
  IO.FS.writeFile path ("\n".intercalate lines ++ "\n")

/-- What the seat log says each seat used. -/
def seatTotals (records : Array Json) (seat : Nat) : Json :=
  let mine := records.toList.filter fun r => jNat r "seat" == some seat
  let calls := mine.filter fun r => jStr r "k" == some "call"
  let drafts := mine.filter fun r => jStr r "k" == some "draft"
  let spent := calls ++ drafts
  let sum (k : String) : Nat := (spent.map fun r => (jNat r k).getD 0).sum
  let count (k : String) : Nat := (mine.filter fun r => jStr r "k" == some k).length
  Json.mkObj
    [ ("calls", toJson calls.length), ("drafts", toJson drafts.length)
    , ("clerkCalls", toJson ((drafts.map fun r => (jNat r "attempts").getD 0).sum))
    , ("input", toJson (sum "input")), ("cacheRead", toJson (sum "cacheRead"))
    , ("cacheWrite", toJson (sum "cacheWrite")), ("output", toJson (sum "output"))
    , ("apiMs", toJson (sum "ms"))
    , ("refused", toJson (count "refused")), ("fallbacks", toJson (count "fallback"))
    , ("notes", toJson (count "note")) ]

/-- Write a game's files. The key is in none of them. -/
def writeOut (ctx : Ctx) (code : String) (status : String) (ranMs : Nat) : IO Json := do
  seatNote ctx code (Json.mkObj [("k", "run"), ("ms", toJson ranMs), ("status", status)])
  let some e ← findEntry ctx code | return Json.null
  let g := e.game
  let records ← seatRecords ctx code
  let dir := ctx.dataDir
  writeLines (dir / s!"{code}.events.jsonl") (e.events.toList.map fun j => (stripPrivate j).compress)
  writeLines (dir / s!"{code}.talk.jsonl") (e.talk.toList.map fun l => (Talk.lineJson l).compress)
  writeLines (dir / s!"{code}.seats.jsonl") (records.toList.map (·.compress))
  let wallMs := (records.toList.filterMap fun r =>
    if jStr r "k" == some "run" then jNat r "ms" else none).sum
  let seats := (List.range g.room.filled).map fun i =>
    let persona := match (g.personas[i]?).join with
      | some p => Persona.toJson' p
      | none => Json.null
    Json.mkObj
      [ ("seat", toJson i), ("name", g.nameOf i), ("kind", g.kinds[i]?.getD "?"), ("persona", persona)
      , ("points", toJson ((g.state.map (·.pointsOf i)).getD 0))
      , ("used", seatTotals records i) ]
  let total (k : String) : Nat :=
    (((List.range g.room.filled).map (seatTotals records)).map fun t => (jNat t k).getD 0).sum
  let first := e.events[0]?.getD Json.null
  let summary := Json.mkObj
    [ ("code", code), ("status", status), ("game", g.spec.id)
    , ("runSeed", toJson (jNat first "_runSeed")), ("diceSeed", toJson g.serverSeed.toNat)
    , ("personaSeed", toJson (jNat first "_personaSeed"))
    , ("model", ctx.seat.model), ("effort", ctx.seat.effort)
    , ("round", toJson ((g.state.map (·.round)).getD 0))
    , ("phase", (g.state.map (fun s => View.phaseText s.phase)).getD "lobby")
    , ("winner", toJson ((g.state.bind (·.winner))))
    , ("events", toJson g.events), ("talkLines", toJson e.talk.size)
    , ("wallMs", toJson wallMs)
    , ("laws", toJson ((g.state.map (·.laws.length)).getD 0))
    , ("dealsStarted", toJson ((g.state.map (·.dealsStarted)).getD 0))
    , ("calls", toJson (total "calls")), ("clerkCalls", toJson (total "clerkCalls"))
    , ("input", toJson (total "input")), ("cacheRead", toJson (total "cacheRead"))
    , ("cacheWrite", toJson (total "cacheWrite")), ("output", toJson (total "output"))
    , ("refused", toJson (total "refused")), ("fallbacks", toJson (total "fallbacks"))
    , ("seats", Json.arr seats.toArray) ]
  IO.FS.writeFile (dir / s!"{code}.summary.json") (summary.pretty ++ "\n")
  return summary

/-! ## Running -/

def progressLine (ctx : Ctx) (code : String) : IO String := do
  let some e ← findEntry ctx code | return s!"[{code}] gone"
  let u := (← ctx.usage.get).getD code {}
  let where_ := match e.game.state with
    | some s => s!"round {s.round}, turn of seat {s.currentSeat.getD 0}, points {s.turnOrder.map s.pointsOf}, laws {s.laws.length}"
    | none => "lobby"
  return s!"[{code}] {where_}; {e.game.events} events, {e.talk.size} talk lines; {u.calls} calls, {u.input}+{u.cacheRead}+{u.cacheWrite} in, {u.output} out; {u.retries} retries, {u.fallbacks} fallbacks"

/-- Drive these tables to the end, or to their time limit. Returns false if any of them did not end. -/
def runTables (ctx : Ctx) (codes : List String) (maxMinutes : Nat) : IO Bool := do
  let start ← IO.monoMsNow
  let limit := maxMinutes * 60000
  startTurnTimer ctx
  for code in codes do kickBots ctx code
  let out ← IO.getStdout
  let mut lastLine := start
  let mut done : List String := []
  let mut ok := true
  repeat
    IO.sleep 500
    let now ← IO.monoMsNow
    let running ← ctx.table.atomically do return (← ctx.botRunning.get)
    if let some why ← ctx.fatal.get then
      IO.eprintln s!"stopping: {why}"
      for code in codes do ctx.stopped.modify (·.insert code)
    if now - start > limit then
      for code in codes do
        if !(done.contains code) then ctx.stopped.modify (·.insert code)
    for code in codes do
      if !(done.contains code) && !running.contains code then
        done := code :: done
        let some e ← findEntry ctx code | continue
        let ended := match e.game.state with
          | some s => s.phase == .ended
          | none => false
        let stopped := (← ctx.stopped.get).contains code
        let status := if ended then "finished" else if stopped then "stopped" else "stuck"
        if !ended then ok := false
        let summary ← writeOut ctx code status (now - start)
        IO.println s!"[{code}] {status}: {summary.pretty}"
        out.flush
    if done.length == codes.length then break
    if now - lastLine > 30000 then
      lastLine := now
      for code in codes do
        if !(done.contains code) then
          IO.println (← progressLine ctx code)
      out.flush
  return ok

/-- Replay a saved game of bots, and check that at each step the bots still choose the same event. -/
def checkBotLog (path : String) : IO Bool := do
  let lines := (← IO.FS.lines path).toList.filter (!·.isEmpty)
  let some first := lines.head? | return false
  let .ok j0 := Json.parse first | return false
  let .ok g0 := Game.create j0 | return false
  let mut g := g0
  let mut n : Nat := 1
  for l in lines.drop 1 do
    let .ok ev := Json.parse l | return false
    if g.state.isSome then
      match Player.nextRuleEvent g with
      | some mine =>
        if mine.compress != ev.compress then
          IO.println s!"event {n}: the log says {ev.compress}, and the bots now choose {mine.compress}"
          return false
      | none =>
        IO.println s!"event {n}: the log says {ev.compress}, and the bots now choose nothing"
        return false
    match Game.apply g ev with
    | .ok g' => g := g'
    | .error err =>
      IO.println s!"event {n}: {err}"
      return false
    n := n + 1
  IO.println s!"the bots chose the same {n} events as the saved game"
  return true

/-- A context for the runner. Rate limits can make a turn slow, and no person is waiting, so a Claude
seat gets more time for a turn here than at a table with people. -/
def simCtx (tbl : Std.HashMap String Entry) (root dataDir : System.FilePath) (seat : SeatSettings) : IO Ctx := do
  let ctx ← Ctx.new tbl root dataDir 0 0 seat
  let turnMs := ((← IO.getEnv "CHARTER_CLAUDE_TURN_MS").bind String.toNat?).getD 1500000
  return { ctx with claudeTurnMs := turnMs }

def run (o : Options) : IO UInt32 := do
  if let some path := o.checkBotLog then
    return if ← checkBotLog path then 0 else 1
  if o.checkPreviews then
    return if ← PreviewCheck.run then 0 else 1
  let root : System.FilePath := (← IO.getEnv "CHARTER_ROOT").getD "."
  let seat ← seatSettingsFromEnv
  let seat := { seat with budgetS := ((← IO.getEnv "CHARTER_SEAT_BUDGET_S").bind String.toNat?).getD 900 }
  match o.resume with
  | some dir =>
    let dataDir : System.FilePath := dir
    let tbl ← loadAll dataDir
    let ctx ← simCtx tbl root dataDir seat
    let codes := tbl.toList.filterMap fun (code, e) =>
      match e.game.state with
      | some s => if s.phase == .ended then none else some code
      | none => none
    if codes.isEmpty then
      IO.println s!"{dir}: every game here has ended"
      return 0
    for code in codes do Seat.restoreMinds ctx code
    IO.println s!"resuming {codes} in {dir}"
    return if ← runTables ctx codes o.maxMinutes then 0 else 1
  | none =>
    if !(gameSpecs.any (·.id == o.game)) then
      IO.eprintln s!"there is no game called {o.game}"
      return 1
    if o.kinds.contains "claude" && (← Formalize.settings root).key.isNone then
      IO.eprintln "no API key: set ANTHROPIC_API_KEY, or CHARTER_ENV_FILE to a file that has it"
      return 1
    let seed ← match o.seed with
      | some n => pure n
      | none => randomNat64
    let dataDir : System.FilePath := o.out ++ "/" ++ (← stamp) ++ s!"-s{seed % 100000}"
    IO.FS.createDirAll dataDir
    let ctx ← simCtx {} root dataDir seat
    let mut codes : List String := []
    for i in List.range o.games do
      match ← seatTable ctx o (derive seed (1000 + i)) with
      | .error err =>
        IO.eprintln s!"could not set a table: {err}"
        return 1
      | .ok code => codes := codes ++ [code]
    IO.println s!"run seed {seed}, model {seat.model}, effort {seat.effort}, {o.games} games in {dataDir}"
    IO.println s!"tables: {codes}"
    (← IO.getStdout).flush
    let ok ← runTables ctx codes o.maxMinutes
    IO.println s!"results are in {dataDir}"
    IO.println s!"to watch: make spectate RESULTS={dataDir}"
    return if ok then 0 else 1

end CharterServer.Sim

open CharterServer.Sim in
def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error err =>
    IO.eprintln err
    return 2
  | .ok o =>
    let code ← run o
    (← IO.getStdout).flush
    -- The turn timer's thread runs for as long as the process does, so leave at once.
    IO.Process.exit code.toUInt8
