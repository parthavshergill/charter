import Lean.Data.Json
import Server.ArenaReference
import Evolved.Pool

/-!
`charter-arena`: many headless games, fast, for the evolution loop.

It reads one JSON object on stdin and writes one JSON line per game, in input order, then a summary line.
See `results/evolve/loop/LEAN_CONTRACT.md`. It has no HTTP, no SQLite, no chronicle and no files, and it does
not import the constitution or the proofs.
-/

namespace CharterServer.Arena
open Lean Charter CharterServer CharterServer.Bots

/-- Every strategy this exe can seat. The reference is for measuring and is not listed. -/
def allStrategies : List Strategy := Evolved.pool ++ [Reference.strategy]

/-! ## The input -/

/-- One named player of the input. -/
structure Entrant where
  key : String
  strategy : Strategy
  /-- The weights it names. All others take their default. -/
  values : List (String × Int)
  deriving Inhabited

/-- One game of the input. -/
structure GameJob where
  seed : Nat
  lineup : List String
  /-- Each seat's place in the list of entrants. -/
  seats : Array Nat
  deriving Inhabited

/-- The whole input. -/
structure Job where
  spec : GameSpec
  seats : Nat
  threads : Nat
  entrants : Array Entrant
  games : Array GameJob
  options : Options
  deriving Inhabited

/-- Read the weights of one entrant. -/
def readValues (key : String) (j : Json) : Except String (List (String × Int)) :=
  match j.getObjVal? "weights" with
  | .error _ => pure []
  | .ok w =>
    match w.getObj? with
    | .error _ => throw s!"the weights of {key} are not an object"
    | .ok kvs =>
      kvs.toList.mapM fun (name, v) =>
        match v.getInt? with
        | .ok i => pure (name, i)
        | .error _ => throw s!"weight {name} of {key} is not a whole number"

/-- Read the input. -/
def readJob (j : Json) : Except String Job := do
  let gameId ← j.getObjValAs? String "game"
  let some spec := gameSpecs.find? (·.id == gameId) | throw s!"there is no game called {gameId}"
  let seats ← j.getObjValAs? Nat "seats"
  if seats < spec.minSeats || spec.maxSeats < seats then
    throw s!"{spec.name} has {spec.minSeats} to {spec.maxSeats} seats"
  let threads := (jNat j "threads").getD 1
  if threads == 0 then throw "threads must be at least 1"
  let table ← (← j.getObjVal? "strategies").getObj?
  let entrants ← table.toList.mapM fun (key, v) => do
    let name := (jStr v "strategy").getD "hand"
    let some st := allStrategies.find? (·.name == name) | throw s!"there is no strategy called {name}"
    pure { key, strategy := st, values := ← readValues key v : Entrant }
  let games ← (← (← j.getObjVal? "games").getArr?).mapM fun g => do
    let seed ← g.getObjValAs? Nat "seed"
    let lineup ← g.getObjValAs? (List String) "lineup"
    if lineup.length != seats then throw s!"seed {seed}: a lineup needs {seats} seats"
    let places ← lineup.mapM fun k =>
      match entrants.findIdx? (·.key == k) with
      | some i => pure i
      | none => throw s!"seed {seed}: no strategy has the key {k}"
    pure { seed, lineup, seats := places.toArray : GameJob }
  let plain := (jBool j "plain").getD false
  let compactEvery := (jNat j "compactEvery").getD 1
  pure { spec, seats, threads, entrants := entrants.toArray, games
         options := if plain then { compactEvery := 0, dropJournal := false } else { compactEvery } }

/-! ## The output -/

/-- The line for one game. -/
def resultLine (g : GameJob) (seats : Nat) (p : Play G) : String :=
  let s := p.state
  let status := if s.phase == .ended then "finished" else "stuck"
  (Json.mkObj
    [ ("seed", toJson g.seed), ("lineup", toJson g.lineup), ("status", status)
    , ("winner", toJson s.winner), ("points", toJson ((List.range seats).map s.pointsOf))
    , ("round", toJson s.round), ("events", toJson p.events)
    , ("offersMade", toJson p.offersMade.toList), ("offersAccepted", toJson p.offersAccepted.toList)
    , ("rejected", toJson p.rejected) ]).compress

/-! ## The workers

Each worker builds its own board and weights. A value that threads share has its count changed with
atomic operations, and that costs more than the game's own work when it happens at every step. -/

/-- Play games until none are left, and give the time spent, in nanoseconds. -/
def worker (job : Job) (next : IO.Ref Nat) (results : Array (IO.Promise String)) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let G := job.spec.G
  let board := Board.of G
  let names := (G.resources.map (·.name)).toArray
  let plans : Array (Strategy × Ctx G) := job.entrants.map fun e =>
    let W := e.values.foldl (fun w x => w.withValue x.1 x.2) Weights.default
    (e.strategy, { weights := W, board })
  repeat
    let i ← next.modifyGet fun n => (n, n + 1)
    let some g := job.games[i]? | break
    let t : Table G := { plans := g.seats.map fun k => plans[k]!, names }
    let p := playGame job.options t g.seed
    if h : i < results.size then results[i].resolve (resultLine g job.seats p)
  return (← IO.monoNanosNow) - t0

/-- Run the input and print the results. -/
def runJob (job : Job) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let out ← IO.getStdout
  let next ← IO.mkRef 0
  let results ← job.games.mapM fun _ => (IO.Promise.new : BaseIO (IO.Promise String))
  let tasks ← (List.range job.threads).mapM fun _ =>
    IO.asTask (worker job next results) Task.Priority.dedicated
  let mut printed := 0
  for r in results do
    out.putStrLn r.result!.get
    printed := printed + 1
    if printed % 64 == 0 then out.flush
  let mut busy := 0
  for t in tasks do
    match ← IO.wait t with
    | .ok ns => busy := busy + ns
    | .error e => throw e
  let wall := (← IO.monoMsNow) - t0
  out.putStrLn (Json.mkObj
    [ ("summary", true), ("games", toJson job.games.size), ("wallMs", toJson wall)
    , ("cpuMs", toJson (busy / 1000000)) ]).compress
  out.flush
  return 0

/-! ## The checks -/

/-- Replay a saved bot game's seeds, and check that the arena's hand bot makes the same events. -/
def checkFixture (path : String) : IO Bool := do
  let lines := (← IO.FS.lines path).toList.filter (!·.isEmpty)
  let parsed := lines.filterMap fun l => (Json.parse l).toOption
  if parsed.length != lines.length then
    IO.println "a line of the file is not JSON"
    return false
  let some first := parsed.head? | return false
  let some spec := specOf? (jStr first "game") | return false
  let some serverSeed := jNat first "_serverSeed" | return false
  let nonces := parsed.filterMap fun j => if jStr j "t" == some "join" then jNat j "nonce" else none
  let events := (parsed.dropWhile fun j => jStr j "t" != some "start").drop 1
  let G := spec.G
  let seats := nonces.length
  let ctx := Ctx.of G
  let t : Table G :=
    { plans := Array.replicate seats (hand, ctx), names := (G.resources.map (·.name)).toArray }
  let mut p := Play.start (initialState G seats (UInt64.ofNat serverSeed) (nonces.map UInt64.ofNat)) seats
  let mut n := 0
  for ev in events do
    match advance {} t p with
    | none =>
      IO.println s!"event {n}: the log says {ev.compress}, and the arena's bots choose nothing"
      return false
    | some (e, p') =>
      let mine := ((eventJson? e).map (·.compress)).getD "other"
      if mine != ev.compress then
        IO.println s!"event {n}: the log says {ev.compress}, and the arena's bots choose {mine}"
        return false
      p := p'
      n := n + 1
  if p.state.phase != .ended then
    IO.println s!"after {n} events the log stops, and the arena's game has not ended"
    return false
  IO.println s!"the arena's hand bot made the same {n} events as the saved game, and the game ended with winner {p.state.winner}"
  return true

/-- Play this many games of every game and scenario, checking the fast bot against the reference. -/
def checkReference (games : Nat) : IO Bool := do
  let mut ok := true
  for spec in gameSpecs do
    let G := spec.G
    let seats := min 4 spec.maxSeats
    let board := Board.of G
    let names := (G.resources.map (·.name)).toArray
    let plain : Ctx G := { weights := .default, board }
    let offering : Ctx G := { plain with weights := { Weights.default with offerLimit := 2 } }
    for (label, scenario, firstCtx) in
        [ ("plain", Reference.Scenario.plain, plain), ("offers", .plain, offering)
        , ("laws", .laws, plain), ("deals", .deals, plain) ] do
      let plans := (List.range seats).toArray.map fun i => (hand, if i == 0 then firstCtx else plain)
      let t : Table G := { plans, names }
      let mut seen : Reference.Seen := {}
      for i in [0:games] do
        match Reference.checkGame scenario t (derive 7 i) seen with
        | .ok x => seen := x
        | .error why =>
          IO.println s!"{spec.id} {label}: {why}"
          ok := false
          break
      IO.println s!"{spec.id} {label}: {seen.states} states, {seen.finished} games finished, {seen.places} placements, {seen.trades} trades, with laws {seen.withLaws}, with deals {seen.withDeals}, with offers {seen.withOffers}, with votes {seen.withVotes}"
  return ok

/-- Every named weight, as JSON. -/
def paramsJson : Json :=
  Json.arr (params.map fun p =>
    Json.mkObj [ ("name", p.name), ("default", toJson (p.get Weights.default))
               , ("min", toJson p.min), ("max", toJson p.max) ]).toArray

/-- Read everything on stdin. -/
partial def readAll (h : IO.FS.Stream) (acc : String := "") : IO String := do
  let line ← h.getLine
  if line.isEmpty then return acc else readAll h (acc ++ line)

/-- Read a job from stdin and run it. -/
def fromStdin : IO UInt32 := do
  let text ← readAll (← IO.getStdin)
  match Json.parse text >>= readJob with
  | .error why =>
    IO.eprintln why
    return 1
  | .ok job => runJob job

end CharterServer.Arena

open CharterServer CharterServer.Arena in
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => fromStdin
  | ["--params"] =>
    IO.println paramsJson.compress
    return 0
  | ["--strategies"] =>
    IO.println (Lean.toJson (Evolved.pool.map (·.name))).compress
    return 0
  | ["--check-fixture", path] => return if ← checkFixture path then 0 else 1
  | ["--check-reference"] => return if ← checkReference 20 then 0 else 1
  | ["--check-reference", n] => return if ← checkReference (n.toNat?.getD 20) then 0 else 1
  | _ =>
    IO.eprintln "usage: charter-arena [--params | --strategies | --check-fixture PATH | --check-reference [GAMES]], or a job as JSON on stdin"
    return 2
