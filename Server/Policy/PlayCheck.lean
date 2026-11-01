import Server.Player
import Server.PreviewCheck

/-!
# Playing whole games with the trained policy

`charter-policy-check WEIGHTS [GAMES] [--vs-hand]` plays games through the server's own `Game.create` and
`Game.apply` (so every event goes through `Engine.step`), with the policy in some seats and the current bot in the
rest.

- Without `--vs-hand`: every world in the Library, every seat played by the policy, at 2, 4 and 6 seats where
  the world allows. Each game must reach its end. It fails if a seat is stuck (no event the engine accepts while
  the game is not over), if a decision fails, or if a game runs past the step cap.
- With `--vs-hand`: one policy seat against current bots, the policy's seat moving round the table, `GAMES`
  games per world. It prints win rate, target wins against round-limit wins, and points.

Time per policy decision is measured on the plain CPU this runs on.
-/

namespace CharterServer.Policy.PlayCheck
open Lean Charter CharterServer CharterServer.Game CharterServer.Player

/-- What one game came to. -/
structure Result where
  game : String
  seats : Nat
  policySeats : List Nat
  ended : Bool
  winner : Option Nat
  /-- The winner reached the target, rather than winning on the round limit. -/
  byTarget : Bool
  points : List Nat
  rounds : Nat
  decisions : Nat
  decisionNs : Nat
  /-- Turn decisions where a zero recurrent state would have chosen another move than the carried one. -/
  stateDiffers : Nat := 0
  error : Option String

/-- Play one game. `policySeats` play by `net`; the others by the current bot. -/
def playOne (net : Net) (spec : GameSpec) (seats seed : Nat) (policySeats : List Nat)
    (record : Option IO.FS.Handle := none) : IO Result := do
  let base : Result := { game := spec.id, seats, policySeats, ended := false, winner := none, byTarget := false
                         points := [], rounds := 0, decisions := 0, decisionNs := 0, error := none }
  let .ok g0 := PreviewCheck.newTable spec seats seed | return { base with error := some "the table did not start" }
  let mut g := g0
  let mut decisions := 0
  let mut ns := 0
  let mut err : Option String := none
  let mut mem : Memory := {}
  let mut lastTurn : Option Nat := none
  if let some h := record then h.putStrLn "reset"
  let mut differs := 0
  for _ in [0:20000] do
    let some s := g.state | break
    if s.phase == .ended then break
    let mut lists : List (List Json) := []
    for seat in List.range seats do
      if policySeats.contains seat then
        let t0 ← IO.monoNanosNow
        match candidatesWith net mem g seat with
        | .ok evs =>
          let t1 ← IO.monoNanosNow
          if s.currentSeat == some seat then
            if let some h := record then
              if seat == policySeats.headD 0 then
                if lastTurn != some s.turnsTaken then h.putStrLn "turn"
                lastTurn := some s.turnsTaken
                h.putStrLn (" ".intercalate ((observationFor g s seat).toList.map toString))
            decisions := decisions + 1
            ns := ns + (t1 - t0)
            -- The move it plays carries the state; count where a zero state would have chosen another move.
            match turnEventFrom net (mem.stateOf net s seat) g s seat, turnEvent net g s seat with
            | .ok (some (evC, _, _)), .ok (some (evZ, _)) =>
              if (Bots.eventJson? evC).map (·.compress) != (Bots.eventJson? evZ).map (·.compress) then differs := differs + 1
            | _, _ => pure ()
          lists := lists ++ [evs]
        | .error e =>
          err := some s!"round {s.round}, seat {seat}: {e}"
          lists := lists ++ [[]]
      else
        lists := lists ++ [Bots.candidatesFor g [seat]]
    if err.isSome then break
    match (merged lists).find? fun ev => (apply g ev).toOption.isSome with
    | some ev =>
      if policySeats.any (s.currentSeat == some ·) then mem := mem.after net g ev
      match apply g ev with
      | .ok g' => g := g'
      | .error e => err := some e; break
    | none =>
      err := some s!"stuck in round {s.round}: seat {s.currentSeat} has no event the engine accepts"
      break
  let some s := g.state | return { base with error := some "no state" }
  let ended := s.phase == .ended
  let points := (List.range seats).map s.pointsOf
  let byTarget := match s.winner with
    | some w => s.pointsOf w ≥ g.spec.G.targetPoints
    | none => false
  let err2 := if err.isNone && !ended then some "the game did not end within the step cap" else err
  return { base with ended, winner := s.winner, byTarget, points, rounds := s.round, decisions, decisionNs := ns
                     stateDiffers := differs
                     error := err2 }

/-- One line about a game. -/
def Result.line (r : Result) : String :=
  let who := match r.winner with
    | some w => s!"seat {w} ({if r.policySeats.contains w then "policy" else "current bot"}) won by {if r.byTarget then "target" else "round limit"}"
    | none => "no winner"
  let ms := if r.decisions == 0 then 0.0 else Float.ofNat r.decisionNs / Float.ofNat r.decisions / 1e6
  s!"{r.game}, {r.seats} seats, policy {r.policySeats}: {if r.ended then "ended" else "NOT ENDED"} in round {r.rounds}; {who}; points {r.points}; {r.decisions} policy turn decisions, {ms} ms each; zero state would differ on {r.stateDiffers}" ++
    (match r.error with | some e => s!"; ERROR: {e}" | none => "")

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | do
    IO.eprintln "usage: charter-policy-check WEIGHTS [GAMES] [--vs-hand] [--record OBS.txt]"
    return 2
  let net ← match ← loadNet path with
    | .ok n => pure n
    | .error e => do IO.eprintln e; return 2
  IO.println s!"weights {path}: E {net.E}, hidden {net.hidden}, layers {net.layers}, pointer {net.pointer}, state rule {net.stateRule.name}"
  let vsHand := args.contains "--vs-hand"
  let games := ((args.drop 1).head?.bind String.toNat?).getD 4
  let mut ok := true
  let recordPath := match args.dropWhile (· != "--record") with
    | _ :: p :: _ => some p
    | _ => none
  let record ← recordPath.mapM fun p => IO.FS.Handle.mk p .write
  if !vsHand then
    for spec in gameSpecs do
      for seats in [2, 4, 6].filter fun n => spec.minSeats ≤ n && n ≤ spec.maxSeats do
        -- Record seat 0's observations in the 4-seat game of each world (or its first), for the differential test.
        let rec_ := if seats == 4 || (seats == spec.maxSeats && spec.maxSeats < 4) then record else none
        let r ← playOne net spec seats (100 + seats) (List.range seats) rec_
        IO.println r.line
        (← IO.getStdout).flush
        if r.error.isSome || !r.ended then ok := false
    IO.println (if ok then "policy check: PASS, every world ended at every seat count tried" else "policy check: FAILED")
  else
    let mut all : List Result := []
    for spec in gameSpecs do
      let seats := min 4 spec.maxSeats
      let mut rs : List Result := []
      for i in [0:games] do
        let r ← playOne net spec seats (5000 + i) [i % seats]
        IO.println r.line
        (← IO.getStdout).flush
        rs := rs ++ [r]
        if r.error.isSome then ok := false
      all := all ++ rs
    let tally (rs : List Result) : String :=
      let wins := rs.filter fun r => r.winner.any r.policySeats.contains
      let target := wins.filter (·.byTarget)
      let pts := rs.map fun r => r.points.getD (r.policySeats.headD 0) 0
      let best := rs.map fun r => (r.points.zipIdx.filter fun (_, i) => !r.policySeats.contains i).foldl (fun m (p, _) => max m p) 0
      s!"{wins.length}/{rs.length} wins ({target.length} by target, {wins.length - target.length} by round limit); policy points {pts.sum}, best current bot's points {best.sum}"
    for spec in gameSpecs do
      IO.println s!"{spec.id}: {tally (all.filter (·.game == spec.id))}"
    IO.println s!"all worlds: {tally all}"
    let d := (all.map (·.decisions)).sum
    let x := (all.map (·.stateDiffers)).sum
    IO.println s!"recurrent state: a zero state instead would change {x} of {d} policy turn decisions"
  return if ok then 0 else 1

end CharterServer.Policy.PlayCheck

def main (args : List String) : IO UInt32 := CharterServer.Policy.PlayCheck.main args
