import EventLog
import Server.Game

/-!
# Saved games, for `make spectate`

    charter-rl-logs DIR

`rl/eval` writes a sample of its games as `DIR/<code>.jsonl`, one server event per line. This replays each through
the server's own `Game.create` and `Game.apply`, which call `Engine.step`, and writes `DIR/<code>.db`, the event log
`make spectate RESULTS=DIR` opens. A game that does not replay is reported and gets no `.db`. Exit 1 if any failed.
-/

open Lean CharterServer

/-- Replay one saved game, and write its event log. -/
def convert (path : System.FilePath) : IO (Except String Nat) := do
  let lines := (← IO.FS.lines path).filter (!·.isEmpty)
  let parsed := lines.toList.mapM Json.parse
  match parsed with
  | .error err => return .error s!"a line is not JSON: {err}"
  | .ok [] => return .error "the file is empty"
  | .ok (first :: rest) =>
    let mut g ← match Game.create first with
      | .ok g => pure g
      | .error err => return .error s!"the table could not be created: {err}"
    let mut n := 1
    for ev in rest do
      match Game.apply g ev with
      | .ok g' => g := g'; n := n + 1
      | .error err => return .error s!"event {n} does not replay: {err}"
    let db := path.withExtension "db"
    if ← db.pathExists then IO.FS.removeFile db
    let log : EventLog.Log String ← EventLog.Log.open db
    for l in lines do
      discard <| log.append l
    return .ok n

def main (args : List String) : IO UInt32 := do
  let [dir] := args | IO.eprintln "usage: charter-rl-logs DIR"; return 2
  let mut bad := 0
  let mut good := 0
  for f in ← System.FilePath.readDir dir do
    if f.fileName.endsWith ".jsonl" then
      match ← convert f.path with
      | .ok n => good := good + 1; IO.println s!"{f.fileName}: {n} events, replayed"
      | .error err => bad := bad + 1; IO.println s!"{f.fileName}: FAILED, {err}"
  IO.println s!"{good} games written, {bad} failed"
  return if bad == 0 then 0 else 1
