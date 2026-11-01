import EventLog
import EventLogTests.Pure

/-! IO tests for the SQLite layer. Each test uses a fresh database in a temp directory. -/

open EventLog

/-- Events: (user, amount). State: (number of events, total amount). -/
abbrev Ev := String × Nat
abbrev St := Nat × Nat

def stepSt (s : St) (e : Ev) : St := (s.1 + 1, s.2 + e.2)

structure Ctx where
  failures : IO.Ref Nat
  passes : IO.Ref Nat

def check (ctx : Ctx) (name : String) (ok : Bool) : IO Unit := do
  if ok then ctx.passes.modify (· + 1)
  else
    ctx.failures.modify (· + 1)
    IO.eprintln s!"FAIL: {name}"

def throws (act : IO α) : IO Bool := do
  try discard act; return false
  catch _ => return true

def evs : Array Ev := #[("ann", 5), ("bob", 7), ("ann", 1), ("cat", 30), ("bob", 2)]

def basic (ctx : Ctx) (dir : System.FilePath) : IO Unit := do
  let path := dir / "basic.db"
  let log : Log Ev ← Log.open path
  check ctx "empty count" ((← log.count) == 0)
  check ctx "empty read" ((← log.readFrom 0).size == 0)
  check ctx "no snapshot" ((← log.loadSnapshot).isNone)
  let mut seqs := #[]
  for e in evs do
    seqs := seqs.push (← log.append e)
  check ctx "append returns 0..n-1" (seqs == #[0, 1, 2, 3, 4])
  check ctx "count" ((← log.count) == 5)
  check ctx "readFrom 0" ((← log.readFrom 0) == evs)
  check ctx "readFrom 3" ((← log.readFrom 3) == #[("cat", 30), ("bob", 2)])
  check ctx "readFrom past end" ((← log.readFrom 9) == #[])
  -- reopen: data persists
  let log2 : Log Ev ← Log.open path
  check ctx "reopen count" ((← log2.count) == 5)
  let pure ← log2.toPure
  check ctx "toPure matches in-memory model" (pure == PureLog.empty.appendAll evs)
  check ctx "replay without snapshot" ((← log2.replay stepSt (0, 0)) == (5, 45))

def snapshots (ctx : Ctx) (dir : System.FilePath) : IO Unit := do
  let log : Log Ev ← Log.open (dir / "snap.db")
  discard <| log.appendAll evs
  let s ← log.checkpoint stepSt (0, 0)
  check ctx "checkpoint seq" (s.seq == 5)
  check ctx "checkpoint state" (s.state == (5, 45))
  check ctx "loadSnapshot latest" ((← log.loadSnapshot).map (·.1) == some 5)
  discard <| log.append ("dan", 100)
  check ctx "replay after snapshot + append" ((← log.replay stepSt (0, 0)) == (6, 145))
  let pure ← log.toPure
  check ctx "replay = pure fold" ((← log.replay stepSt (0, 0)) == pure.state stepSt (0, 0))
  -- earlier snapshot by explicit seq; latest wins on load
  log.saveState (pure.snapshotAt stepSt (0, 0) 2)
  check ctx "latest snapshot still 5" ((← log.loadSnapshot).map (·.1) == some 5)
  check ctx "loadSnapshotAt 2" ((← log.loadSnapshotAt 2).isSome)
  check ctx "snapshot beyond log rejected" (← throws (log.saveSnapshot 99 ByteArray.empty))
  -- snapshots survive reopen
  let log2 : Log Ev ← Log.open (dir / "snap.db")
  check ctx "reopen replay" ((← log2.replay stepSt (0, 0)) == (6, 145))
  -- second checkpoint picks up from the first
  let s2 ← log2.checkpoint stepSt (0, 0)
  check ctx "second checkpoint" (s2 == ⟨6, (6, 145)⟩)

def atomicity (ctx : Ctx) (dir : System.FilePath) : IO Unit := do
  let log : Log Ev ← Log.open (dir / "atomic.db")
  discard <| log.append ("ann", 1)
  let first ← log.appendAll #[("b", 2), ("c", 3)]
  check ctx "appendAll returns first seq" (first == 1)
  check ctx "appendAll count" ((← log.count) == 3)
  -- a transaction that fails part-way leaves no trace
  let failed ← throws <| log.db.transaction (α := Unit) do
    discard <| log.append ("x", 9)
    discard <| log.append ("y", 9)
    throw (IO.userError "boom")
  check ctx "failing transaction throws" failed
  check ctx "rollback leaves count" ((← log.count) == 3)
  check ctx "next seq after rollback" ((← log.append ("d", 4)) == 3)

def corruption (ctx : Ctx) (dir : System.FilePath) : IO Unit := do
  let log : Log Ev ← Log.open (dir / "bad.db")
  discard <| log.append ("ok", 1)
  discard <| log.appendRaw (ByteArray.mk #[0xff, 0xff, 0xff])
  check ctx "undecodable event throws" (← throws (log.readFrom 0))
  check ctx "raw read still works" ((← log.readRawFrom 0).size == 2)
  check ctx "decodable prefix readable" ((← log.readRawFrom 0)[0]!.size > 0)
  -- empty encodings (Unit) round-trip as zero-length blobs
  let ul : Log Unit ← Log.open (dir / "unit.db")
  discard <| ul.append ()
  discard <| ul.append ()
  check ctx "unit events" ((← ul.readFrom 0) == #[(), ()])

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Random appends and checkpoints; the file always agrees with the pure model. -/
def randomized (ctx : Ctx) (dir : System.FilePath) : IO Unit := do
  let log : Log Ev ← Log.open (dir / "rand.db")
  let mut model : PureLog Ev := PureLog.empty
  let mut seed : UInt64 := 7
  let mut ok := true
  for i in [0:400] do
    seed := lcg seed
    let r := (seed >>> 33).toNat
    if r % 10 == 0 then
      discard <| log.checkpoint stepSt (0, 0)
    else if r % 10 == 1 then
      let batch : Array Ev := #[(s!"u{i}", r % 50), (s!"v{i}", r % 7)]
      discard <| log.appendAll batch
      model := model.appendAll batch
    else
      let e : Ev := (s!"u{r % 5}", r % 100)
      let seq ← log.append e
      ok := ok && seq == model.count
      model := model.append e
    if i % 40 == 0 then
      ok := ok && (← log.replay stepSt (0, 0)) == model.state stepSt (0, 0)
  ok := ok && (← log.toPure) == model
  ok := ok && (← log.replay stepSt (0, 0)) == model.state stepSt (0, 0)
  check ctx "randomized log agrees with PureLog" ok

/-- The README quickstart. -/
def quickstart (ctx : Ctx) (dir : System.FilePath) : IO Unit := do
  let step (total : Nat) (deposit : Nat) : Nat := total + deposit
  let log : Log Nat ← Log.open (dir / "bank.db")
  let seq ← log.append 10
  discard <| log.appendAll #[5, 7]
  discard <| log.checkpoint step 0
  discard <| log.append 1
  check ctx "quickstart seq" (seq == 0)
  check ctx "quickstart replay" ((← log.replay step 0) == 23)
  check ctx "quickstart readFrom" ((← log.readFrom 2) == #[7, 1])

def main : IO UInt32 := do
  let ctx : Ctx := { failures := ← IO.mkRef 0, passes := ← IO.mkRef 0 }
  IO.FS.withTempDir fun dir => do
    basic ctx dir
    snapshots ctx dir
    atomicity ctx dir
    corruption ctx dir
    randomized ctx dir
    quickstart ctx dir
  let f ← ctx.failures.get
  IO.println s!"eventlog_tests: {← ctx.passes.get} passed, {f} failed"
  return if f == 0 then 0 else 1
