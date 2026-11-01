import SQLite
import Codec
import EventLog.Pure

/-!
# EventLog.Log: a durable event log in SQLite

Schema (one SQLite file per log):

```sql
CREATE TABLE events    (seq INTEGER PRIMARY KEY, body BLOB NOT NULL);  -- seq = 0, 1, 2, ...
CREATE TABLE snapshots (seq INTEGER PRIMARY KEY, body BLOB NOT NULL);  -- state after `seq` events
```

Events are stored as `Codec.encodeBytes e`. `append` assigns `seq = count` in the same SQL
statement, so the sequence numbers are always `0 .. count-1` with no gaps. The database runs in
WAL mode with `synchronous = FULL`: when `append` returns, the event is on disk.

This layer is tested, not proved (it is FFI). It mirrors `EventLog.PureLog`; `Log.toPure`
reads the file back as a `PureLog`.
-/

namespace EventLog

/-- A handle to an open event log of events of type `ε`. -/
structure Log (ε : Type) where
  db : SQLite
  path : System.FilePath

namespace Log

variable {ε : Type}

private def schema : String :=
  "PRAGMA journal_mode = WAL;
   PRAGMA synchronous = FULL;
   CREATE TABLE IF NOT EXISTS events (seq INTEGER PRIMARY KEY, body BLOB NOT NULL);
   CREATE TABLE IF NOT EXISTS snapshots (seq INTEGER PRIMARY KEY, body BLOB NOT NULL);"

/-- Open (or create) the log stored at `path`. -/
def «open» (path : System.FilePath) (busyTimeoutMs : Int32 := 5000) : IO (Log ε) := do
  let db ← SQLite.open path busyTimeoutMs
  db.exec schema
  return { db, path }

private def toInt64 (n : Nat) : Int64 := Int64.ofNat n

private def ofInt64 (i : Int64) : Nat := i.toInt.toNat

/-- Number of events. -/
def count (log : Log ε) : IO Nat := do
  let stmt ← log.db.prepare "SELECT COUNT(*) FROM events"
  if ← stmt.step then
    return ofInt64 (← stmt.columnInt64 0)
  else
    throw (.userError "eventlog: COUNT(*) returned no row")

/-- Append raw bytes as the next event. Returns its sequence number. -/
def appendRaw (log : Log ε) (body : ByteArray) : IO Nat := do
  let stmt ← log.db.prepare
    "INSERT INTO events (seq, body) VALUES ((SELECT COUNT(*) FROM events), ?1)"
  stmt.bindBlob 1 body
  stmt.exec
  return ofInt64 (← log.db.lastInsertRowId)

/-- Append one event. Returns its sequence number (the old `count`). -/
def append [Codec ε] (log : Log ε) (e : ε) : IO Nat :=
  log.appendRaw (Codec.encodeBytes e)

/-- Append several events atomically (all or none). Returns the first new sequence number. -/
def appendAll [Codec ε] (log : Log ε) (es : Array ε) : IO Nat :=
  log.db.transaction (mode := .immediate) do
    let start ← log.count
    for e in es do
      discard <| log.appendRaw (Codec.encodeBytes e)
    return start

/-- Raw bodies of events with `seq ≥ n`, in order. -/
def readRawFrom (log : Log ε) (n : Nat) : IO (Array ByteArray) := do
  let stmt ← log.db.prepare "SELECT seq, body FROM events WHERE seq >= ?1 ORDER BY seq"
  stmt.bindInt64 1 (toInt64 n)
  let mut out := #[]
  let mut expect := n
  while ← stmt.step do
    let seq := ofInt64 (← stmt.columnInt64 0)
    if seq != expect then
      throw (.userError s!"eventlog: gap in sequence numbers at {expect} (found {seq})")
    out := out.push (← stmt.columnBlob 1)
    expect := expect + 1
  return out

/-- Events with `seq ≥ n`, in order. Throws if a stored body does not decode. -/
def readFrom [Codec ε] (log : Log ε) (n : Nat) : IO (Array ε) := do
  let raws ← log.readRawFrom n
  let mut out := #[]
  for h : i in [0:raws.size] do
    match Codec.decodeBytes (α := ε) raws[i] with
    | some e => out := out.push e
    | none => throw (.userError s!"eventlog: event {n + i} does not decode")
  return out

/-- The whole log as a pure value. -/
def toPure [Codec ε] (log : Log ε) : IO (PureLog ε) :=
  return ⟨← log.readFrom 0⟩

/-- Store a snapshot: `bytes` is the encoded state after the first `seq` events.
Replaces any snapshot with the same `seq`. -/
def saveSnapshot (log : Log ε) (seq : Nat) (bytes : ByteArray) : IO Unit := do
  let n ← log.count
  if seq > n then
    throw (.userError s!"eventlog: snapshot seq {seq} is beyond the log ({n} events)")
  let stmt ← log.db.prepare "INSERT OR REPLACE INTO snapshots (seq, body) VALUES (?1, ?2)"
  stmt.bindInt64 1 (toInt64 seq)
  stmt.bindBlob 2 bytes
  stmt.exec

/-- The latest snapshot `(seq, bytes)`, if any. -/
def loadSnapshot (log : Log ε) : IO (Option (Nat × ByteArray)) := do
  let stmt ← log.db.prepare "SELECT seq, body FROM snapshots ORDER BY seq DESC LIMIT 1"
  if ← stmt.step then
    return some (ofInt64 (← stmt.columnInt64 0), ← stmt.columnBlob 1)
  else
    return none

/-- The snapshot with exactly this `seq`, if any. -/
def loadSnapshotAt (log : Log ε) (seq : Nat) : IO (Option ByteArray) := do
  let stmt ← log.db.prepare "SELECT body FROM snapshots WHERE seq = ?1"
  stmt.bindInt64 1 (toInt64 seq)
  if ← stmt.step then return some (← stmt.columnBlob 0) else return none

/-- Encode and store the state after the first `seq` events. -/
def saveState {σ : Type} [Codec σ] (log : Log ε) (snap : Snapshot σ) : IO Unit :=
  log.saveSnapshot snap.seq (Codec.encodeBytes snap.state)

/-- The latest snapshot decoded as a state, or `⟨0, init⟩` if there is none.
Throws if the stored snapshot does not decode. -/
def loadState {σ : Type} [Codec σ] (log : Log ε) (init : σ) : IO (Snapshot σ) := do
  match ← log.loadSnapshot with
  | none => return ⟨0, init⟩
  | some (seq, bytes) =>
    match Codec.decodeBytes (α := σ) bytes with
    | some st => return ⟨seq, st⟩
    | none => throw (.userError s!"eventlog: snapshot at {seq} does not decode")

/-- Current state: resume from the latest snapshot and fold the events after it.
This is `PureLog.replayFrom`; by `PureLog.replay_eq_fold` it equals folding the whole log
whenever the stored snapshot was produced by `snapshotAt` (for example via `checkpoint`). -/
def replay {σ : Type} [Codec ε] [Codec σ] (log : Log ε) (step : σ → ε → σ) (init : σ) :
    IO σ := do
  let snap ← log.loadState init
  let rest ← log.readFrom snap.seq
  return EventLog.replay step snap.state rest

/-- Compute the current state (from the latest snapshot) and store it as a new snapshot.
Returns the snapshot. -/
def checkpoint {σ : Type} [Codec ε] [Codec σ] (log : Log ε) (step : σ → ε → σ) (init : σ) :
    IO (Snapshot σ) :=
  log.db.transaction (mode := .immediate) do
    let snap ← log.loadState init
    let rest ← log.readFrom snap.seq
    let s : Snapshot σ := ⟨snap.seq + rest.size, EventLog.replay step snap.state rest⟩
    log.saveState s
    return s

end Log
end EventLog
