# lean-eventlog

An append-only, SQLite-backed event log for Lean 4 apps, with snapshots, whose pure model is proved to give the same state whether you replay from a snapshot or fold the whole log.

Lean 4 (`leanprover/lean4:v4.35.0`). Library `EventLog`. Dependencies:

- [lean-codec](../lean-codec) (`codec`): events and snapshot states are stored as `Codec.encodeBytes`.
- [leansqlite](../../forks/leansqlite) (`leansqlite`), the Charter fork on branch `charter-v4.35`
  (upstream `leanprover/leansqlite` re-pinned from v4.36.0-rc2 to v4.35.0; no source changes were
  needed). SQLite itself is bundled and compiled from source, so you need a C compiler `cc`.

No Mathlib, no Batteries. **Backend: SQLite** (the file-based fallback in the spec was not needed).

## Non-goals

- No proofs about the IO layer. SQLite is FFI; the IO layer is tested against the pure model.
- No multi-writer coordination beyond SQLite's own locking (one writer process per log is the
  intended use; a 5 s busy timeout is set).
- No compaction, deletion, or rewriting of events. Snapshots are an optimisation, never a
  replacement for events.
- No schema evolution of event types: if your `Codec` changes, old events may stop decoding
  (`readFrom` then throws, naming the sequence number).
- No hashing or tamper evidence (hash the encoded bytes yourself if you need it).

## Guarantees

The pure model (`EventLog/Pure.lean`, proofs in `EventLog/Theorems.lean`):

```lean
def replay (step : σ → ε → σ) (init : σ) (es : Array ε) : σ := es.foldl step init
structure Snapshot (σ) where seq : Nat; state : σ
structure PureLog (ε) where events : Array ε
def PureLog.readFrom (l) (n) : Array ε := l.events.extract n l.events.size
def PureLog.state (l) step init : σ := replay step init l.events
def PureLog.snapshotAt (l) step init (k) : Snapshot σ :=
  let k' := min k l.count; ⟨k', replay step init (l.events.extract 0 k')⟩
def PureLog.replayFrom (l) step (snap) : σ := replay step snap.state (l.readFrom snap.seq)
def PureLog.SnapshotValid (l) step init (snap) : Prop :=
  snap.seq ≤ l.count ∧ snap.state = replay step init (l.events.extract 0 snap.seq)
```

```lean
-- Headline: replaying from a snapshot taken by `snapshotAt k` equals folding the whole log.
theorem EventLog.PureLog.replay_eq_fold (l : PureLog ε) (step : σ → ε → σ) (init : σ) (k : Nat) :
    l.replayFrom step (l.snapshotAt step init k) = l.events.foldl step init

-- Resuming from any valid snapshot gives the state of the whole log.
theorem EventLog.PureLog.replayFrom_valid {l : PureLog ε} {step : σ → ε → σ} {init : σ}
    {snap : Snapshot σ} (h : l.SnapshotValid step init snap) :
    l.replayFrom step snap = l.state step init

-- `snapshotAt` produces a valid snapshot.
theorem EventLog.PureLog.snapshotAt_valid (l : PureLog ε) (step : σ → ε → σ) (init : σ) (k : Nat) :
    l.SnapshotValid step init (l.snapshotAt step init k)

-- Snapshots stay valid as the log grows (append-only).
theorem EventLog.PureLog.snapshotValid_append {l : PureLog ε} {step : σ → ε → σ} {init : σ}
    {snap : Snapshot σ} (h : l.SnapshotValid step init snap) (e : ε) :
    (l.append e).SnapshotValid step init snap
theorem EventLog.PureLog.snapshotValid_appendAll {l : PureLog ε} {step : σ → ε → σ} {init : σ}
    {snap : Snapshot σ} (h : l.SnapshotValid step init snap) (es : Array ε) :
    (l.appendAll es).SnapshotValid step init snap

-- Incremental replay: after one append, the resumed state is one more `step`.
theorem EventLog.PureLog.replayFrom_append {l : PureLog ε} {step : σ → ε → σ} {snap : Snapshot σ}
    (h : snap.seq ≤ l.count) (e : ε) :
    (l.append e).replayFrom step snap = step (l.replayFrom step snap) e

-- Append-only array behaviour.
theorem EventLog.PureLog.readFrom_append {l : PureLog ε} {n : Nat} (h : n ≤ l.count) (e : ε) :
    (l.append e).readFrom n = (l.readFrom n).push e
theorem EventLog.PureLog.readFrom_appendAll (l : PureLog ε) (es : Array ε) :
    (l.appendAll es).readFrom l.count = es
theorem EventLog.PureLog.appendAll_eq_foldl (l : PureLog ε) (es : Array ε) :
    l.appendAll es = es.foldl append l
theorem EventLog.PureLog.state_append (l : PureLog ε) (step : σ → ε → σ) (init : σ) (e : ε) :
    (l.append e).state step init = step (l.state step init) e
theorem EventLog.replay_append (step : σ → ε → σ) (init : σ) (a b : Array ε) :
    replay step init (a ++ b) = replay step (replay step init a) b
```

Axiom audit (`lake build` prints it from `EventLog/Audit.lean`):

```
'EventLog.PureLog.replay_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.replayFrom_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.snapshotAt_valid' depends on axioms: [propext]
'EventLog.PureLog.snapshotValid_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.snapshotValid_appendAll' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.replayFrom_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.readFrom_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.readFrom_appendAll' depends on axioms: [propext, Classical.choice, Quot.sound]
'EventLog.PureLog.appendAll_eq_foldl' depends on axioms: [propext, Quot.sound]
'EventLog.PureLog.state_append' depends on axioms: [propext, Quot.sound]
'EventLog.replay_append' depends on axioms: [propext, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, or new axioms.

## What is tested but not proved

The IO layer `EventLog.Log` (`EventLog/Log.lean`) is checked by `lake test`
(`EventLogTests/Main.lean`, 34 checks, each on a fresh database in a temp directory):

- `append` returns sequence numbers `0, 1, 2, …`; `count`, `readFrom n` and `toPure` agree with
  the in-memory `PureLog`; data and snapshots survive closing and reopening the file.
- `checkpoint` stores the current state; `replay` (latest snapshot + later events) equals the
  full fold, also after further appends and after a second checkpoint.
- `saveSnapshot` past the end of the log is rejected; the latest snapshot wins on load.
- `appendAll` is atomic (one transaction); a transaction that throws part-way leaves no events
  and the next sequence number is unchanged.
- A stored body that does not decode makes `readFrom` throw; zero-length encodings
  (`Unit`) round-trip.
- 400 random appends, batch appends and checkpoints: the file always agrees with `PureLog`, and
  `replay` always equals `PureLog.state`.

Not proved: that `Log.replay` equals `PureLog.replayFrom` on the decoded contents (it is the
same fold by construction; `Log.replay` is a three-line function), and that SQLite is durable.
`Log.replay` trusts the stored snapshot: it is valid (in the sense of `SnapshotValid`) if it was
written by `checkpoint` or by `saveState (l.snapshotAt …)` with the same `step` and `init`.

Pure-model `#guard` checks live in `EventLogTests/Pure.lean` and run during `lake build`.

## Quickstart

```toml
# lakefile.toml
[[require]]
name = "eventlog"
path = "../lean-eventlog"
```

```lean
import EventLog
open EventLog

def step (total : Nat) (deposit : Nat) : Nat := total + deposit

def main : IO Unit := do
  let log : Log Nat ← Log.open "bank.db"       -- creates tables if needed
  let seq ← log.append 10                      -- seq = 0 on a fresh file
  discard <| log.appendAll #[5, 7]             -- atomic batch
  discard <| log.checkpoint step 0             -- snapshot (seq, state) as Codec bytes
  discard <| log.append 1
  IO.println (← log.replay step 0)             -- 23: snapshot state + events after it
  IO.println (← log.readFrom 2)                -- #[7, 1]
```

API (`EventLog.Log ε`; `[Codec ε]` where values are encoded):

| Function | Meaning |
|---|---|
| `Log.open path` | open or create; WAL mode, `synchronous = FULL` |
| `append e : IO Nat` | append one event, return its sequence number |
| `appendAll es : IO Nat` | append atomically, return the first sequence number |
| `readFrom n : IO (Array ε)` | events with `seq ≥ n` (throws on undecodable bytes) |
| `count : IO Nat` | number of events |
| `saveSnapshot seq bytes`, `loadSnapshot : IO (Option (Nat × ByteArray))` | raw snapshots (latest wins) |
| `saveState snap`, `loadState init` | typed snapshots via `[Codec σ]` |
| `replay step init`, `checkpoint step init` | resume from latest snapshot; store a new one |
| `toPure : IO (PureLog ε)` | the whole file as the pure model |
| `appendRaw`, `readRawFrom`, `loadSnapshotAt` | byte-level access |

Schema: `events(seq INTEGER PRIMARY KEY, body BLOB NOT NULL)` and
`snapshots(seq INTEGER PRIMARY KEY, body BLOB NOT NULL)`. `append` assigns
`seq = (SELECT COUNT(*) FROM events)` in the same statement, so there are no gaps.

## Second use case: an audit log for a web app

`examples/AuditLog.lean` records admin actions (`grantRole`, `revokeRole`, `loginFailed`,
`deleteRecord`, …) before they take effect. The access-control view (roles held, failed-login
counters) is a fold over the log, resumed from a checkpoint. It uses `Codec.ofPartial` for the
`Action` type. Run `lake exe audit_log` (temp database) or `lake exe audit_log audit.db`:

```
checkpoint at seq 5
  #5: failed login for mallory
  #6: bob deleted record #42
  #7: alice revoked editor from bob
roles now: [(alice, admin)]
failed logins: [(mallory, 3)]
replay from checkpoint == full fold: true
history of bob:
  alice granted editor to bob
  bob deleted record #42
  alice revoked editor from bob
```
