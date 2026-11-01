/-!
# EventLog.Pure: the reference model

An event log is an append-only array of events. The state of an application is
`replay step init events`, a left fold. A *snapshot* `(seq, state)` records the state
after the first `seq` events, so a reader can resume from it instead of replaying
everything.

The IO layer (`EventLog.Log`) stores exactly this structure on disk; `Log.toPure`
reads it back as a `PureLog`.
-/

namespace EventLog

/-- Fold events into a state. -/
def replay {σ ε : Type} (step : σ → ε → σ) (init : σ) (es : Array ε) : σ :=
  es.foldl step init

/-- The state after the first `seq` events. -/
structure Snapshot (σ : Type) where
  seq : Nat
  state : σ
deriving Repr, Inhabited, DecidableEq

/-- An append-only log of events. Event `i` has sequence number `i` (0-based). -/
structure PureLog (ε : Type) where
  events : Array ε := #[]
deriving Repr, Inhabited, DecidableEq

namespace PureLog

variable {ε σ : Type}

def empty : PureLog ε := ⟨#[]⟩

/-- Number of events. -/
def count (l : PureLog ε) : Nat := l.events.size

/-- Append one event; its sequence number is the old `count`. -/
def append (l : PureLog ε) (e : ε) : PureLog ε := ⟨l.events.push e⟩

/-- Append several events in order. -/
def appendAll (l : PureLog ε) (es : Array ε) : PureLog ε := ⟨l.events ++ es⟩

/-- Events with sequence number `≥ n`, in order. -/
def readFrom (l : PureLog ε) (n : Nat) : Array ε := l.events.extract n l.events.size

/-- The current state: fold the whole log. -/
def state (l : PureLog ε) (step : σ → ε → σ) (init : σ) : σ := replay step init l.events

/-- Snapshot after the first `k` events (clamped to `count`). -/
def snapshotAt (l : PureLog ε) (step : σ → ε → σ) (init : σ) (k : Nat) : Snapshot σ :=
  let k' := min k l.count
  ⟨k', replay step init (l.events.extract 0 k')⟩

/-- Resume from a snapshot: fold the events after `snap.seq` into `snap.state`. -/
def replayFrom (l : PureLog ε) (step : σ → ε → σ) (snap : Snapshot σ) : σ :=
  replay step snap.state (l.readFrom snap.seq)

/-- A snapshot is valid for `l` if it is the state after its first `seq` events. -/
def SnapshotValid (l : PureLog ε) (step : σ → ε → σ) (init : σ) (snap : Snapshot σ) : Prop :=
  snap.seq ≤ l.count ∧ snap.state = replay step init (l.events.extract 0 snap.seq)

end PureLog
end EventLog
