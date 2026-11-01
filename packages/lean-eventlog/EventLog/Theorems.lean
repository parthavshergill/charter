import EventLog.Pure

/-!
# Guarantees about the pure model

`replay_eq_fold` is the headline: resuming from a snapshot gives the same state as folding
the whole log. The other theorems say snapshots stay valid as the log grows, and that
appends and reads behave like an append-only array.
-/

namespace EventLog

variable {ε σ : Type}

theorem replay_eq_foldl_toList (step : σ → ε → σ) (init : σ) (es : Array ε) :
    replay step init es = es.toList.foldl step init := by
  simp [replay, Array.foldl_toList]

theorem replay_append (step : σ → ε → σ) (init : σ) (a b : Array ε) :
    replay step init (a ++ b) = replay step (replay step init a) b := by
  simp [replay_eq_foldl_toList, List.foldl_append]

theorem replay_push (step : σ → ε → σ) (init : σ) (a : Array ε) (e : ε) :
    replay step init (a.push e) = step (replay step init a) e := by
  simp [replay_eq_foldl_toList]

namespace PureLog

theorem toList_extract_zero (a : Array ε) (k : Nat) :
    (a.extract 0 k).toList = a.toList.take k := by
  simp [Array.toList_extract]

theorem toList_extract_prefix (l : PureLog ε) (k : Nat) :
    (l.events.extract 0 k).toList = l.events.toList.take k :=
  toList_extract_zero _ _

theorem toList_readFrom (l : PureLog ε) (n : Nat) :
    (l.readFrom n).toList = l.events.toList.drop n := by
  simp only [readFrom, Array.toList_extract, List.extract_eq_take_drop]
  apply List.take_of_length_le
  simp

@[simp] theorem count_append (l : PureLog ε) (e : ε) : (l.append e).count = l.count + 1 := by
  simp [count, append]

@[simp] theorem count_appendAll (l : PureLog ε) (es : Array ε) :
    (l.appendAll es).count = l.count + es.size := by
  simp [count, appendAll]

@[simp] theorem readFrom_zero (l : PureLog ε) : l.readFrom 0 = l.events := by
  simp [readFrom]

theorem snapshotAt_seq (l : PureLog ε) (step : σ → ε → σ) (init : σ) (k : Nat) :
    (l.snapshotAt step init k).seq = min k l.count := rfl

/-- Resuming from any valid snapshot gives the state of the whole log. -/
theorem replayFrom_valid {l : PureLog ε} {step : σ → ε → σ} {init : σ} {snap : Snapshot σ}
    (h : l.SnapshotValid step init snap) : l.replayFrom step snap = l.state step init := by
  obtain ⟨_, hst⟩ := h
  simp only [replayFrom, state, hst, replay_eq_foldl_toList, toList_extract_prefix,
    toList_readFrom, ← List.foldl_append, List.take_append_drop]

/-- `snapshotAt` produces a valid snapshot. -/
theorem snapshotAt_valid (l : PureLog ε) (step : σ → ε → σ) (init : σ) (k : Nat) :
    l.SnapshotValid step init (l.snapshotAt step init k) :=
  ⟨Nat.min_le_right _ _, rfl⟩

/-- **Headline guarantee.** Replaying from a snapshot taken by `snapshotAt k` equals folding
the whole log. -/
theorem replay_eq_fold (l : PureLog ε) (step : σ → ε → σ) (init : σ) (k : Nat) :
    l.replayFrom step (l.snapshotAt step init k) = l.events.foldl step init :=
  replayFrom_valid (snapshotAt_valid l step init k)

/-- Appending keeps every earlier event and puts the new one last. -/
theorem readFrom_append {l : PureLog ε} {n : Nat} (h : n ≤ l.count) (e : ε) :
    (l.append e).readFrom n = (l.readFrom n).push e := by
  apply Array.toList_inj.mp
  simp only [toList_readFrom, append, Array.toList_push]
  exact List.drop_append_of_le_length (by simpa [count] using h)

/-- What `appendAll` added is exactly what is read back from the old end. -/
theorem readFrom_appendAll (l : PureLog ε) (es : Array ε) :
    (l.appendAll es).readFrom l.count = es := by
  apply Array.toList_inj.mp
  simp [toList_readFrom, appendAll, count]

theorem appendAll_eq_foldl (l : PureLog ε) (es : Array ε) :
    l.appendAll es = es.foldl append l := by
  rw [← Array.foldl_toList]
  obtain ⟨evs⟩ := l
  obtain ⟨xs⟩ := es
  simp only [appendAll]
  induction xs generalizing evs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, append]
    rw [← ih]
    simp

/-- Snapshots stay valid as the log grows (the log is append-only). -/
theorem snapshotValid_append {l : PureLog ε} {step : σ → ε → σ} {init : σ} {snap : Snapshot σ}
    (h : l.SnapshotValid step init snap) (e : ε) : (l.append e).SnapshotValid step init snap := by
  obtain ⟨hle, hst⟩ := h
  refine ⟨by simp; omega, ?_⟩
  rw [hst]
  congr 1
  apply Array.toList_inj.mp
  simp only [toList_extract_zero, append, Array.toList_push]
  rw [List.take_append_of_le_length (by simpa [count] using hle)]

theorem snapshotValid_appendAll {l : PureLog ε} {step : σ → ε → σ} {init : σ}
    {snap : Snapshot σ} (h : l.SnapshotValid step init snap) (es : Array ε) :
    (l.appendAll es).SnapshotValid step init snap := by
  rw [appendAll_eq_foldl, ← Array.foldl_toList]
  induction es.toList generalizing l with
  | nil => exact h
  | cons x xs ih => exact ih (snapshotValid_append h x)

@[simp] theorem state_append (l : PureLog ε) (step : σ → ε → σ) (init : σ) (e : ε) :
    (l.append e).state step init = step (l.state step init) e := by
  simp [state, append, replay_push]

/-- Incremental replay: after one append, the resumed state is one more `step`. -/
theorem replayFrom_append {l : PureLog ε} {step : σ → ε → σ} {snap : Snapshot σ}
    (h : snap.seq ≤ l.count) (e : ε) :
    (l.append e).replayFrom step snap = step (l.replayFrom step snap) e := by
  simp [replayFrom, readFrom_append h, replay_push]

end PureLog
end EventLog
