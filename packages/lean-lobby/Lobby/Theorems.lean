import Lobby.Lemmas

/-!
# Lobby guarantees

The README lists these theorems under "Guarantees"; `Lobby/Audit.lean` prints their axioms.
-/

namespace Lobby

/-! ## Invariant preservation -/

theorem onRoom_wf {l : Lobby} {c : String} {f : Room → Except Reject (Room × Notice)}
    (hf : ∀ r r' n, r.WF → f r = .ok (r', n) → r'.WF ∧ r'.code = r.code)
    (h : ∀ r ∈ l.rooms, r.WF) : ∀ r ∈ (l.onRoom c f).1.rooms, r.WF := by
  rcases onRoom_cases (l := l) (c := c) (f := f) with he | ⟨r, r', n, hr, hfr, he⟩
  · rw [he]; exact h
  · rw [he]
    intro x hx
    rcases mem_put hx with hx | rfl
    · exact h x hx
    · exact (hf r x n (h r (room?_spec hr).1) hfr).1

/-- One step preserves `Room.WF` for every room. -/
theorem step_wf {l : Lobby} (c : Cmd) (h : ∀ r ∈ l.rooms, r.WF) :
    ∀ r ∈ (l.step c).1.rooms, r.WF := by
  cases c with
  | create code min max =>
    simp only [step]
    split
    · exact h
    · split
      · exact h
      · rename_i hbad
        intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact h r hr
        · exact Room.new_wf (by omega) (by omega)
  | join code name token => exact onRoom_wf (fun _ _ _ hw hj => Room.join_wf hw hj) h
  | reconnect code token => exact onRoom_wf (fun _ _ _ hw hj => Room.reconnect_wf hw hj) h
  | leave code token => exact onRoom_wf (fun _ _ _ hw hj => Room.leave_wf hw hj) h
  | start code => exact onRoom_wf (fun _ _ _ hw hj => Room.start_wf hw hj) h

/-- Every room of a reachable lobby satisfies the invariant. -/
theorem reachable_wf {l : Lobby} (hl : Reachable l) : ∀ r ∈ l.rooms, r.WF := by
  induction hl with
  | empty => simp [Lobby.empty]
  | step c _ ih => exact step_wf c ih

/-! ## Guarantees -/

/-- No two filled seats of a room share a token. -/
theorem seat_unique {l : Lobby} (hl : Reachable l) {r : Room} (hr : r ∈ l.rooms) :
    r.tokens.Nodup :=
  (reachable_wf hl r hr).tokens_nodup

/-- A token holds at most one seat: two seats with the same token are the same seat. -/
theorem seat_unique_index {l : Lobby} (hl : Reachable l) {r : Room} (hr : r ∈ l.rooms)
    {i j : Nat} {a b : SeatInfo} (ha : r.seats[i]? = some (some a))
    (hb : r.seats[j]? = some (some b)) (hab : a.token = b.token) : i = j := by
  rw [← Array.getElem?_toList] at ha hb
  exact index_unique_of_nodup (seat_unique hl hr) ha hb hab

/-- A started room always has at least `minSeats` filled seats. -/
theorem started_has_min {l : Lobby} (hl : Reachable l) {r : Room} (hr : r ∈ l.rooms)
    (hs : r.started = true) : r.minSeats ≤ r.filled :=
  (reachable_wf hl r hr).started_min hs

/-- `start` on a room that has not started succeeds iff at least `minSeats` seats are filled. -/
theorem start_iff_min {l : Lobby} {c : String} {r : Room} (h : l.room? c = some r)
    (hns : r.started = false) :
    ((l.step (.start c)).1.room? c).map (·.started) = some true ↔ r.minSeats ≤ r.filled := by
  have hc := (room?_spec h).2
  simp only [step, onRoom, h, Room.start, hns, Bool.false_eq_true, ite_false]
  by_cases hlt : r.filled < r.minSeats
  · simp only [hlt, ite_true, h, Option.map_some, hns]
    simp only [Bool.false_eq_true, Option.some.injEq, false_iff]
    omega
  · simp only [hlt, ite_false]
    rw [room?_put (r' := { r with started := true }) (by simp [h]) hc]
    simp only [Option.map_some, true_iff]
    omega

/-- Joining a full room is rejected and changes nothing. -/
theorem join_full_rejected {l : Lobby} {c : String} {r : Room} (h : l.room? c = some r)
    (hf : r.isFull = true) (name token : String) :
    l.step (.join c name token) = (l, [.rejected c .roomFull]) := by
  simp [step, onRoom, h, Room.join, hf]

/-- Reconnecting with a seated token gives back the same seat (same index, name, token),
now connected; no other seat changes and the started flag is kept. -/
theorem reconnect_restores {l : Lobby} {c t : String} {r : Room} {i : Nat} {s : SeatInfo}
    (h : l.room? c = some r) (hs : r.seatOf? t = some (i, s)) :
    (l.step (.reconnect c t)).2 = [.reconnected c i s.name] ∧
    ∃ r', (l.step (.reconnect c t)).1.room? c = some r' ∧
      r'.seatOf? t = some (i, { s with connected := true }) ∧
      r'.started = r.started ∧
      ∀ j, j ≠ i → r'.seats[j]? = r.seats[j]? := by
  have hc := (room?_spec h).2
  have htok := (Room.seatOf?_spec hs).2
  simp only [step, onRoom, h, Room.reconnect, hs, hc]
  refine ⟨trivial, _, room?_put (by simp [h]) hc, ?_, rfl, ?_⟩
  · simp only [Room.seatOf?, Room.setSeat_toList]
    exact findSeat_set_same (x := { s with connected := true }) htok hs
  · intro j hj
    simp [Room.setSeat, Array.getElem?_setIfInBounds_ne (Ne.symm hj)]

theorem list_set_self {α} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : l.set i a = l := by
  apply List.ext_getElem?
  intro j
  by_cases hij : i = j
  · subst hij
    obtain ⟨hi, hia⟩ := List.getElem?_eq_some_iff.mp h
    simp [hi, hia]
  · simp [List.getElem?_set_ne hij]

/-- In a started room, `leave` then `reconnect` with the same token restores the room exactly
(if the seat was connected before). -/
theorem leave_reconnect_restores {l : Lobby} {c t : String} {r : Room} {i : Nat} {s : SeatInfo}
    (h : l.room? c = some r) (hst : r.started = true) (hs : r.seatOf? t = some (i, s))
    (hcon : s.connected = true) :
    ((l.step (.leave c t)).1.step (.reconnect c t)).1.room? c = some r := by
  have hc := (room?_spec h).2
  obtain ⟨hget, htok⟩ := Room.seatOf?_spec hs
  -- after leave
  have hl1 : (l.step (.leave c t)).1 = l.put c (r.setSeat i (some { s with connected := false })) := by
    simp [step, onRoom, h, Room.leave, hs, hst]
  have h1 : (l.step (.leave c t)).1.room? c = some (r.setSeat i (some { s with connected := false })) := by
    rw [hl1]; exact room?_put (by simp [h]) hc
  have hs1 : (r.setSeat i (some { s with connected := false })).seatOf? t =
      some (i, { s with connected := false }) := by
    simp only [Room.seatOf?, Room.setSeat_toList]
    exact findSeat_set_same (x := { s with connected := false }) htok hs
  generalize (l.step (.leave c t)).1 = l1 at h1
  simp only [step, onRoom, h1, Room.reconnect, hs1]
  rw [room?_put (l := l1) (c := c) (r' := (r.setSeat i (some { s with connected := false })).setSeat i
      (some { name := s.name, token := s.token })) (by simp [h1]) hc]
  congr 1
  have hs' : ({ name := s.name, token := s.token } : SeatInfo) = s := by
    cases s; simp_all
  rw [hs']
  obtain ⟨code, mn, mx, seats, started⟩ := r
  simp only [Room.setSeat, Room.mk.injEq, and_true, true_and]
  apply Array.toList_inj.mp
  simp only [Array.toList_setIfInBounds, List.set_set]
  exact list_set_self hget

end Lobby
