import Lobby.Basic

/-! Helper lemmas about seat lists, rooms, and `Lobby.put`. -/

namespace Lobby

/-! ## Seat lists -/

theorem findSeat_spec {t : String} :
    ∀ {l : List (Option SeatInfo)} {i : Nat} {s : SeatInfo},
      findSeat t l = some (i, s) → l[i]? = some (some s) ∧ s.token = t
  | [], _, _, h => by simp [findSeat] at h
  | none :: tl, i, s, h => by
    cases hf : findSeat t tl with
    | none => simp [findSeat, hf] at h
    | some p =>
      obtain ⟨a, b⟩ := p
      simp [findSeat, hf] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using findSeat_spec hf
  | some x :: tl, i, s, h => by
    by_cases hx : x.token = t
    · simp [findSeat, hx] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [hx]
    · cases hf : findSeat t tl with
      | none => simp [findSeat, hx, hf] at h
      | some p =>
        obtain ⟨a, b⟩ := p
        simp [findSeat, hx, hf] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using findSeat_spec hf

theorem findSeat_none {t : String} :
    ∀ {l : List (Option SeatInfo)}, findSeat t l = none →
      t ∉ (l.filterMap id).map (·.token)
  | [], _ => by simp
  | none :: tl, h => by
    cases hf : findSeat t tl with
    | none => simpa using findSeat_none hf
    | some p => simp [findSeat, hf] at h
  | some x :: tl, h => by
    by_cases hx : x.token = t
    · simp [findSeat, hx] at h
    · cases hf : findSeat t tl with
      | none =>
        have := findSeat_none hf
        simp only [List.filterMap_cons, id, List.map_cons, List.mem_cons, not_or]
        exact ⟨Ne.symm hx, this⟩
      | some p => simp [findSeat, hx, hf] at h

theorem firstEmpty_spec :
    ∀ {l : List (Option SeatInfo)} {i : Nat}, firstEmpty l = some i → l[i]? = some none
  | [], _, h => by simp [firstEmpty] at h
  | none :: _, i, h => by
    simp [firstEmpty] at h
    subst h; simp
  | some _ :: tl, i, h => by
    cases hf : firstEmpty tl with
    | none => simp [firstEmpty, hf] at h
    | some j =>
      simp [firstEmpty, hf] at h
      subst h
      simpa using firstEmpty_spec hf

theorem firstEmpty_none_iff :
    ∀ {l : List (Option SeatInfo)}, firstEmpty l = none ↔ ∀ x ∈ l, x.isSome
  | [] => by simp [firstEmpty]
  | none :: _ => by simp [firstEmpty]
  | some _ :: tl => by
    simp [firstEmpty, firstEmpty_none_iff (l := tl)]

theorem filterMap_set_none_perm {x : SeatInfo} :
    ∀ {l : List (Option SeatInfo)} {i : Nat}, l[i]? = some none →
      ((l.set i (some x)).filterMap id).Perm (x :: l.filterMap id)
  | [], _, h => by simp at h
  | none :: tl, 0, _ => by simp
  | some y :: tl, 0, h => by simp at h
  | none :: tl, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa using filterMap_set_none_perm h
  | some y :: tl, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, List.filterMap_cons, id]
    exact ((filterMap_set_none_perm h).cons y).trans (List.Perm.swap x y _)

theorem filterMap_set_none_sublist :
    ∀ {l : List (Option SeatInfo)} {i : Nat}, ((l.set i none).filterMap id).Sublist (l.filterMap id)
  | [], _ => by simp
  | none :: tl, 0 => by simp
  | some y :: tl, 0 => by simp
  | none :: tl, i + 1 => by
    simpa using (filterMap_set_none_sublist (l := tl) (i := i))
  | some y :: tl, i + 1 => by
    simp only [List.set_cons_succ, List.filterMap_cons, id]
    exact (filterMap_set_none_sublist (l := tl) (i := i)).cons_cons y

theorem tokens_set_same {s x : SeatInfo} (hx : x.token = s.token) :
    ∀ {l : List (Option SeatInfo)} {i : Nat}, l[i]? = some (some s) →
      ((l.set i (some x)).filterMap id).map (·.token) = (l.filterMap id).map (·.token)
  | [], _, h => by simp at h
  | none :: tl, 0, h => by simp at h
  | some y :: tl, 0, h => by
    simp at h; subst h; simp [hx]
  | none :: tl, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa using tokens_set_same hx h
  | some y :: tl, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa using tokens_set_same hx h

theorem length_set_same {s x : SeatInfo} :
    ∀ {l : List (Option SeatInfo)} {i : Nat}, l[i]? = some (some s) →
      ((l.set i (some x)).filterMap id).length = (l.filterMap id).length
  | [], _, h => by simp at h
  | none :: tl, 0, h => by simp at h
  | some y :: tl, 0, _ => by simp
  | none :: tl, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa using length_set_same h
  | some y :: tl, i + 1, h => by
    simp only [List.getElem?_cons_succ] at h
    simpa using length_set_same h

theorem findSeat_set_same {t : String} {x : SeatInfo} (hx : x.token = t) :
    ∀ {l : List (Option SeatInfo)} {i : Nat} {s : SeatInfo},
      findSeat t l = some (i, s) → findSeat t (l.set i (some x)) = some (i, x)
  | [], _, _, h => by simp [findSeat] at h
  | none :: tl, i, s, h => by
    cases hf : findSeat t tl with
    | none => simp [findSeat, hf] at h
    | some p =>
      obtain ⟨a, b⟩ := p
      simp [findSeat, hf] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [findSeat, findSeat_set_same hx hf]
  | some y :: tl, i, s, h => by
    by_cases hy : y.token = t
    · simp [findSeat, hy] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [findSeat, hx]
    · cases hf : findSeat t tl with
      | none => simp [findSeat, hy, hf] at h
      | some p =>
        obtain ⟨a, b⟩ := p
        simp [findSeat, hy, hf] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [findSeat, hy, findSeat_set_same hx hf]

theorem mem_filterMap_of_getElem? {l : List (Option SeatInfo)} {i : Nat} {s : SeatInfo}
    (h : l[i]? = some (some s)) : s ∈ l.filterMap id := by
  rw [List.mem_filterMap]
  exact ⟨some s, List.mem_of_getElem? h, rfl⟩

/-- Distinct tokens means a token names at most one seat index. -/
theorem index_unique_of_nodup :
    ∀ {l : List (Option SeatInfo)} {i j : Nat} {a b : SeatInfo},
      ((l.filterMap id).map (·.token)).Nodup →
      l[i]? = some (some a) → l[j]? = some (some b) → a.token = b.token → i = j
  | [], _, _, _, _, _, ha, _, _ => by simp at ha
  | _ :: _, 0, 0, _, _, _, _, _, _ => rfl
  | hd :: tl, 0, j + 1, a, b, hn, ha, hb, hab => by
    simp at ha; subst ha
    simp only [List.getElem?_cons_succ] at hb
    simp only [List.filterMap_cons, id, List.map_cons, List.nodup_cons] at hn
    exact absurd (hab ▸ List.mem_map_of_mem (f := (·.token)) (mem_filterMap_of_getElem? hb)) hn.1
  | hd :: tl, i + 1, 0, a, b, hn, ha, hb, hab => by
    simp at hb; subst hb
    simp only [List.getElem?_cons_succ] at ha
    simp only [List.filterMap_cons, id, List.map_cons, List.nodup_cons] at hn
    exact absurd (hab ▸ List.mem_map_of_mem (f := (·.token)) (mem_filterMap_of_getElem? ha)) hn.1
  | hd :: tl, i + 1, j + 1, a, b, hn, ha, hb, hab => by
    simp only [List.getElem?_cons_succ] at ha hb
    have hn' : ((tl.filterMap id).map (·.token)).Nodup := by
      cases hd with
      | none => simpa using hn
      | some y => simp only [List.filterMap_cons, id, List.map_cons, List.nodup_cons] at hn; exact hn.2
    rw [index_unique_of_nodup hn' ha hb hab]

/-! ## Rooms -/

namespace Room

@[simp] theorem setSeat_toList {r : Room} {i : Nat} {s : Option SeatInfo} :
    (r.setSeat i s).seats.toList = r.seats.toList.set i s := by
  simp [setSeat]

@[simp] theorem setSeat_code {r : Room} {i s} : (r.setSeat i s).code = r.code := rfl
@[simp] theorem setSeat_started {r : Room} {i s} : (r.setSeat i s).started = r.started := rfl
@[simp] theorem setSeat_min {r : Room} {i s} : (r.setSeat i s).minSeats = r.minSeats := rfl
@[simp] theorem setSeat_max {r : Room} {i s} : (r.setSeat i s).maxSeats = r.maxSeats := rfl
@[simp] theorem setSeat_size {r : Room} {i s} : (r.setSeat i s).seats.size = r.seats.size := by
  simp [setSeat]

theorem isFull_iff {r : Room} : r.isFull = true ↔ ∀ x ∈ r.seats.toList, x.isSome := by
  simp only [isFull, Option.isNone_iff_eq_none]
  exact firstEmpty_none_iff

theorem seatOf?_spec {r : Room} {t : String} {i : Nat} {s : SeatInfo}
    (h : r.seatOf? t = some (i, s)) : r.seats.toList[i]? = some (some s) ∧ s.token = t :=
  findSeat_spec h

/-- Changing a filled seat to another seat with the same token keeps tokens and count. -/
theorem setSeat_same_token {r : Room} {i : Nat} {s x : SeatInfo}
    (h : r.seats.toList[i]? = some (some s)) (hx : x.token = s.token) :
    (r.setSeat i (some x)).tokens = r.tokens ∧ (r.setSeat i (some x)).filled = r.filled := by
  simp only [tokens, filled, occupants, setSeat_toList]
  exact ⟨tokens_set_same hx h, length_set_same h⟩

theorem new_wf {c : String} {min max : Nat} (h0 : 0 < min) (h1 : min ≤ max) :
    (Room.new c min max).WF where
  size_eq := by simp [Room.new]
  min_pos := h0
  min_le_max := h1
  tokens_nodup := by
    simp [Room.new, tokens, occupants]
  started_min := by simp [Room.new]

theorem join_wf {r r' : Room} {n t : String} {no : Notice} (hw : r.WF)
    (h : r.join n t = .ok (r', no)) : r'.WF ∧ r'.code = r.code := by
  unfold join at h
  split at h; · cases h
  split at h; · cases h
  rename_i _ hst
  split at h; · cases h
  rename_i hseat
  split at h; · cases h
  rename_i i hi
  cases h
  have hnone := firstEmpty_spec hi
  have hperm := filterMap_set_none_perm (x := { name := n, token := t, connected := true }) hnone
  refine ⟨⟨by simp [hw.size_eq], hw.min_pos, hw.min_le_max, ?_, ?_⟩, rfl⟩
  · simp only [tokens, occupants, setSeat_toList]
    rw [(hperm.map _).nodup_iff]
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨findSeat_none hseat, hw.tokens_nodup⟩
  · simp [hst]

theorem reconnect_wf {r r' : Room} {t : String} {no : Notice} (hw : r.WF)
    (h : r.reconnect t = .ok (r', no)) : r'.WF ∧ r'.code = r.code := by
  unfold reconnect at h
  split at h; · cases h
  rename_i i s hs
  cases h
  obtain ⟨hget, _⟩ := seatOf?_spec hs
  obtain ⟨htok, hfill⟩ := setSeat_same_token (x := { s with connected := true }) hget rfl
  refine ⟨⟨by simp [hw.size_eq], hw.min_pos, hw.min_le_max, ?_, ?_⟩, rfl⟩
  · rw [htok]; exact hw.tokens_nodup
  · rw [hfill]; simpa using hw.started_min

theorem leave_wf {r r' : Room} {t : String} {no : Notice} (hw : r.WF)
    (h : r.leave t = .ok (r', no)) : r'.WF ∧ r'.code = r.code := by
  unfold leave at h
  split at h; · cases h
  rename_i i s hs
  obtain ⟨hget, _⟩ := seatOf?_spec hs
  split at h
  · cases h
    obtain ⟨htok, hfill⟩ := setSeat_same_token (x := { s with connected := false }) hget rfl
    refine ⟨⟨by simp [hw.size_eq], hw.min_pos, hw.min_le_max, ?_, ?_⟩, rfl⟩
    · rw [htok]; exact hw.tokens_nodup
    · rw [hfill]; simpa using hw.started_min
  · rename_i hst
    cases h
    refine ⟨⟨by simp [hw.size_eq], hw.min_pos, hw.min_le_max, ?_, ?_⟩, rfl⟩
    · simp only [tokens, occupants, setSeat_toList]
      exact (filterMap_set_none_sublist.map _).nodup hw.tokens_nodup
    · simp [hst]

theorem start_wf {r r' : Room} {no : Notice} (hw : r.WF)
    (h : r.start = .ok (r', no)) : r'.WF ∧ r'.code = r.code := by
  unfold start at h
  split at h; · cases h
  split at h; · cases h
  rename_i hlt
  cases h
  exact ⟨⟨hw.size_eq, hw.min_pos, hw.min_le_max, hw.tokens_nodup,
    fun _ => Nat.le_of_not_lt hlt⟩, rfl⟩

end Room

/-! ## Lobby plumbing -/

theorem room?_spec {l : Lobby} {c : String} {r : Room} (h : l.room? c = some r) :
    r ∈ l.rooms ∧ r.code = c := by
  unfold room? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem mem_put {l : Lobby} {c : String} {r r' : Room} (h : r ∈ (l.put c r').rooms) :
    r ∈ l.rooms ∨ r = r' := by
  simp only [put, List.mem_map] at h
  obtain ⟨x, hx, rfl⟩ := h
  by_cases hc : x.code = c
  · simp [hc]
  · simp [hc, hx]

theorem room?_put {l : Lobby} {c : String} {r' : Room}
    (h : (l.room? c).isSome) (hc : r'.code = c) : (l.put c r').room? c = some r' := by
  obtain ⟨rooms⟩ := l
  simp only [room?, put] at *
  rw [List.find?_isSome] at h
  simp only [beq_iff_eq] at h
  induction rooms with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x.code = c
    · simp [hx, hc]
    · simp only [List.mem_cons] at h
      have h' : ∃ a, a ∈ xs ∧ a.code = c := by
        obtain ⟨a, ha | ha, hac⟩ := h
        · subst ha; exact absurd hac hx
        · exact ⟨a, ha, hac⟩
      rw [List.map_cons, List.find?_cons_of_neg (by simp [hx])]
      exact ih h'

/-- Shape of `onRoom`'s result. -/
theorem onRoom_cases {l : Lobby} {c : String} {f : Room → Except Reject (Room × Notice)} :
    (l.onRoom c f).1 = l ∨
      ∃ r r' n, l.room? c = some r ∧ f r = .ok (r', n) ∧ (l.onRoom c f) = (l.put c r', [n]) := by
  unfold onRoom
  split
  · exact .inl rfl
  · rename_i r hr
    split
    · exact .inl rfl
    · rename_i r' n hf
      exact .inr ⟨r, r', n, hr, hf, rfl⟩

end Lobby
