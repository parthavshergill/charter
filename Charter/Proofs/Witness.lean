import Charter.Games.Witnesses

/-!
# Three complete games

The kernel runs the three test games, so these theorems rest on no compiled code. The event lists are
in `Charter/Games/Witnesses.lean`.
-/

namespace Charter.Proofs

open Charter Charter.Engine Charter.Games

theorem witness_of_check {G : GameDef} {r : Except String (State G)}
    (h : endedWithWinnerAndLaw r = true) :
    ∃ s, r = .ok s ∧ s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws ≠ [] ∧
      1 ≤ s.dealsStarted := by
  cases r with
  | error m => simp [endedWithWinnerAndLaw] at h
  | ok s =>
    simp only [endedWithWinnerAndLaw, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨s, rfl, h1, h2, h3, h4⟩

theorem a_full_game_exists :
    ∃ events s, Engine.replay tinySettlers 2 42 [25283273] events = .ok s ∧
      s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws ≠ [] ∧ 1 ≤ s.dealsStarted :=
  ⟨settlersGameEvents, witness_of_check (by decide +kernel)⟩

theorem a_full_space_game_exists :
    ∃ events s, Engine.replay tinySpace 3 7 [23841] events = .ok s ∧
      s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws ≠ [] ∧ 1 ≤ s.dealsStarted :=
  ⟨spaceGameEvents, witness_of_check (by decide +kernel)⟩

theorem a_founded_game_exists :
    ∃ events s, Engine.replay tinyFounded 2 42 [25283273] events = .ok s ∧
      s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws.map (·.1) = [0] := by
  have h : endedWithFoundingLaw
      (Engine.replay tinyFounded 2 42 [25283273] foundedGameEvents) = true := by decide +kernel
  cases hr : Engine.replay tinyFounded 2 42 [25283273] foundedGameEvents with
  | error m =>
    rw [hr] at h
    simp [endedWithFoundingLaw] at h
  | ok s =>
    rw [hr] at h
    simp only [endedWithFoundingLaw, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨foundedGameEvents, s, hr, h.1.1, h.1.2, h.2⟩

end Charter.Proofs
