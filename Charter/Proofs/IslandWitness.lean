import Charter.Constitution.Supporting
import Charter.Games.IslandGameEvents

/-!
# A complete game of the real Island

The promises begin "for any state that can really happen in a valid game". `Charter/Proofs/Witness.lean`
shows that such states exist for three test games. This file shows it for the real Island, at 4 seats,
with the real dice. The kernel replays every event through `Engine.step`, so no compiled code is trusted.

The game is in `Charter/Games/IslandGameEvents.lean`. Four bots played it with the policy in
`Server/Bots.lean`, and `scripts/island_game.lean` added one deal and one law. Nothing here changes the
Island or the engine.

The server does not import this file.
-/

namespace Charter.Proofs

open Charter Charter.Engine Charter.Games.Island

/-- What `a_full_island_game_exists` says about a game's end, as a test the kernel can run. -/
def islandGameEndedAsPlayed (r : Except String (State island)) : Bool :=
  match r with
  | .ok s =>
    s.phase == .ended && s.winner == some 2 && s.turnOrder.map s.pointsOf == [9, 6, 10, 6] &&
      decide (island.targetPoints ≤ s.pointsOf 2) && decide (s.round < island.rounds) &&
      !s.lawEnds && s.laws.map (·.1) == [1] && decide (1 ≤ s.dealsStarted)
  | .error _ => false

/-- A complete game of the real Island exists. Seat 2 wins by reaching the target, before the round
limit, and no law ended the game. Scores are 9, 6, 10 and 6. One law, with id 1, is in force at the end,
and one deal started. -/
theorem a_full_island_game_exists :
    ∃ events s, Engine.replay island 4 1 [1, 2, 3, 4] events = .ok s ∧
      s.phase = .ended ∧ s.winner = some 2 ∧ s.turnOrder.map s.pointsOf = [9, 6, 10, 6] ∧
      island.targetPoints ≤ s.pointsOf 2 ∧ s.round < island.rounds ∧ s.lawEnds = false ∧
      s.laws.map (·.1) = [1] ∧ 1 ≤ s.dealsStarted := by
  have h : islandGameEndedAsPlayed
      (Engine.replay island 4 1 [1, 2, 3, 4] islandGameEvents) = true := by decide +kernel
  cases hr : Engine.replay island 4 1 [1, 2, 3, 4] islandGameEvents with
  | error m =>
    rw [hr] at h
    simp [islandGameEndedAsPlayed] at h
  | ok s =>
    rw [hr] at h
    simp only [islandGameEndedAsPlayed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    exact ⟨islandGameEvents, s, hr, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The Island starts with no laws, so the law in force at the end got there by a vote. -/
theorem island_starts_with_no_laws : island.startingLaws = [] := rfl

/-- The vote on the law: seat 3 says no, then seats 0, 1 and 2 say yes. Three of four is a majority. -/
example : votesOn 1 islandGameEvents = [(3, false), (0, true), (1, true), (2, true)] := by
  decide +kernel

/-- The events depend on the dice. With another server seed, the same events are rejected. -/
example : (Engine.replay island 4 2 [1, 2, 3, 4] islandGameEvents).toOption.isNone = true := by
  decide +kernel

/-- A state of the real Island that has really happened, with a winner and a law in force. So the
promises' conditions can be met on the real game. -/
theorem a_finished_island_game_can_happen :
    ∃ s, Reachable island s ∧ s.phase = .ended ∧ s.winner = some 2 ∧ s.laws ≠ [] := by
  obtain ⟨events, s, hr, h1, h2, -, -, -, -, h3, -⟩ := a_full_island_game_exists
  have hs : Reachable island s :=
    ((Charter.X_what_you_vote_on_is_what_runs island island_valid).1 s).2
      ⟨4, 1, [1, 2, 3, 4], events, by decide, by decide, hr⟩
  refine ⟨s, hs, h1, h2, ?_⟩
  intro h
  simp [h] at h3

/-- `the_winner_earned_it` on this game, with every condition met: seat 2 has the most points. -/
example : ∃ s, Reachable island s ∧ ∀ p ∈ s.turnOrder, s.pointsOf p ≤ s.pointsOf 2 := by
  obtain ⟨s, hs, -, h2, -⟩ := a_finished_island_game_can_happen
  exact ⟨s, hs, ((Charter.the_winner_earned_it island island_valid s hs).1 2 h2).2.2.1⟩

end Charter.Proofs
