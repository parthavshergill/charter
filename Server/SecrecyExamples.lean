import Server.SecrecyPromise
import Charter.Games.Tiny

/-!
# The secrecy promise, on real states

A two-seat game of Tiny Settlers in which grain is hidden. In one state seat 1 holds 5 grain, and in the
other it holds 9, with a different seed.
-/

namespace CharterServer.SecrecyExamples

open Charter CharterServer CharterServer.Secrecy

/-- Grain is hidden. -/
def grainHidden : Secrecy := { hidden := ["grain"] }

/-- A new two-seat game. -/
def start : State Charter.tinySettlers := initialState Charter.tinySettlers 2 0 [0]

/-- `start`, with seat 1 holding `n` grain and the seed set to `seed`. -/
def withGrain (n : Nat) (seed : UInt64) : State Charter.tinySettlers :=
  { start with
    books := fun a r => if a = .player 1 ∧ r = "grain" then n else start.books a r
    seed := seed }

/-- The game is running, so the promise applies. -/
example : (withGrain 5 1).phase ≠ .ended := by decide

/-- The two states differ only in what seat 0 may not see, and in what a spectator may not see. -/
theorem only_hidden_things_differ (v : Option Seat) (hv : v ≠ some 1) :
    HiddenDifference grainHidden v (withGrain 5 1) (withGrain 9 2) := by
  refine ⟨rfl, ?_, by simp [withGrain, start, initialState], ?_, ?_⟩
  · intro a r hSee
    have : ¬ (a = .player 1 ∧ r = "grain") := by
      rintro ⟨rfl, rfl⟩
      simp [Secrecy.seesHolding, Secrecy.owns, grainHidden, hv] at hSee
    simp [State.balance, withGrain, this]
  · intros; rfl
  · intros; rfl

/-- So seat 0 sees the same. -/
example : observe grainHidden (some 0) (withGrain 5 1) = observe grainHidden (some 0) (withGrain 9 2) :=
  (nobody_sees_what_is_hidden _ _ _ _ (by decide)).2 (only_hidden_things_differ _ (by decide))

/-- A spectator sees the same too. -/
example : observe grainHidden none (withGrain 5 1) = observe grainHidden none (withGrain 9 2) :=
  (nobody_sees_what_is_hidden _ _ _ _ (by decide)).2 (only_hidden_things_differ _ (by decide))

/-- Seat 1 owns that grain, so it sees the difference. A function that hid a seat's own hand from it
would break the promise. -/
example : observe grainHidden (some 1) (withGrain 5 1) ≠ observe grainHidden (some 1) (withGrain 9 2) := by
  intro h
  have := congrArg (fun s => s.balance (.player 1) "grain") h
  simp [observe, withGrain, start, initialState, State.balance, Secrecy.seesHolding, Secrecy.owns] at this

/-- **A leak is rejected.** A server that sent the whole state would break the promise: seat 0 would
tell these two states apart, though they differ only in what is hidden from it. -/
example : ¬ ∀ s₁ s₂ : State Charter.tinySettlers,
    HiddenDifference grainHidden (some 0) s₁ s₂ → s₁ = s₂ := by
  intro leak
  have := congrArg (fun s => s.balance (.player 1) "grain")
    (leak _ _ (only_hidden_things_differ (some 0) (by decide)))
  simp [withGrain, State.balance] at this

/-- A game that marks nothing still hides the seed: these two states differ only in their seed. -/
example : observe {} (some 0) (withGrain 5 1) = observe {} (some 0) (withGrain 5 2) := by
  rw [unmarked_games_hide_only_the_seed _ _ (by decide), unmarked_games_hide_only_the_seed _ _ (by decide)]
  rfl

end CharterServer.SecrecyExamples
