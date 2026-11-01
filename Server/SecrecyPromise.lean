import Server.SecrecyProofs

/-!
# The secrecy promise

A game can hide some goods, seal its declarations and hide its roll. `Server/Secrecy.lean` says what
each of these means, and defines `observe`, the one function that says what a seat may know. The server
builds everything it sends to a seat from `observe`. That last step is tested, not proved: see
`docs/process/trusted-surface.md`.

The promise has two halves, and it needs both. A function that showed nothing would keep the first half
alone, and a function that showed everything would keep the second half alone.

To read the statements, read `Secrecy`, `observe` and `HiddenDifference` in `Server/Secrecy.lean`.
`Server/SecrecyExamples.lean` meets every hypothesis on a real state, and shows a leak rejected.
-/

namespace CharterServer.Secrecy

open Charter CharterServer

/-- **Nobody sees what is hidden from them.** While a game runs, two states look the same to a viewer
exactly when they differ only in what is hidden from it:

* other seats' holdings of hidden goods, and what the bank and the treasury hold of them,
* the amounts of journal entries in hidden goods that do not touch the viewer's own accounts,
* other seats' sealed declarations,
* a hidden roll, unless it started the viewer's own turn,
* the seed.

From left to right: a seat learns nothing about these from what `observe` gives it. From right to left:
`observe` keeps everything else. -/
theorem nobody_sees_what_is_hidden {G : GameDef} (sec : Secrecy) (viewer : Option Seat)
    (s₁ s₂ : State G) (hRunning : s₁.phase ≠ .ended) :
    observe sec viewer s₁ = observe sec viewer s₂ ↔ HiddenDifference sec viewer s₁ s₂ :=
  SecrecyProofs.observe_eq_iff sec viewer s₁ s₂ hRunning

/-- **The end reveals everything.** Once a game has ended, every seat and every spectator sees the
whole state. So a replay of a finished game hides nothing. -/
theorem the_end_reveals_everything {G : GameDef} (sec : Secrecy) (viewer : Option Seat)
    (s : State G) (hEnded : s.phase = .ended) :
    observe sec viewer s = s :=
  SecrecyProofs.observe_ended sec viewer s hEnded

/-- **A game that marks nothing hides only the seed.** Every game made before secrecy existed sees
what it saw before. -/
theorem unmarked_games_hide_only_the_seed {G : GameDef} (viewer : Option Seat) (s : State G)
    (hRunning : s.phase ≠ .ended) :
    observe {} viewer s = { s with seed := 0 } :=
  SecrecyProofs.observe_unmarked viewer s hRunning

end CharterServer.Secrecy
