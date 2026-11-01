import Charter.Words.Game
import Charter.Words.RuleLanguage
import Charter.Words.GameDef
import Charter.Words.Books
import Charter.Words.Deal
import Charter.Words.State
import Charter.Words.Fast
import Charter.Words.LawEffects
import Charter.Words.Payments
import Charter.Words.Placing
import Charter.Words.LawChecks
import Charter.Words.DealChecks
import Charter.Words.Turns
import Charter.Words.Dice
import Charter.Words.Valid
import Charter.Words.Renaming

/-!
# The words the constitution uses

A theorem means only what its words mean. These files define the words. Read them in this order:

* `Words/Game.lean`: names, limits, and the parts of a game.
* `Words/RuleLanguage.lean`: what a law can say.
* `Words/GameDef.lean`: what a game is, including its founding laws.
* `Words/Books.lean`: accounts, entries and the journal.
* `Words/Deal.lean`: what a deal can say.
* `Words/State.lean`: the game state, events, and the rules in force.
* `Words/Turns.lean`: what comes after a turn, and how long a game can be.
* `Words/Fast.lean`: `settle`, which shrinks payments when an account is short, and faster code for it
  that is proved equal.
* `Words/LawEffects.lean`: what a law does when it runs, the dice payout, and the whole of a roll.
* `Words/Payments.lean`: what deals owe, and what trades and fees move.
* `Words/Placing.lean`: when a build is allowed, what it costs, and the board after it.
* `Words/LawChecks.lean`: which laws can pass.
* `Words/DealChecks.lean`: which deals can run.
* `Words/Dice.lean`: the seed, a new game, and the dice.
* `Words/Valid.lean`: the checks every game must pass.
* `Words/Renaming.lean`: what it means to rename every seat.

Three things are defined elsewhere:

* `Engine.step`, `Engine.replay` and `Engine.predictNextTurn` are in `Charter/Engine`. They are the
  code that runs, so the theorems are about them.
* `Sha256.hash` and its helpers are in `Charter/Sha256.lean`.
* Lists, numbers and strings come from Lean itself.
-/
