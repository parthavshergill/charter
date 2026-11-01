import Charter.Engine.Step
import Charter.Engine.Sha256

/-!
# The Charter engine

A pure, executable game engine. It imports only `Charter.Words` and what that imports. Read in this order:

* `Engine/Basic.lean`: posting to the books, counting actions, ending the game.
* `Engine/Deals.lean`: starting, signing and leaving deals.
* `Engine/Turn.lean`: the turn change and the preview, which share one definition.
* `Engine/Moves.lean`: one function per move.
* `Engine/Proposals.lean`: proposals and votes.
* `Engine/Step.lean`: `step`, `replay` and `legalMoves`.
* `Engine/Sha256.lean`: tests of the SHA-256 in `Charter/Sha256.lean`.
-/
