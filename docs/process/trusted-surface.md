# The trusted surface

A theorem means what its statement says. The statement means what every definition it mentions means, and so on through those definitions' bodies. So a reader must review those definitions. This document lists them, says what is trusted, and says what is only tested.

To print the list for yourself:

    lake env lean --run scripts/spec_surface.lean --list

The script stops at `Charter.Engine`. The engine is the code the theorems are about, so a reader does not need to trust its body. It also leaves out what Lean generates, such as structure fields and match helpers. For a pair of functions defined together, such as `Effect.plan` and `Effect.planAll`, it lists only the second, because Lean compiles the first into it.

## Size

The ten commandments and the six supporting promises mention 321 definitions in all. Of these, 75 are the short named parts in `Charter/Constitution/Promises.lean`.

| Text a reader must review | Size |
|---|---|
| The commandments | 253 lines in `Constitution.lean` |
| The named parts | 607 lines in `Constitution/Promises.lean` |
| The words | 2,062 lines, in 16 files by topic. `Fast.lean` holds faster code that is proved equal to the plain words, and a reader can skip all of it but `settle` |
| SHA-256 | 111 lines |

Two kinds of text are outside the surface: the tiny games, in `Games/Tiny.lean`; and the examples and rejection tests, in `Constitution/Examples.lean`.

## The definitions, by topic

Each row is one group. `Promises` means `Charter/Constitution/Promises.lean`, and the other files are in `Charter/Words`.

| Topic | File | Count | What it means, and why it is here |
|---|---|---|---|
| How a game runs | `Promises` | 4 | `Reachable`, `EndsTurn`, `newEntries`, `LawPasses`. Which states can happen, which events end a turn, what entries a step added, and which vote passes a law. |
| Parts of commandment I | `Promises` | 2 | The books match the journal, and the journal only grows. |
| Parts of commandment III | `Promises` | 17 | Who can change the laws, what can happen to an open proposal, and how actions, declarations and the phase can change. |
| Parts of commandment IV | `Promises` | 3 | Deposits cover debts, deals pay what is due, and the list of builds is true. |
| Parts of commandment V | `Promises` | 17 | The one list of ways money can enter or leave each kind of account. |
| Parts of commandment VI | `Promises` | 10 | How long a deal can run, what can change it, and whom it can restrict. |
| Parts of commandments VII to IX | `Promises` | 10 | The exact charge of a build, how the dice roll, who can end a turn, and where a turn goes. |
| Parts of commandment X | `Promises` | 5 | Replay, the preview, and the exact entries of a turn change. |
| Parts of `bank_trades_and_setup_are_exact` | `Promises` | 7 | When a bank trade or a setup placement is accepted, and exactly what each one does. |
| Names and limits | `Game` | 26 | Seats, resources, the parts of a game and the fixed limits. The limits keep a game finite and a turn fast. |
| What a game is | `GameDef` | 8 | A game as data, including its founding laws. |
| Which games can run | `Valid` | 5 | The checks in `GameDef.Valid`. Every promise assumes them. A founding law must pass `lawProblems` at every allowed number of seats. |
| Accounts and the journal | `Books` | 7 | Where resources are, and how an entry moves them in full or fails. Commandment I rests on this. |
| The rule language | `RuleLanguage` | 10 | What a law can say. It has no way to name a seat, which commandment II rests on. |
| What a deal can say | `Deal` | 8 | Signers, deposits, terms, and the most a deal can owe per round. |
| State and events | `State` | 36 | The game state, every event, and the rules in force, which are computed from the laws. |
| What a law does | `LawEffects` | 26 | The meaning of the rule language, what the dice pay out, and the whole of a roll, with the seat whose turn it starts. |
| How a shortfall is settled | `Fast` | 1 | `settle`. |
| Payments | `Payments` | 21 | What deals owe at a round's end, refunds, trades and fees. Commandments IV, V and X state these exactly. |
| Placing a piece | `Placing` | 9 | When a build is allowed, what it costs, and the board after it. Commandment VII rests on this. |
| Which laws can pass | `LawChecks` | 30 | `lawProblems` and what it needs. These keep laws small and stop laws that would do nothing. |
| Which deals can run | `DealChecks` | 7 | `dealProblems`, the deposits a deal must hold, and when one can start. |
| Turns | `Turns` | 6 | What follows each turn, and the most turns and events a game can have. |
| Seed and dice | `Dice` | 6 | The fingerprint, the game's seed, a new game, and each roll. Commandment VIII rests on this. |
| Renaming | `Renaming` | 15 | What it means to rename every seat. Only commandment II uses these. |
| SHA-256 | `Charter/Sha256.lean` | 22 | The hash behind the fingerprint and the seed. |
| The code under test | `Charter/Engine` | 3 | `Engine.step`, `Engine.replay` and `Engine.predictNextTurn`. The theorems are about these. Their bodies are not part of the surface. |

## What each promise adds

All ten commandments rest on the same 134 definitions: the data types of a game, `GameDef.Valid`, `Reachable`, `Engine.step`, `initialState`, the seed functions, SHA-256, and `lawProblems` with everything it reads, because `GameDef.Valid` checks founding laws with it. The table shows what each promise needs on top of those.

| Promise | Total | Added | Main additions |
|---|---|---|---|
| I | 142 | 8 | Posting entries, the list of accounts, the total of a resource |
| II | 149 | 15 | `Renaming` |
| III | 164 | 30 | Votes, `ProposalsKept`, `nextStage`, how actions and the phase change |
| IV | 154 | 20 | `worstCase`, `duePayments`, `BuildsRecorded` |
| V | 218 | 84 | The named parts of V, `lawEntries`, `harvestEntries`, `rollEntries`, `settle`, `roundEndEntries`, trades and fees |
| VI | 153 | 19 | `DealsKept`, `dealAfter`, `closingDeals`, `blockedByDeal`, `tradeBlocked` |
| VII | 166 | 32 | `canPlace`, `placedPieces`, `costEntries`, `lawEntries`, `settle` |
| VIII | 147 | 13 | `rollAt`, `dieAt`, `scramble`, `nextStage` |
| IX | 150 | 16 | `maxTurns`, `maxEvents`, `TurnMovedOn`, `nextStage` |
| X | 199 | 65 | `Engine.replay`, `Engine.predictNextTurn`, `lawEntries`, `harvestEntries`, `rollEntries`, `roundEndEntries` |
| `the_winner_earned_it` | 142 | 8 | `pointsOf`, `maxTurns`, `MajorityEndedTheGame` |
| `limits_hold` | 136 | 2 | `maxActiveDeals`, `maxOpenPerSeat` |
| `every_other_event_is_exact` | 165 | 31 | `depositEntries`, `refundEntries`, `settle`, `VoteWritesExactly`, `DeclarationsKept` |
| `bank_trades_and_setup_are_exact` | 154 | 20 | `bankTradeEntries`, `refundEntries`, `placedPieces`, `placementOk`, its named parts |
| `proposals_are_accepted` | 144 | 10 | `dealProblems` and its checks |
| `deals_can_start` | 150 | 16 | `dealProblems`, `canStartDeal`, `depositEntries` |

## What is trusted

- **The Lean kernel and compiler.** The kernel checks the proofs. The compiler builds the server that runs `Engine.step`. No proof uses `native_decide`, so no proof trusts the compiler.
- **Lean's own library.** Lists, numbers and strings come from it. So does the hash table in `Charter/Words/Fast.lean`, whose lemmas the `@[csimp]` theorems use.
- **`@[csimp]`.** The compiler runs the faster function that each such theorem proves equal to a plain one. The kernel checks the equality. The compiler is already trusted to do the replacement.
- **The server's duties.** The theorems cannot see four things. The server must decide who may send an event for a seat. It must decide who may send `forceEndTurn`. It must publish the fingerprint first, use each player's own nonce, when the player supplies one, and keep its seed from clients until the game ends. It must check `G.Valid` before it runs a game, because the engine never checks it. For the Island, `island_valid` proves that check.
- **The seed's size.** `commitmentOf` hashes a 64-bit seed with no salt. A very large search could find the seed from its fingerprint.
- **SHA-256, to hide the seed.** Neither side alone can choose the dice, assuming four things. The server publishes the fingerprint before players add nonces. It uses each player's own nonce, when the player supplies one. It keeps its seed secret until the game ends. SHA-256 hides the seed. These assumptions are not proved.

## What no theorem covers

- **The screen.** Nothing proves that it shows the true state, or that it sends what a player chose.
- **A law's description.** It is Claude's words. A pack's founding laws have the pack's own words in its place. No proof and no sentence test stands behind either. They can be wrong. The rule source right below them is what counts, and that is what the screen shows every player and every Claude seat as the binding text.
- **The clerk.** Nothing proves that the rule it writes is the rule a player asked for. Its `DIFFERENCE` line is its own account of the gap. It says nothing about the description.
- **A law's title.** It is free text with no meaning in the game. The description call does not see it.
- **Fair dice.** Nothing proves the rolls are fair. Commandment VIII says only that nobody can change them after the seed is fixed.

## What is tested but not proved

- **SHA-256 is the real SHA-256.** `Charter/Engine/Sha256.lean` checks the NIST example vectors and the padding boundaries. `Charter/EngineTests.lean` checks two more values against Python's `hashlib`.
- **Which offers stay open.** `OffersKept` says that no offer appears from nowhere or changes. It does not say that a cancel or an accept removes only that offer, or that a turn end clears them. `Charter/EngineTests.lean` checks these.
- **The engine's own helpers.** `legalMoves`, which the screen uses, has tests and no theorem.
- **Every seat can place its setup pieces.** `Charter/EngineTests.lean` checks this for the tiny games. `Charter/Games/IslandTests.lean` checks the settlements for the Island, and shows one way a road can be blocked at 4 seats. A one-time search found no such block at 2 and 3 seats. That search is not kept, so nothing checks that result again.
- **The preview on the screen.** Commandment X proves `predictNextTurn` is exact. That the screen shows its result is tested only. So are the preview's build cases, which use what commandment VII states.
- **The promises on real games.** `Charter/EngineTests.lean` runs a checker of the constitution's claims on every step of complete and random games. The file has 536 `#guard`s and `example`s.
- **A deal's sentences.** `ServerTests.lean` writes each one out in full.
- **The clerk and the descriptions, as code.** `make clerk-check` tests the clerk's memory and reply handling. It tests what a description call sends, that a description goes only with the law it was written for, that no client can supply one, and what shows when there is none. The check of what descriptions say was a one-time test, and `docs/process/reviews.md` gives its results.
- **The whole server.** `make smoke` plays a full game over HTTP, restarts the server, and checks that the game replays from its log.

## A full game of the real Island

`a_full_island_game_exists`, in `Charter/Proofs/IslandWitness.lean`, has the kernel replay one complete game of the real Island at 4 seats, through `Engine.step`, with the real dice. So the promises' conditions can be met on the real game, not only on the three test games. Bots played the game, and a script added one deal and one law. The events are in `Charter/Games/IslandGameEvents.lean`, which `scripts/island_game.lean` writes. The server does not import this theorem. If a change to the Island or the engine makes the game illegal, the build fails, and that script can play a new game.

## How the proofs are checked

`make audit` does three things, with no sandbox, so it runs on macOS:

1. It prints the axioms of each promise, and fails if any theorem in a `Charter` module rests on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. `sorry` would appear here as `sorryAx`.
2. It runs `leanchecker` on the spec, the engine, the proofs and the constitution, which replays them through the kernel.
3. It scans `Charter` for banned constructs, such as `sorry`, `axiom`, `native_decide` and `unsafe`.

### Comparator

`bash scripts/comparator.sh` runs Lean's Comparator, `lake comparator`, inside its bubblewrap sandbox. Comparator needs Linux, so the script uses a Docker container. CI runs it on each pull request that can change a theorem. `make audit` does not run it, and neither replaces the other.

Comparator accepted 22 theorems, which `comparator.json` lists: the ten commandments, the six supporting promises, and the six witnesses in `Charter/Proofs/Witness.lean` and `Charter/Proofs/IslandWitness.lean`. With `--paranoid`, the five other checkers that ship with Lean accepted them too. CI does not use `--paranoid`, so that was a run by hand, and a later change needs a new one.

For those theorems, Comparator checks three things:

1. Each statement is the same term as in `Comparator/Challenge.lean`, a generated file that states them with no proofs.
2. Their proofs rest on no axiom other than `propext`, `Classical.choice` and `Quot.sound`.
3. The kernel accepts them, and everything they use, from an export of the sandboxed build.

Two limits apply:

- **The definitions are shared.** The challenge imports the same words, named parts and engine as the proofs. So a changed definition changes both sides, and Comparator shows no difference. A reader must still review the definitions. `scripts/statement_lock.sh` guards the words and named parts. It does not guard the engine, the Island, HexGrid or SHA-256.
- **It judges only those 22 theorems.** `Constitution/Examples.lean`, `Charter/EngineTests.lean` and other theorems that those 22 do not use are outside it. `make audit` covers the theorems in `Charter` modules.
