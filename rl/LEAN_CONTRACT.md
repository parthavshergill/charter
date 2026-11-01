# Lean contract for the evolve loop

Owner: the Lean agent. Status: final. The interface is firm, and every number here was measured.

## Modules

- The module a strategy imports: `Server.BotCore`. It is the ONLY import allowed in `Evolved/S<id>.lean`.
  So the static check's rule is: refuse any `import` line other than `import Server.BotCore`.
- Pool file: `Evolved/Pool.lean`. Exe: `charter-arena`, root `Server.Arena`. Build: `lake build charter-arena`.
- Binary: `.lake/build/bin/charter-arena`. `strip` it on Linux after the build if you upload it.

## A strategy module (compiled and run in a scratch copy, exactly as here)

`Evolved/S17.lean`:

```lean
import Server.BotCore

namespace Evolved.S17
open Charter CharterServer CharterServer.Bots

/-- Plays like the hand bot, but ignores offers. -/
def strategy : Strategy :=
  Strategy.ofSeat "s17" fun ctx s seat =>
    turnEvents ctx s seat

end Evolved.S17
```

`Evolved/Pool.lean`, which the loop regenerates:

```lean
import Server.BotCore
import Evolved.S17

namespace Evolved
open CharterServer

/-- The strategies the arena can seat. -/
def pool : List Bots.Strategy := [Bots.hand, Evolved.S17.strategy]

end Evolved
```

The `name` given to `Strategy.ofSeat` is what `"strategy"` in the arena's JSON refers to. Names must be unique in
the pool. The module name, namespace and strategy name need not match, but keep them the same.

## The API a strategy can use (all in `Server/BotCore.lean`, namespace `CharterServer.Bots`)

Give Opus the source of `Server/BotCore.lean` itself; it is short and has a docstring per definition.

- `Strategy.ofSeat name f`, with `f : {G : GameDef} → Ctx G → State G → Nat → List Event`. It gives one seat's
  events, best first. The engine tries them in order and the first it accepts happens.
- `Ctx G`: `ctx.weights : Weights`, `ctx.board : Board G`, `ctx.offersThisTurn : Nat`.
- `Weights`: named `Int` fields, listed by `--params`. A strategy's own constants: `ctx.weights.extraOr "name" 7`,
  where 7 is the default. Unknown weight names in the arena's JSON land in `extra`.
- Parts of the hand bot to reuse: `turnMove ctx s seat : Move` (the bot's move), `turnEvents ctx s seat` (that move,
  then ending the turn, only on the seat's turn), `reactions ctx s [seat]` (votes, signatures, accepted offers),
  `actionMove`, `setupFrom`, `setupPlaces`, `placesOf ctx s seat test`, `isLegal s seat m`, `bestLegal`, `bestBy`,
  `spotValue ctx v`, `roadValue ctx free l`, `freeMap`, `reachMap`, `freeSites`, `hasFreeSite`, `tradeToward`,
  `offerToward`, `buildTargets`, `offerScore`, `incomeOf`, `bal s seat r`, `pips G n`.
- From the rules: `s.pointsOf`, `s.pieces`, `s.round`, `s.currentSeat`, `s.phase`, `s.offers`, `s.openProposals`,
  `s.rules`, `s.costOf k`, `s.turnOrder`, `Engine.step G s e`, `G.targetPoints`, `goodsOf G`, `spotPiece G`,
  `linkPiece G`, `upgradePiece G`.
- `ctx.board` holds tables worked out once per game, so prefer it and `freeMap` to walking `G.map.links`.
  `Engine.legalMoves G s p` works, but it costs about 90 `step` calls, so it makes a strategy much slower.

A seat is asked only when it is its turn, or when a proposal or an offer is open. A strategy that answers nothing
on its turn loses that turn: the arena ends it and counts `rejected`.

## Arena input and output: the design file's JSON, plus these details

- `winner`: seat number or null. If a whole game ends with no seat at the target, the rules still name a winner:
  the most points, the earliest seat on a tie.
- `offersMade[i]`: offers seat i made. `offersAccepted[i]`: how many of seat i's offers another seat accepted.
- `rejected`: how many times no candidate of a seat was accepted, so the arena ended the turn for it.
- `round`: the state's round when the game ended. `events`: events the engine accepted.
- `points`: by seat number.
- `summary.cpuMs`: the sum of the worker threads' busy time, not a kernel CPU figure.
- `threads` is optional, default 1. `strategy` is optional, default `hand`. `weights` values must be whole numbers;
  a float is an error. The arena does not clamp weights to their ranges: the loop must.
- Exit 1 and a line on stderr, before any game runs: unknown game or strategy, a lineup with an unknown key or the
  wrong length, a seat count the game does not support, bad JSON. Exit 2: unknown flag.
- Lines come in input order and are flushed every 64 lines, so a reader sees steady progress.
- Same input, same output, whatever `threads` is. A seed makes the same game as `charter-sim`'s table with that seed.

Flags: `--params`, `--strategies`, `--check-fixture PATH`, and `--check-reference [GAMES]`, which plays every game
checking the fast bot against the old one at every step.

Seats supported: island and belt 2 to 6, not-catan 3 to 4, slime-parliament 2 to 4.

The arena has no time limit of its own. A strategy that compiles can still be very slow, so run each batch under a
process timeout, and treat a timeout or a non-zero exit as that strategy's failure.

A seat speaks only for itself: the arena drops any event a strategy asks for on behalf of another seat, and the timer's
`forceEndTurn`. So a strategy cannot vote for a rival or end a rival's turn.

Two JSON fields exist only for measuring, and the loop has no need of them: `"plain": true` (no speed tricks in the game
loop) and `"compactEvery": N`. A hidden strategy `hand-reference` is the old bot, at about 90 `step` calls per decision.

## What to upload to build it

These 13 MB are enough. I built and ran them from nothing: `Charter`, `Charter.lean`, `Server`, `Evolved`, `packages`,
`forks`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`. Do not leave out `forks` or `packages`, because lake
needs them. The image needs the `gcc` and `libc6-dev` of the repo's `Dockerfile`, because `forks/leansqlite` builds a C
file even though the arena never uses it. The result is 131 MB of `.lake`. This was built on macOS, not on Linux.

## Findings that matter for the loop

1. **The hand bot's rule for accepting offers can be exploited, and a one-weight change finds it.** One seat with
   `{"offerLimit": 2}` against 3 hand bots, seats rotating, 8000 games on fresh seeds: it wins **83.6%** on island and
   **95.1%** on not-catan. On island it makes about 28 offers a game and about 20 are accepted, because a hand bot takes
   any offer that gives it as many goods as it pays, even a good it does not need. Expect the first generation to find
   this. The win over `3 x hand` then measures mostly this one hole, and later progress has to come from play against
   champions that have closed it. For comparison, `{"offerLimit": 1, "offerGive": 2}` gets 29.1% and 43.1%.
2. **The seat decides most of a game.** The map and the setup choices are fixed, and every hand bot sets up the same
   way, so each seat gets the same start every game. All-hand wins by seat, 8000 games on fresh seeds (fair is 25%):
   - island: 7.0%, 13.5%, 57.5%, 21.9%
   - not-catan: 13.5%, 26.8%, 57.4%, 2.3%
   - belt: 27.8%, 47.2%, 11.9%, 13.1%
   - slime-parliament: 2.8%, 9.5%, 73.7%, 13.9%

   So rotate seats exactly equally, as the design says. A win rate from one seat means little, and an unbalanced
   rotation would swamp a real effect.
3. **Rotation is fair.** Four named hand bots, seats rotating, 8000 games on fresh seeds: island 24.4%, 25.4%, 25.8%,
   24.4%; not-catan 24.7%, 25.6%, 25.3%, 24.4%; belt 24.3%, 24.7%, 25.8%, 25.3%; slime 25.4%, 24.1%, 25.5%, 25.0%.
   The standard error at this size is about 0.48%. On a shared seed, all-hand rotations are the same game, so each gets
   exactly 2000 of 8000. A seed reused across rotations gives paired games, not independent ones, and a Wilson bound
   assumes independent games.
4. **A game can end with a winner at 0 points.** If nobody builds, the rules name the earliest seat, and the status is
   still `finished`. Look at `rejected` to spot a strategy that throws away its turns.

## Measured numbers (this Mac: 10 performance and 4 efficiency cores, shared with other sessions)

Games per second on one thread, 4 seats of `hand`.

| Stage | island | not-catan |
|---|---:|---:|
| Before: old bot, plain loop (books grow, journal kept) | 2.1 | 0.7 |
| Old bot, books kept as a table, journal emptied | 21 | 14 |
| New bot, plain loop | 56 | 22 |
| New bot, journal emptied only | 54 | 22 |
| After: new bot, books kept as a table, journal emptied | 740 | 427 |

What mattered:
- `State.books` is a function that gains a layer per entry, so a lookup walks every entry so far. Replacing it with an
  equal table after each step gives 10x to 20x. Every event still goes through `Engine.step`, and the books answer the
  same.
- `Engine.legalMoves` is about 90 `step` calls per decision. The new policy tests only the moves it is about to consider.
  This gives about 30x.
- Leaving the look for a winner out of the legality test, and not working out the same map facts twice in a decision,
  gave about 40% (from 514 and 315).

Tried and not kept: `-mcpu=native` (the binary did not change) and thin LTO (760 games per second with and without).
Lake already compiles with `-O3 -DNDEBUG`. Emptying the journal gains nothing measurable alone. It stays because it costs
nothing and holds less memory.

Thread scaling on island, games per second in all (per thread). Other sessions' load changed between runs, so there are
two rows.

| Threads | 1 | 2 | 4 | 8 | 12 |
|---|---:|---:|---:|---:|---:|
| Load about 9 | 753 | | 2854 (714) | 5587 (698) | |
| Load about 20 | 738 | 1411 (705) | 2782 (695) | 4370 (546) | 5764 (480) |

Not-catan, load about 20: 411 at 1 thread; 1659 (415) at 4; 3051 (381) at 8; 3525 (294) at 12. At a load of about 30,
8 threads fell to 285 per thread on island and 251 on not-catan, so an idle-core figure needs an idle machine.
A measure less affected by load, CPU seconds from `time`: island 20000 games at 8 threads used 32.3 s of user CPU, which
is 620 games per CPU second, against 757 at 1 thread. So 8 threads keep about 82% of the speed of one. Some of that
loss may be the efficiency cores. Workers share no data in the hot path, on purpose (see `worker` in `Server/Arena.lean`).
I have no number for Modal's cores. Measure them.

With every seat at `offerLimit` 2 a game has more events: island 326 events a game, 276 to 392 games per second per thread
at 8 threads depending on load; not-catan 447 events a game, 130 at the higher load. Budget for this after generation 1.

Peak memory: 67.5 MB maximum resident at 8 threads for 20000 games on island, 67.8 MB on not-catan (macOS `time -l`). At 1
thread, 2000 games: 41 MB. Results wait in memory until printed, at about 200 bytes a game. This does not include any
Python process in the container, and it is a macOS figure.

Build:
- Clean full `lake build charter-arena`: 58 build steps (47 modules of this repo, the rest from packages), 28 s wall and
  57 CPU seconds (user + sys), load about 20. From the upload list above, at a higher load: 52 s wall, 70 CPU seconds.
- The whole project (`lake build`, default targets, with all proofs) took 157 steps: 116 s wall and 176 CPU seconds. So the
  arena needs 37% of the steps and 24% of the wall time.
- The `valid` theorems are cheap: Island 3.3 s, NotCatan 2.5 s, SlimeParliament 2.3 s, Belt 2.2 s, each counting its whole
  module. The slowest module the arena needs is `HexGrid.Theorems`, at 7.8 s.
- After changing only one `Evolved/S<id>.lean`: 3.1 to 3.7 s with a pool of 4. It rebuilds that module, `Evolved.Pool` and
  `Server.Arena`, and links. A comment-only change took 2.5 s.
- Binary: 102.7 MB, and 82.4 MB after `strip -x` on macOS. It starts in about 20 ms once the file is cached, and took
  about a second the first time.
