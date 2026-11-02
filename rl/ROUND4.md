# Round 4: make the policy the bot in the game

The owner's goal: the trained policy replaces the hand-written bot in the game. `rl/CLOUD_PROTOCOL.md` and the rules in `rl/ROUND2.md` and `rl/ROUND3.md` still apply. Read the last `RESULT` on PR #18, the last `RESULT` on PR #31, and the last `ADVICE` on PR #11.

## The bar

A policy is ready when all of these hold through the server path (450 games or more, 50 per world), measured on `main`'s nine worlds:

1. **Strength.** It wins 25% or more against 3 table bots, counting only wins that a table bot could have contested.
2. **Every world.** It wins 10% or more on each world, and it is not passive on any of them: a reader of its games sees it build and trade.
3. **Honest play.** No declaration loops, no reward hacking, and limit wins are under half of all its wins.
4. **Speed.** 50 ms or less per decision on CPU, on the server.
5. **Any game.** It plays every game that passes `G.Valid`, at 2 to 6 seats, with no fallback bot.

The owner decides when to switch the default. This bar says when to ask.

## Where it stands

CANDIDATE 9 wins 22.2% on the server. With the decision-time blend at c = 100 it wins 30.3% on the six worlds where declarations play no part. The table bot never declares, so the blend's wins on Omerta and The Pit do not count. A fix to the table bot is in progress in a separate session.

| Name | Job | Modal limit, this round |
|---|---|---|
| server path (PR #31) | Put the blend in the server, and measure | $5 |
| `entity4` (PR #18) | Train for The Pit and the weak worlds | $30 |
| `speed` (PR #11) | Take the new table bot into the harness when it lands | $5 |

## Server path

Add `logit + c·(V(s′) − V(s))` over the policy's top candidates to the Lean policy path, with `c` and the candidate count in the weights file's settings. Check it against `choose_mix` in `rl/entity/entity_numpy.py` on recorded decisions. Report time per decision. Measure CANDIDATE 9 with the blend at c = 30 and c = 100, in the usual 450 games.

## `entity4`

The Pit is the world furthest from the bar, and wider worlds, chain worlds and lookahead at decision time did not fix it. Find out why, then fix it. Try these in order, and stop each by its own rule:

1. **Learn from the improved move.** Train the policy toward lookahead-improved targets (Gumbel-style policy improvement, or a sampled best response), so the policy itself learns what the blend finds. Item 3 in `ADVICE (round 2)` on PR #11 describes it. Stop if the server-like nine-world score, with the blend off, does not gain 2 points over CANDIDATE 9 at 50M.
2. **Keep the table bot's skills.** On decisions where the policy passes up a build or trade the table bot would make, add an imitation loss at a small weight, or run DAgger against `table` on chain and fast pack worlds. The table's move ranks about 46th on The Pit. Stop if The Pit stays under 5% with no lone auction wins.
3. **Two-step value.** A bank trade earns nothing in one step, so one-step lookahead cannot price it. Try a candidate that scores a trade together with the best build it allows. Stop if The Pit does not rise.

Choose by the server-like row (`--random-map 0 --laws off`), at 800 games per world. Do not count a win from a declaration that no opponent contests. When the new table bot lands, re-measure CANDIDATE 9 first, and do not compare numbers across that change.

## Wild worlds

The owner wants far wilder games in training, so the policy learns to read rules and does not memorise worlds. The evidence so far: 512 pack worlds in three styles. The fast style moved AI Bubble from 6% to 21%, and Procgen needed about 10,000 levels to close its gap. Plain wider worlds did not help before per-move rows.

`speed` builds `pack-wild`:

1. **Far more worlds.** Tens of thousands of seeds, with a new world each game, and a separate `pack-wild-val`.
2. **Wilder economies.** Random build trees of any shape the engine allows, including long upgrade chains, goods that convert into each other, odd costs, yields and point values. Few or many goods. Rich and starved boards. Very short and very long games. Odd bank rates and dice.
3. **Wilder laws.** Dense founding laws from the whole rule language: taxes, dividends, auctions, declarations that pay, round-end transfers, piece moves on a roll, cost changes, worth changes, conditional rewards, repeals.
4. **Rules that change during the game.** Laws pass and lapse in the middle of training games, because that is what Charter is. This matters most: the policy must cope when the world changes under it.
5. **Perturbed Island and Not Catan.** Mutate only these two training worlds: costs, points, targets and laws. Do not build from the text, numbers or structure of any held-out shipped world.

Agents may write law ideas in English and have them drafted into the rule language, as the owner's plan always allowed. Every world must pass `G.checks`.

**Keep the worlds honest.** A wild world is no use if it is decided by luck or by doing nothing. Reject a world where a passive seat wins more than its share, where a random seat matches `table`, or where the game is decided in setup. Report the rejection rate, and a coverage check by style. Every observation column should vary.

**`entity4`** runs this beside item 1, from CANDIDATE 9's run: the same recipe on `island,not-catan,pack-wild`, with the switches on. Judge at 30M and 60M on the server-like row, with `pack-wild-val` beside it. Stop if held-out without Pirate Republic has not gained 2 points by 60M. Then try replaying worlds by value loss (PLR). Read games on wild worlds as well, because new worlds can bring new ways to hack: stalls, no-op loops and worlds won by a single trick.

## `speed`

When the table bot PR merges to `main`, vendor the new bot, signal `HARNESS-READY`, and give the old and new table's win shares by world.

## Reporting

As in round 3: `PROGRESS` and `CANDIDATE` on PR #18, `RESULT` on PR #31, with a `REVIEW` of real games that reads every line. Nothing merges and the default does not change until the owner says so.
