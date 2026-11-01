# The bot arena

The arena plays many games between bots, fast, and reports who won. Use it to measure a bot. It does not serve
tables, and it does not change how a table plays.

Each event of each game goes through `Engine.step`, the same as at a real table. So a bot in the arena cannot
break a rule. A bot that wins in the arena won under the real rules of that pack.

| File | What it holds |
|---|---|
| `Server/BotCore.lean` | The bot's policy, its weights and the `Strategy` type |
| `Server/ArenaPlay.lean` | The loop that plays one game |
| `Server/Arena.lean` | The `charter-arena` program: input, threads, output and checks |
| `Server/ArenaReference.lean` | A slow copy of the policy, only for checking the fast one |
| `Evolved/Pool.lean` | The list of strategies the arena can seat |
| `Server/GenericCheck.lean`, `Evolved/Generic.lean` | A build check that no strategy names a pack |

## Play some games

```bash
lake build charter-arena
```

```bash
echo '{"game":"island","seats":4,"threads":4,"strategies":{"x":{"strategy":"hand","weights":{"pipValue":12}},"o":{"strategy":"hand"}},"games":[{"seed":1,"lineup":["x","o","o","o"]},{"seed":2,"lineup":["o","x","o","o"]}]}' | .lake/build/bin/charter-arena
```

The input is one JSON object:

| Field | Meaning |
|---|---|
| `game` | A pack's id, such as `island` or `pirate-republic` |
| `seats` | The number of seats. The pack must support it |
| `threads` | Optional. The default is 1 |
| `strategies` | Named players. Each has a `strategy`, default `hand`, and `weights`, whole numbers only |
| `games` | Each game has a `seed` and a `lineup`, with one player's name per seat |

The output has one JSON line per game, in input order, and then one summary line. A game's line has these fields:

| Field | Meaning |
|---|---|
| `winner` | The winning seat, or null |
| `lineup`, `seed` | The input of this game |
| `points` | Points by seat |
| `round` | The round when the game ended |
| `events` | The number of events the engine accepted |
| `offersMade`, `offersAccepted` | Offers by seat, and how many of them another seat accepted |
| `rejected` | How many turns ended because the engine accepted none of a seat's events |
| `status` | `finished` when the game ended |

The same input gives the same output, whatever the number of threads. Bad input stops the program before any game
runs: exit 1 with a reason for bad JSON, an unknown game or an unknown strategy, and exit 2 for an unknown flag.

`--params` lists the weights with their defaults and ranges. `--strategies` lists the strategies you can seat.

## Measure a bot fairly

**Rotate the seats equally.** On a pack's fixed map, all hand bots open the same way in every game. So the seat
decides much of the game:

| Hand bots, 4,000 games, wins by seat | Seat 0 | Seat 1 | Seat 2 | Seat 3 |
|---|---:|---:|---:|---:|
| Island, same openings | 7% | 13% | 58% | 21% |
| Island, `setupJitter` 30 | 25% | 23% | 27% | 25% |
| Slime Parliament, same openings | 3% | 10% | 73% | 14% |
| Slime Parliament, `setupJitter` 30 | 15% | 21% | 29% | 34% |

**Vary the openings too.** The `setupJitter` weight adds noise to the value of each spot during setup. The game's
seed and the spot fix the noise, so a game can be replayed. Without it, a bot can win by learning one fixed opening
that fails when the other seats open differently. The default is 0, so a real table's hand bot opens as it always did.
Slime Parliament keeps a seat effect even with jitter, so rotation is still required. So does Pirate Republic, now
that hand bots declare: with 4 hand bots, seat 1 wins 93% of games. A tie leaves the hat where it is, and every seat
holds 1 ballot after each round's end, so the captain keeps the hat by declaring 1 ballot too. Seat 0 takes the hat
first. In the next round seat 0 does not declare ballots, because it predicts that no later seat will, and seat 1
takes the hat. From then on seat 1 keeps it by tying.

**Measure against more than one opponent.** The default hand bot accepts any even swap, even of a good it does
not need. One change, `{"offerLimit": 2}`, wins 85% on Island and 96% on Not Catan against three default hand bots. So
also test against opponents that refuse all offers, such as `{"acceptMargin": 10}`. The default hand bot makes no
offers. So opponents that refuse offers change nothing unless the measured bot makes offers.

**Know what the opponents do not do.** Hand bots never propose a law. They declare only where a law in force
reads declarations at a round's end, and only the numbers 0, 1 and what they hold. A strategy that does what they do
not can win a contest that nobody else enters. Before you believe a very high win rate, turn off one part
of the strategy at a time and measure again.

## Add a strategy

A strategy is a function from a seat and a state to the events that seat wants, best first. The engine tries the
events in order, and the first one it accepts happens.

1. Write `Evolved/S17.lean`. It imports only `Server.BotCore`:

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

2. Add it to `Evolved/Pool.lean`: `import Evolved.S17`, and `Evolved.S17.strategy` in the list.
3. Run `lake build charter-arena`. Seat it with `"strategy": "s17"`. The build fails if the strategy names a pack,
   or holds a string that is not on the approved list. See below.

A strategy's own constants need no new field. Read one with `ctx.weights.extraOr "myWeight" 7`, where 7 is the
default, and set it in `weights`. The file `Server/BotCore.lean` has the parts of the hand bot you can reuse, such as
`turnMove`, `reactions`, `spotValue` and `bestBy`.

A seat speaks only for itself. The arena drops an event that a strategy asks for on behalf of another seat, and the
timer's event. So a strategy cannot vote for a rival or end a rival's turn.

The arena has no time limit. A strategy that compiles can still be very slow, so run a batch under a process
timeout. `Engine.legalMoves` works, but it costs about 90 calls of `Engine.step` per decision.

## The bot names no pack

The hand bot reads everything from the state and the rules, so it plays any pack. `Server/BotCore.lean` imports
no pack, and a build check enforces part of the rule. `#check_generic s` walks every constant that `s` reaches,
through the types and bodies of definitions. It fails if the walk reaches a constant under `Charter.Games`,
`gameSpecs`, `specOf?` or `GameSpec`. It also fails on a string in the bot's own code, in `Server/BotCore.lean`,
`Server/GameFacts.lean` or `Evolved/`, that is not on `approvedStrings` in `Server/GenericCheck.lean`. That list
holds the weights' names and the keys of the log's JSON. A strategy with weights of its own adds their names there.

`Evolved/Generic.lean` runs the check on the hand bot, its weights and every strategy in the pool, and
`lake build charter-arena` builds that file. It also shows the check failing on three bad strategies: one that
names a good, one that uses a pack's definition, and one that reads the list of packs.

The check has limits:

- It catches names and direct references to packs. It does not catch a rule tuned to one pack's shape, such as
  `if G.targetPoints == 18`. `#bot_numbers s` lists the numbers in the bot's own code, to review by eye.
- It is a check at build time, not a proof. No theorem of the game depends on it, and it is not part of their
  trusted surface.

## Why it is fast

Two changes give most of the speed, and neither changes what a rule sees:

- **The books.** `State.books` is a function that gains a layer per entry, so a lookup walks every entry so far.
  The arena replaces it with an equal table. It also empties `State.journal` after each step, because the engine only
  appends to it.
- **The policy.** The bot tests only the moves it is about to consider. It no longer asks for every legal move.

Hand bots, 4 seats, on a Mac with 14 cores, shared with other work:

| Pack | Events per game | Games per second, 1 thread | Games per second, 6 threads |
|---|---:|---:|---:|
| Island | 178 | 369 | 2,007 |
| Not Catan | 213 | 227 | 1,245 |
| Slime Parliament | 139 | 490 | 2,723 |
| AI Bubble | 226 | 202 | 1,152 |
| Pirate Republic | 100 | 466 | 2,595 |
| Strike the Earth | 207 | 245 | 1,355 |

This table is from before the hand bot declared. Declaring costs time only where a law reads declarations at a
round's end. There, each time the bot might declare, it predicts the round's end once for each number it tries. On a
Linux machine with 4 cores, 4 hand bots on Pirate Republic play 50 games per second per thread, against 199 before.
On the other packs the change in speed was smaller than the noise between runs.

## How we know the fast bot is the same bot

`make arena-check` runs in CI and makes two checks:

- `--check-fixture scripts/fixtures/bot-game.jsonl` plays a recorded bot game, and requires the same events.
- `--check-reference 2` plays each pack with plain bots, offers, laws and deals. At each step, it requires that the
  fast policy chooses what `Server/ArenaReference.lean` chooses. That file uses no shortcuts. It asks for every
  legal move, and it tries declarations on every resource. One of the check's laws makes a good worth a point and
  pays seats that declare, so the rules for both run on every pack.

These are checks on games that were played, not proofs. The rules themselves stay safe either way, because every event
goes through `Engine.step`.
