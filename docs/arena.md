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
Slime Parliament keeps a seat effect even with jitter, so rotation is still required.

**Measure against more than one opponent.** The default hand bot accepts any even swap, even of a good it does
not need. One change, `{"offerLimit": 2}`, wins 85% on Island and 96% on Not Catan against three default hand bots. So
also test against opponents that refuse all offers, such as `{"acceptMargin": 10}`.

**Know what the opponents do not do.** Hand bots never declare, and they never propose a law. A strategy that does
these things can win a contest that nobody else enters. Before you believe a very high win rate, turn off one part
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
3. Run `lake build charter-arena`. Seat it with `"strategy": "s17"`.

A strategy's own constants need no new field. Read one with `ctx.weights.extraOr "myWeight" 7`, where 7 is the
default, and set it in `weights`. The file `Server/BotCore.lean` has the parts of the hand bot you can reuse, such as
`turnMove`, `reactions`, `spotValue` and `bestBy`.

A seat speaks only for itself. The arena drops an event that a strategy asks for on behalf of another seat, and the
timer's event. So a strategy cannot vote for a rival or end a rival's turn.

The arena has no time limit. A strategy that compiles can still be very slow, so run a batch under a process
timeout. `Engine.legalMoves` works, but it costs about 90 calls of `Engine.step` per decision.

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

## How we know the fast bot is the same bot

`make arena-check` runs in CI and makes two checks:

- `--check-fixture scripts/fixtures/bot-game.jsonl` plays a recorded bot game, and requires the same events.
- `--check-reference 2` plays each pack with plain bots, offers, laws and deals. At each step, it requires that the
  fast policy chooses what `Server/ArenaReference.lean` chooses. That file uses no shortcuts, and it asks for every
  legal move.

These are checks on games that were played, not proofs. The rules themselves stay safe either way, because every event
goes through `Engine.step`.
