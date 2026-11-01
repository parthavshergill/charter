# Charter RL harness

A policy that plays Charter's moves and votes (never proposes laws), trained by self-play with PufferLib on Modal.
Every action goes through the Lean engine's `Engine.step`. There is no second model of the rules.

## Parts

| Path | What it is |
|---|---|
| `rl/lean/CharterRL/` | The environment in Lean: `Layout` (tables, action list), `Tables` (per-game facts, opponents, settings), `Actions` (decode, mask), `Obs`, `Env`, `Capi` (C exports), `Check` (tests) |
| `rl/env/build.sh` | Builds `rl/build/libcharter_rl.so`: the engine, the bots and the env over Lean's shared runtime |
| `rl/env/charter_rl.h`, `capi.c` | The C interface. `charter.py` is the Python binding (ctypes) |
| `rl/layout.json` | Where every observation column and action is. Printed by `charter-rl-check --layout` |
| `rl/puffer/charter.h`, `charter.ini` | The PufferLib env and its config |
| `rl/puffer/test_env.c` | Runs `charter.h` on the CPU without the trainer, checking the seat and mask rules |
| `rl/modal_app.py` | `test`, `train`, `eval` on Modal, each with a timeout cut to a dollar limit |
| `rl/eval/eval.py` | One command, one report |
| `rl/reference/policy.py` | Runs a PufferLib checkpoint in NumPy (MinGRU + linear decoder), for eval |

Pinned: Lean v4.35.0, PufferLib `ea7f989371270d2948f96728bda8aec5e7634a4c`.

## Commands

```bash
lake build charter-rl-check && .lake/build/bin/charter-rl-check --quick
rl/env/build.sh
python3 rl/eval/eval.py random hand --games 16
```

On Modal (only `MODAL_TOKEN_ID` and `MODAL_TOKEN_SECRET` needed; set `CHARTER_RL_NAME` to your name, so the app is
`charter-rl-<name>`; `CHARTER_RL_BUDGET` is your dollar budget for today):

```bash
cd rl && modal run modal_app.py --action test --quick --max-dollars 0.5
cd rl && modal run modal_app.py --action train --run <name>/try1 --minutes 20 --max-dollars 1.5 --train-args "--train.total_timesteps=50_000_000"
cd rl && modal run modal_app.py --action eval --run <name>/try1 --subjects "random,hand,<name>/try1/ckpt/.../<step>.bin" --games 200
```

`train` writes `/vol/<run>/train.log`, `ckpt/` and a meta JSON next to the first and last checkpoint, on the volume
`charter-rl`. Behind an HTTPS proxy, install `modal[api-proxy-support]` and set `SSL_CERT_FILE` to its CA bundle.

## The environment

- **Seats.** Four. Agent `i` plays game seat `seat_of[i]`, drawn afresh each game. Each tick, exactly one agent may
  act. The others see zeros and a mask with only the no-op (action 695). Bots inside the env (`hand`, `fair`,
  `closed`) play without ticks.
- **Actions.** 695 plus the no-op: end turn, vote no, vote yes, bank trades by resource row pair, declarations by
  resource row and level, a link piece on a link, a spot piece on a spot. Offers and deals have no action.
- **Observation.** 4434 floats of fixed tables (`rl/layout.json`): global, seats (this seat first, then turn order),
  resources, kinds, tiles, spots, links, laws, the open proposal. No names. Rows of resources and kinds are in a
  new random order each game (`slot_order = shuffled`; `game` keeps the game's order). With `move_rows = 1` (and a
  build with `-DCHARTER_MOVE_ROWS`) a table of up to 64 legal moves and what each changes is appended: 7122 floats.
- **Reward.** At the end: 1 for the winner, plus `reward_standing` (0.25) for first down to -0.25 for last.
  `shaping_points` adds a share per point gained; off by default.
- **Laws.** At the start of a turn, with chance 1 in `law_every` (8), the seat whose turn it is proposes a law from
  the game's library. Votes: `vote_mode = random` (a coin), `bot` (the hand bot's `lawOk`) or `policy` (votes are
  actions). Under `random` and `bot` the policy never sees a vote.
- **Bot ladder.** With `num_agents = 1`, bots fill the other seats: `bot_policy` 0 random legal, 1 `hand`, 2 `fair`,
  3 `closed`. `fair`, `closed` and `hand` play identically when nobody makes offers, and no seat here makes offers,
  so only 0 and 1 are worth running.
- **Maps.** `random_map = 1` shuffles resources and numbers between the tiles that pay, each game.

`[env]` keys in `charter.ini`: `games` (comma-separated ids), `vote_mode`, `slot_order`, `move_rows`, `law_every`,
`random_map`, `preview`, `reward_win`, `reward_standing`, `shaping_points`, `bot_policy`, `distinct_opps`.

Games: train on `island`, `not-catan`; hold out `slime-parliament`, `ai-bubble`, `strike-the-earth`,
`pirate-republic`.

## What is tested

`charter-rl-check` (all pass; see the PR for numbers):
- **mask:** for every one of the 695 actions at every decision of random games, the mask is 1 exactly when
  `Engine.step` accepts the action's event. Two kinds are counted apart, not as errors: declarations in games where no
  law reads one, and moves by the voting seat while a vote is due. Two seeded errors (end turn always offered; the
  last legal action dropped) are caught.
- **determinism:** the same seed and actions give the same observations, masks and rewards.
- **seed blind:** changing `State.seed` (the dice) changes no observation number. A seeded error that shows the next
  roll is caught.
- **renaming:** renaming every resource and piece and reversing their order in the game gives the same encoding when
  each name keeps its row. A seeded error (rows follow the game's list order) is caught.
- **maps:** random maps pass the full `G.checks`.

`rl/puffer/test_env.c`: exactly one agent may act per tick, waiting agents may only wait, games end, rewards sum to 1
per game in self-play.

## Eval

`rl/eval/eval.py SUBJECT...` plays fixed tables: opponents `hand` x3 and random x3; training and held-out games;
each game its own seed, the subject at seat k mod 4 in game k; phases `whole`, `setup` (subject places the opening
pieces, `hand` plays on) and `play` (`hand` places them, the subject plays on); with and without laws. It reports win
rates with 95% Wilson intervals, by seat, and points. Subjects: `random`, `hand`, or a policy file with a JSON meta
(see `rl/reference/policy.py`). A custom encoder adds its forward there.

## Known limits

- Speed, one thread: self-play with observations about 4.4k ticks/s (17k agent rows/s); one seat against three
  `hand` bots about 1.3k decisions/s. The vote preview is about half the cost of an observation (`preview = 0`
  doubles the speed). Per-move rows cost about 2.3x (6.1k to 2.7k decisions/s on Island).
- A linear decoder has one fixed output per action, so spot and link numbering on held-out maps differs from training.
- The pool holds only `hand`, whose strength relied on offers, which this env has no action for.
