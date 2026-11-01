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
| `rl/RUN_A_POLICY.md` | How a checkpoint chooses one action: observation, mask, forward pass (flat, and entity with pointer), decoding, and the recurrent state between decisions |
| `rl/imitation/` | `collect.py` (the hand bot's decisions, with ticks and final returns), `bc.py` (behaviour cloning; `--sequences` replays whole games with waiting ticks, `--vf-coef` trains the value) |

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

## PufferLib patches

`rl/puffer/patches/` is applied to every build (`--no-patch` turns it off):
- `0001-learner-rows-only` (10 lines): minibatches walked all `total_agents` rows, so PPO also trained on frozen
  seats' rows (other policies' actions). With one buffer, this keeps the rows before `policy_layout[1]`. Real by
  reading the code. An A/B at 20M steps (Island and Not Catan, 8 min each) showed no measurable difference: against
  three `hand`, 2.2% (1.2 to 4.2) with it, 1.2% (0.5 to 2.9) without, on training games.
- `0002-warm-start` (8 lines): `--base.warm_start_path=FILE` loads weights into the trainable policy first.
  `rl/imitation/bc.py` writes such a file.

## A custom encoder

Put it in `rl/arch/<name>/` (or `rl/<name>/`) with:
- `puffer_build.sh`: run as `bash puffer_build.sh PUFFER_DIR OCEAN_DIR LAYOUT_JSON`. It copies its `.cu` and headers
  into `OCEAN_DIR` (PufferLib's `ocean/charter/`) and prints the extra nvcc flags on its last line of output.
- `patches/*.patch`, optional: applied after `rl/puffer/patches/`, and only when this encoder is built (the
  `src/ocean.cu` hook goes here, not in `rl/puffer/patches/`, which every build applies).
- `policy.py` with `load_policy(path, meta)`, returning an object with `.player(seed)`, for eval.
  `rl/reference/policy.py` has `mingru_step` and `Player` to reuse.

Then `modal run modal_app.py --action train --encoder <name> [--meta-extra '{"entity_dim": 32}']`. Checkpoint metas
say `"format": "puffer-<name>"`, and eval loads them through your `policy.py`.

`rl/reference/encoders.py` is one example design per encoder kind (max pool for `entity`, for instance). It does not
fix the design. The protocol's rule is met by your own PyTorch version of your encoder, checked the same way: forward
and every weight gradient on the same weights and inputs, with a seeded error caught. `reference_test.py --check`
works for any encoder that has an entry in `ENCODERS`.

## The environment

**Layout version 2.** Every game that passes `G.Valid` fits, at any seat count from 2 to 6: the layout's limits are
the engine's own (`Charter/Words/Game.lean`: 6 seats, 16 resources, 16 kinds of piece counting those laws add, 100
spots, 48 laws in force). Links and tiles have no limit in the engine, so they have no table: what a spot's links and
tiles hold is in the spot's row, and a placement is chosen by its row in `places`. Version 1 (observation 4434, 696
actions, at most 8 resources, 60 spots, 84 links, 24 tiles, 16 laws) refused larger games; its last commit is
`e466f9f`.

- **Seats.** `seats` in `[env]` gives the seat counts, for example `2-6` (the default) or `4`; each game draws one
  that the game allows (Not Catan takes 3 or 4). `num_agents` must be the most of them (6 for `2-6`), and `[vec] total_agents` a multiple of `num_agents`
  (1536 by default: 256 envs. The GPU holds every agent's observation for the whole horizon, 1536 x 64 x 11465
  floats is 4.5 GB; 3072 agents did not fit on a T4). Agent `i`
  plays game seat `seat_of[i]`, drawn afresh each game; agents past the seat count sit the game out. Each tick,
  exactly one agent may act. The others see zeros and a mask with only the no-op (action 515), written once when they
  start waiting. Bots inside the env (`hand`, `fair`, `closed`, `champion`) play without ticks.
- **Actions.** 515 plus the no-op: end turn (0), vote no (1), vote yes (2), bank trades by resource row pair (3 to
  258), declarations by resource row and level (259 to 386), and a placement by its row of `places` (387 to 514).
  Offers and deals have no action.
- **Placements.** Every legal placement of the decision, asked of the engine, in a fixed order: replacing a piece,
  then attaching, then a new piece on a spot, then a piece on a link; within each, by the spot's pips (a link: its
  better free end), most first; then by spot and kind row. Row `i` of `places` describes action `387 + i`: its kind
  (one-hot over kind rows), placement, spot numbers (`at`, `at_b` for a link's other end, on the scale of 100, so a
  row can be matched with its `spots` row, which has the pips by resource), the spot's pips, goods, demand, reach,
  points and yield gained, cost and shortfall. The order does not use names, so it is the same under renaming. At most 128 rows: past
  that, `place_overflow` is 1 and the rest have no action. No game here comes near it (the most seen is 100, in
  setup on a 100-spot map). A turn always has end turn, and a setup turn always has a row, so a seat is never left
  without an action.
- **Observation.** 11465 floats of fixed tables (`rl/layout.json`): global, seats (this seat first, then turn
  order, 6 rows), resources (16), kinds (16), spots (100: map, pieces, and the links and tiles at each spot), laws
  (48), the open proposal, and places (128 x 35). No names. Rows of resources and kinds are in a new random order
  each game (`slot_order = shuffled`; `game` keeps the game's order). With `move_rows = 1` (and a build with
  `-DCHARTER_MOVE_ROWS`) a table of up to 64 legal moves and what each changes is appended: 15177 floats.
- **Cost of the change.** The observation is 2.6 times as long, and `places` is 39% of it, so a flat encoder at hidden
  128 has about 1.5M weights in its first layer (v1: 0.57M), and env time per observation went up (see Known limits).
  A linear decoder still gives each action one fixed output: row `i` of `places` means "the i-th placement in this
  order", which is more stable across maps than v1's "this spot number", but choosing well among rows needs an
  encoder that scores each row from its own features (a pointer over rows), which is the encoder agents' choice.
- **Reward.** At the end: 1 for the winner, plus `reward_standing` (0.25) for first down to -0.25 for last.
  `shaping_points` adds a share per point gained; off by default.
- **Laws.** At the start of a turn, with chance 1 in `law_every` (8), the seat whose turn it is proposes a law from
  the game's library. Votes: `vote_mode = random` (a coin), `bot` (the hand bot's `lawOk`) or `policy` (votes are
  actions). Under `random` and `bot` the policy never sees a vote.
- **Bot ladder.** With `num_agents = 1`, bots fill the other seats: `bot_policy` 0 random legal, 1 `hand`, 2 `fair`,
  3 `closed`, 4 `champion`, 5 `champion-closed`. `fair`, `closed` and `hand` play identically when nobody makes
  offers, and `hand` makes none, so of those only 0 and 1 are worth running. `eval_bots = 0,1,4`.
- **Champion.** The best strategy of the earlier evolution run (`g10w44`), with its weights:
  `rl/opponents/night2_champion.lean` and `.json`. `rl/opponents/gen_champion.py` copies it into
  `rl/lean/CharterRL/Champion.lean` (do not edit that file; `--check` says if it is stale). It is in the training
  library only, which the server does not import. `champion` makes offers and accepts them among bot seats (the
  policy has no action for offers); `champion-closed` makes and accepts none. It costs about 9 times as much time per
  decision as `hand`.
- **Training against bots.** `bot_share = p`: in self-play, each game has chance `p` that agents other than 0 sit out and
  `bot_policy` bots take their seats, so agent 0 also plays against, say, `champion` (`bot_policy = 4`). The agents
  that sit out see only waiting rows, with no reward.
- **Maps.** `random_map = 1` shuffles resources and numbers between the tiles that pay, each game.

`[env]` keys in `charter.ini`: `games` (comma-separated ids), `seats`, `vote_mode`, `slot_order`, `move_rows`, `law_every`,
`random_map`, `preview`, `reward_win`, `reward_standing`, `shaping_points`, `bot_policy`, `bot_share`,
`distinct_opps`, `declare_always`, `stale_wait`, `shaping_relative`, `shaping_gamma`. The Lean configuration also takes `record` (keep the game's events for a saved log;
eval only).

- **Waiting rows** (`stale_wait`, off by default). By default a waiting agent's observation is all zeros. PufferLib
  still runs it through the network on every tick, so its recurrent state moves on those ticks, and with zero input
  MinGRU pulls the state halfway to 0.5 each time; the critic also sees one constant on every waiting row. With
  `stale_wait = 1`, an agent that has decided in this game keeps its last observation while it waits (only the mask
  changes). Agents that sit the game out, and agents before their first decision, see zeros.
- **Shaping** (`shaping_relative = c`, off by default): potential-based. A seat's potential is c times its points
  less the mean of the others' points, over the target, and is 0 once the game is over. Each tick pays each seat
  `shaping_gamma * Φ(after) - Φ(before)`. With `shaping_gamma` equal to `[train] gamma` it keeps the best play the
  same (Ng, Harada and Russell 1999); `charter-rl-check` confirms that with gamma 1 each seat's shaped returns over a
  game equal the unshaped ones. `shaping_points` (absolute, not potential-based) is still there. Eval always judges
  real wins; the report prints a policy's training settings.
- **Eval and the server run the recurrent state as training did.** `Player.wait` runs one forward pass on the
  waiting observation (zeros, or the last one under `stale_wait`) for every decision of another caller seat;
  `rl/eval` does it by default (`--wait-steps 0` turns it off). `rl/RUN_A_POLICY.md` says what a server must do.
- **Setup:** the mask does not offer end turn in a setup turn while a placement is legal (the engine allows it, and
  policies gave up free opening pieces that way).

`declare_always = 1` offers declarations in every game. Island and Not Catan have no law that reads one, so by
default declarations are never legal there, their outputs are never trained, and on held-out games that do read them
(AI Bubble, Pirate Republic) policies have been seen to repeat one 125 to 199 times a game. With the switch on, the
engine accepts them in training games too (they change nothing there and use one of the turn's 20 actions), so
training sees what they do. Eval keeps the default unless the policy's meta says otherwise.

Games: train on `island`, `not-catan`; hold out `slime-parliament`, `ai-bubble`, `strike-the-earth`,
`pirate-republic`. Made-up games (`rl/lean/CharterRL/Gen.lean`) have ids `gen-limits-N`, `gen-tiny-N` and
`gen-odd-N`: at the engine's limits, tiny, and odd sizes in between, each kept only if it passes `G.checks`. They are
for "can it play", never for training or choosing settings.

## What is tested

`charter-rl-check` (all pass; see the PR for numbers):
- **mask:** for every one of the 515 actions at every decision of random games, the mask is 1 exactly when
  `Engine.step` accepts the action's event. Also every kind on every spot and every link is tried, and each placement
  the engine accepts must have a row of `places` (or be counted past the last row). Two kinds are counted apart, not
  as errors: declarations in games where no law reads one, and moves by the voting seat while a vote is due. Three
  seeded errors (end turn always offered; the last legal action dropped; the last legal placement given no row) are
  caught. Held-out games are checked at every seat count they allow.
- **can it play:** every game, and made-up games at the engine's limits (16 resources, 16 kinds, 100 spots, about
  385 links, 60 tiles, 40 founding laws) and at tiny and odd sizes, at every seat count from 2 to 6, played to the
  end with random legal actions: no decision without an action, no refused action, no game stuck before its end, and
  the mask checked against the engine at the first decisions of each.
- **determinism:** the same seed and actions give the same observations, masks and rewards.
- **seed blind:** changing `State.seed` (the dice) changes no observation number. A seeded error that shows the next
  roll is caught.
- **renaming:** renaming every resource and piece and reversing their order in the game gives the same encoding when
  each name keeps its row. A seeded error (rows follow the game's list order) is caught.
- **maps:** random maps pass the full `G.checks`.

`rl/puffer/test_env.c`: exactly one agent may act per tick, waiting agents may only wait, games end, rewards sum to 1
per game in self-play, at 4 seats and at 2 to 6, on made-up games too.

## Eval

`rl/eval/eval.py SUBJECT...` plays fixed tables: opponents `hand` x3, random x3 and `champion` x3 (`--opponents`
picks others, such as `champion-closed`); training and held-out games;
each game its own seed, the subject at seat k mod 4 in game k; phases `whole`, `setup` (subject places the opening
pieces, `hand` plays on) and `play` (`hand` places them, the subject plays on); with and without laws. It reports win
rates with 95% Wilson intervals, by seat, and points. Subjects: `random`, `hand`, `champion`, `champion-closed`, or a
policy file with a JSON meta (see `rl/reference/policy.py`). A custom encoder adds its forward there.

**Hollow wins.** Every table also gives *target wins %* (with its interval): games the subject won by reaching the
game's target points. Wins at the round limit go to the leader on points, often with a low score. It also gives the
split of the subject's wins (at the target, at the round limit, other: a law ended the game), the share of games that
ended at the limit, and the mean points of the subject and of the best other seat. The trainer's log has
`target_win` too. The reward is unchanged.

**Can it play** (`--can-play 1`, the default): a separate check from how well it plays. The subject plays the
made-up games (2 at the engine's limits, 3 tiny, 8 odd) at every seat count from 2 to 6, at every seat, against
random players, and the report gives games that did not end, refused actions and errors, with PASS or FAIL. Eval
tables stay at 4 seats, so results compare across runs.

**Saved games, to read.** `--logs K` (default 2) keeps the first K games of every table in `OUT/games/<subject>/`:
- `<code>.jsonl`: the server's event log of the game: the table's creation (with the dice's seed and the dealt map),
  a join per seat, the start, and every event. `charter-rl-logs DIR` replays each through the server's `Game.create`
  and `Game.apply`, and writes `<code>.db`. Then `make spectate RESULTS=OUT/games/<subject>` shows them; the subject's
  seat is named `subject ...`. Eval runs `charter-rl-logs` itself when it is built (on Modal it is).
- `<code>.md`: a short summary: moves by type for each seat, points at the end of each round, what each seat built
  and when, trades and offers, and laws proposed with each seat's vote.
- `OUT/games/index.md`: one row per saved game, with the winner, points and a link to its summary.

A dealt map reaches the server through an optional `_map` field of the creation event (`GameSpec.dealt` in
`Server/Spec.lean`): the same game with its paying tiles' resources and numbers in the logged order. It must pass
`G.Valid`, like every game. No other log has the field, so live tables do not change.

## Known limits

- Speed, one thread (this harness's own measure, `prof.c`-style: self-play, `vote_mode = bot`, observation and mask
  at every decision): Island about 6.0K decisions/s, Not Catan 4.0K, Island at 6 seats 4.9K. Before round 2's speed
  work, on the same machine and layout: 4.1K, 3.4K and 3.0K. What changed: the hand bot's vote check (`lawOk`) is
  worked out once per law for all seats (it was 41% of the time), a law's preview once per law for all voters, table
  widths are kept, and `freeMap`/`reachMap` once per decision. Waiting agents' zero rows are written once.
- `champion` is about 5 times faster than as written (Island, one seat against three: 128 to 650 decisions/s;
  `champion-closed` about 300 to 1,120), and still about 3 times slower than `hand`.
- Trainer speed on Modal (T4, 8 CPUs, flat 128, one MinGRU layer, layout 2, 1536 agents, 6 per env, seats 2 to 6):
  about 53K SPS, with the env 33% of each epoch and copying observations to the GPU 35%. SPS counts agent rows, and
  5 of 6 rows per tick are waiting rows, so that is about 9K decisions/s. Layout 1 (2048 agents, 4 per env): about
  56K SPS, env 67%, so about 14K decisions/s. Training at 4 seats (`--env.seats=4 --env.num_agents=4`) has fewer
  waiting rows.
- A linear decoder has one fixed output per action. Under layout 2 a placement's action is its row in a fixed order,
  not a spot number; scoring rows by their features needs a pointer-style decoder, which PufferLib's linear decoder is
  not.
- The policy has no action for offers, and `champion` gets much of its strength from offers (see the PR).
- `hand` is weak on some held-out games: random players beat three `hand` bots in 69% of Pirate Republic games and
  matched them on Strike the Earth (200 games each). Read held-out results by game; the report has a table for it.
