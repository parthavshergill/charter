# The trained bot

`CHARTER_BOT=policy make run` makes every bot seat ("Add a bot") play by a trained network. Without that
setting, bot seats play the rule-based bot of `Server/BotCore.lean`, as before. The default does not change.

## Files

- `Layout.lean`, `Obs.lean`: what the network reads, and its actions. A copy of the training harness's
  `rl/lean/CharterRL/` (branch `rl-harness` at `89a3a51`, layout version 2, the layout of `entity2`'s candidates),
  cut to what one decision needs.
- `Net.lean`: the network in plain Lean (entity encoder, MinGRU, linear decoder, pointer decoder over the rows of
  `places` and over bank trades), and the reader of the weights file. No GPU, no Python, no new library.
- `Bot.lean`: one decision, the seat's memory, and the switch `CHARTER_BOT`.
- `Server/Player.lean`: `trained` is one more player beside `human` and `bot`. It gets a `Situation` and answers
  with events; the engine has the final word, as for the others.
- `PlayCheck.lean`: `charter-policy-check`, whole games through `Game.create` and `Game.apply`.
- `DiffMain.lean`: `charter-policy-diff`, the Lean network against the NumPy one.
- `policy.chpw`: the weights. **Not in this PR yet.** Swap a checkpoint in as this one file.

## Swapping in a checkpoint

```
python3 scripts/policy_weights.py CKPT.bin --out Server/Policy/policy.chpw --gru-state carry
```

`CKPT.bin.json` must sit beside the checkpoint. The file is a header (sizes, action offsets and the state
rule) and then the checkpoint's floats, unchanged. The server refuses a file whose layout or sizes do not match,
and says why. `--gru-state` is needed when the meta has no `gru_state`; see below.

## How it decides

- On its turn: the legal action with the highest score. Every legal action is asked of the engine first. No
  sampling: the same state gives the same move.
- Votes, signatures and accepted offers: the rule-based bot's rule. The checkpoints were trained with
  `vote_mode=bot`, so the network never learned to vote, and it has no action for deals or offers.
- Every event goes through `Game.apply`, so through `Engine.step`.
- The network's memory (MinGRU state) starts at zero each game. Between one seat's decisions it follows the
  weights file's **state rule**, which must match how the checkpoint was trained:
  - `carry`: it goes on from the seat's last decision. This is the harness's eval (`rl/reference/policy.py`,
    `Player`) and its games against bots, so every published eval number used it.
  - `turn`: it is set to 0.5 at the start of each of the seat's turns and goes on within the turn. In self-play
    training, the zero observations a seat gets while it waits drive its state to 0.5 (see `ADVICE` on PR #11).
  - `zero`: zero at every decision. This is behaviour cloning.
  The converter reads it from the meta's `gru_state`, or from `--gru-state`, and refuses to guess.
- The driver keeps each table's memory in the server process and moves a seat's state on after its move goes
  through. After a restart, a seat's state starts again from zero.

## Limits, plainly

Layout version 2's limits are the engine's own (16 resources, 16 kinds of piece, 100 spots, 48 laws, 6 seats), so
every game that passes `G.Valid` fits. When more than 128 placements are legal at once, only the first 128 in the
harness's order have a row, as in training; end turn is always on offer. A checkpoint of another layout is refused
when the server starts.

## Checks

- `make policy-check`: makes stand-in weights if `policy.chpw` is missing, runs the differential test (with game
  resets and turn starts, under the file's state rule), plays every world in the Library to its end at 2, 4 and 6
  seats (where the world allows) with the policy in every seat, and plays a table of policy bots on every world
  through the real server over HTTP (`scripts/policy_server_check.py`).
- `.lake/build/bin/charter-policy-check WEIGHTS N --vs-hand`: one policy seat against current bots, N games per
  world. Prints win rate, target wins against round-limit wins, and points.
