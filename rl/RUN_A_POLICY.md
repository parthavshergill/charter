# Running a trained policy for one decision

This is for the server path: how a checkpoint from this harness chooses one action in a live game. Everything here
is code that already exists. `rl/eval/eval.py` uses it the same way. Layout version 2 (`rl/layout.json`).

## The parts

| Step | Code | What it does |
|---|---|---|
| 1. Observation | `CharterRL.observe` (`rl/lean/CharterRL/Obs.lean`), reached as `Env.observation` and `charter_obs` | 11465 floats for the seat that must decide |
| 2. Legal actions | `CharterRL.legal` (`rl/lean/CharterRL/Actions.lean`), reached as `Env.mask` and `charter_mask` | 515 bytes, 1 for each action on offer |
| 3. Forward pass | `rl/reference/policy.py` (flat), `rl/entity/entity_numpy.py` on `rl/entity2` (entity with pointer) | 515 logits (and the value) from the observation and the recurrent state |
| 4. Choice | `Player.act` in `rl/reference/policy.py` | the highest logit among legal actions |
| 5. Event | `CharterRL.decode` (`Actions.lean`), applied by `Env.step` and `charter_step` | the action as an engine `Event`, through `Engine.step` |

## 1. The observation

`observe T ep ctx settings base s d places free reach preview` needs:
- `T : Tables`: `Tables.ofSpec spec` for the game (`rl/lean/CharterRL/Tables.lean`).
- `ep : Episode`: which resource and piece sits in which row. `Episode.make G settings.slotOrder seed`. Policies
  are trained with `slot_order = shuffled`, so any fixed order is in distribution. Keep it for the whole game. When
  a law adds a piece, call `ep.seat s.rules.pieces` (as `Env.syncLaws` does).
- `ctx`: `{ weights := .default, board := Board.of G }`. On a dealt (random) map use `Board.remap G T`.
- `base`: `template T ep G seats false`, then `writeLaws base G s.laws` whenever the laws in force change.
- `s`: the game's `State`. On the server, that is `Game.state`.
- `d : Decision`: `.turn seat` on the seat's own turn, or `.vote seat id L` when it must vote on law `id`.
- `places`: `placeList ctx ep s seat free reach`, with `free := freeMap ctx s` and `reach := reachMap ctx s seat`.
  This is the list that the `places` table shows and that actions 387 to 514 index.
- `preview`: `some (previewOf ep s seats id L)` for a vote (and `settings.preview`), else `none`.

`Env.await` does exactly this list, so the simplest server path is to build an `Env` and keep it in step. The
observation never reads `State.seed`, so it shows nothing a seat should not see.

## 2. The mask and 5. decoding

`legal T ep places s d` gives the actions on offer, and `decode T ep places d a` turns action `a` into an `Event`:
- 0: end turn. 1 and 2: vote no and yes (only when `d` is a vote).
- 3 to 258: bank trade, give row `i / 16`, get row `i % 16`, with `i = a - 3`.
- 259 to 386: declare (only in games where a law reads declarations, or with `declare_always`).
- 387 to 514: place `places[a - 387]`.

The mask and `decode` use the same `places`, so compute it once per decision. In setup, end turn is not offered
while a placement is legal. Every action the mask offers is accepted by `Engine.step` (`charter-rl-check` tests
this on every action of every decision). Send the decoded event to the server as that seat's move or vote.

**What the policy never does:** propose laws, make offers, accept offers, or sign deals. The server's bot does none
of these for it, or falls back to its own rules for them. Under `vote_mode = bot` (the training default, and
`entity2`'s runs), **the policy also never votes**: training used `lawOk` (the hand bot's check) for its votes. So
the server must vote with `CharterServer.Bots.lawOk ctx s seat id L` unless the checkpoint's meta says
`"vote_mode": "policy"`.

## 3. The forward pass

The checkpoint is a PufferLib `.bin` (raw float32, each block padded to a multiple of 8 floats) with a `.bin.json`
meta. The shapes come from the meta: `hidden`, `layers`, `obs_size`, `act_size` (516: 515 actions plus the value),
and for the entity encoder `entity_dim` (E, default 32) and `pointer`.

**Flat** (`format: puffer-flat`): blocks `encoder` (hidden x obs), `decoder` (act_size x hidden), then one `gru`
(3·hidden x hidden) per layer. Forward: `x = encoder @ obs`; then each MinGRU layer; `y = decoder @ x`; logits
`y[:-1]`, value `y[-1]`. No biases.

**Entity with pointer** (`format: puffer-entity`, `rl/entity2`): blocks `in_<table>` (E x table width) for each base
table of `layout.json` in order (`global`, `seats`, `resources`, `kinds`, `spots`, `laws`, `proposal`, `places`),
`out` (hidden x tables·E), `decoder` (act_size x hidden), then with `pointer` the block `ptr` (3E x hidden), then
the GRU blocks. Forward (`entity_numpy.py`):
1. For each table: its rows `X` (rows x width); `R = relu(X @ in_t.T)`; the mean of `R` over rows whose column 0
   (`real`) is above 0.5, or zeros if none. Keep `R` for `places` and `resources`.
2. `x = out @ concat(means)`; then the MinGRU layers, as for flat.
3. `y = decoder @ x`; `logits = y[:-1]`.
4. Pointer: `q = ptr @ x`, split into three parts of size E. Add `R_places @ q[0:E]` to logits 387 onward (one per
   `places` row). For bank trades, add `(R_res @ q[E:2E])[i] + (R_res @ q[2E:3E])[j]` to action `3 + 16·i + j`.

**MinGRU** (one layer, at the pinned PufferLib commit; `mingru_step`): `c = W @ x`, split into `h, g, p` of size
hidden; `tilde = h + 0.5` where `h >= 0`, else `sigmoid(h)`; `state' = state + sigmoid(g)·(tilde - state)`;
output `sigmoid(p)·state' + (1 - sigmoid(p))·x`. The state starts at zeros each game.

## 4. The choice, and the recurrent state between decisions

Choose `argmax` of the logits with illegal actions set to minus infinity (greedy, as eval does).

**The recurrent state must move as it did in training.** PufferLib runs every agent's row through the network on
every tick, including the ticks where another trainable seat decides. On those ticks the agent's observation is all
zeros (or, for a checkpoint trained with `stale_wait = 1`, its own last observation), and its state moves. So for
each decision made by another seat between two of this seat's decisions, run the forward pass once on that
observation and keep only the new state. `Player.wait` does this; eval calls it for every decision of another
caller seat. Bots inside the environment (`hand`, `champion` in `bot_share` games) took no ticks in training. On the
server there is no exact match for a mix of humans and bots, so count every other seat's decision, which is what
self-play training saw. Do not skip it: with zero input, each step moves the state halfway to 0.5, so after the
few ticks of a 4-seat round a trained policy's memory is mostly reset, and a state that was never reset is one it
did not see in training.

## In Python, today

```python
from charter import Game                      # rl/env/charter.py, over rl/build/libcharter_rl.so
from reference.policy import load_policy      # with rl/ on sys.path; entity: rl/entity/policy.py
meta = json.load(open(path + ".json"))
player = load_policy(path, meta).player(seed=0)  # greedy
g = Game({"game": "island", "lineup": ["caller"] * 4, "seed": 1, "vote_mode": "bot"})
player.reset()
while not g.over:
    if g.seat == my_seat:
        g.step(player.act(g))                 # observation, mask, forward, argmax, decode, Engine.step
    else:
        g.step(other_action)
        player.wait(g.obs_size)               # the tick the other seat took
```

A server-side bot in Lean needs only steps 1, 2 and 5 from `CharterRL` and the forward pass in step 3, which is
about 40 lines of matrix products. The weights are fixed, so they can be loaded once.
