# RL harness handoff

Branch `rl-harness`, from `bot-arena` with `main` merged. **`rl/` does not build yet and nothing in it has ever run.**

## Done and tested

- `main` is merged. The only breakage was `ServerTests.lean` using `beltSpec`. Its arena tests now use `strikeSpec`.
- `lawsFor` moved to `Server/LawLibrary.lean`, so the environment can use it without the proofs. `PreviewCheck` imports it.
- `Play.commit` split out of `advance` in `Server/ArenaPlay.lean`.
- `lake build charter-sim charter-arena ServerTests` passes after those changes. `make smoke`, `make audit` and `charter-arena --check-reference` were NOT run.

## Half done, never compiled or only partly

All under `rl/lean/CharterRL/`, in import order:

- `Layout.lean`: limits, observation tables, action layout, JSON. Compiles.
- `Tables.lean`: game tables, opponents (`hand`, `fair`, `closed`), `Settings`, row order, random maps. **Does not compile:**
  - `Tables` cannot derive `Inhabited`; write it by hand.
  - `shuffled` needs `Inhabited PieceDef` and `Inhabited Region`. Add local instances or drop the bound.
  - `randomMap` needs a type on its `filter` lambda.
- `Actions.lean`, `Obs.lean`, `Env.lean`: written, never compiled, so expect errors. They are blocked on `Tables.lean`.
- `lakefile.toml` names two targets whose roots do not exist yet: `CharterRL.CheckMain` and `CharterRL.Capi`. Neither is a default target, so `lake build` is unaffected.

## Next, in order

1. Make `CharterRL.Env` compile.
2. Write `Capi.lean` (exports) and `rl/env/capi.c` (runtime init, thread init, copies into caller buffers). Build the shared library: compile `capi.c` to `rl/build/capi.o`, then `lake build charter-rl-shared`, which links with `-shared`. This link is an untried idea.
3. Write `Check.lean` and `CheckMain.lean`:
   - mask against `Engine.step` on every action, on Tutorial Island and Not Catan, with a seeded error to prove the test catches one
   - determinism
   - changing `State.seed` changes no observation number
   - renaming and reordering resources and kinds gives the same encoding up to that reordering; this needs a renamer over the law syntax
   - full `G.checks` on sampled random maps
   - steps per second, memory, and the cost of `move_rows` and the preview
4. Write `rl/OBSERVATIONS.md`, `rl/layout.json` and `rl/games.json`: train on `island` and `not-catan`; hold out `slime-parliament`, `ai-bubble`, `strike-the-earth` and `pirate-republic`.
5. Write `rl/eval`: same seeds for everyone, one independent seed per game, exactly equal seats, Wilson intervals. Report tables with and without laws, setup and play measured apart, and each policy's settings. Test subjects are random-legal and hand. Policy format: `.npz` weights plus a JSON `meta`.
6. Write `rl/reference/`: flat, per-entity and attention encoders, then the PufferLib shape below, plus the NumPy test with a seeded error.
7. Write `rl/imitation/`: use `Env.suggest` for labels, store float16 under `results/`, then run behaviour cloning through eval.
8. Write `rl/modal_app.py`: `train`, `eval` and `test`, apps prefixed `charter-rl`, one Volume folder per run, a hard spending limit and timeout on every command, `MODAL_PROFILE=charter`, at most $5 for testing. Reuse the evolve `modal_backend.py`, `modal_worker.py` and `money.py`, and `charter_puffer_smoke.py`. Not started; none of those files have been read yet.
9. Write `rl/puffer/charter.h` and its config, and `rl/README.md`.

## Measured so far

- **Steps per second: not measured.** The environment has never run.
- **Per-move row cost: not measured.**
- Preview cost: not measured.
- `G.checks`, one call each: Island 0.76 ms; the games with founding laws 9 to 15 ms. That is too slow per reset, since the arena plays a game in 1.4 to 2.3 ms. `Env.start` therefore runs only `shapeChecks` per map, whose own cost is not measured. `LawChecks.lean` does not read regions, so the founding check should not change with the map; step 3 must confirm this with full checks.
- Largest game sizes: 7 resources, 54 spots, 72 links, 18 tiles, 1 link kind, 6 spot kinds.

## Decisions, all in the code and all untested

- Limits: 6 seats, 8 resources, 1 link kind, 8 spot kinds, 60 spots, 84 links, 24 tiles, 16 laws, 64 move rows. That gives 695 actions.
- No names in observations. Resources and kinds appear by what they do.
- `slot_order` is `shuffled` by default, so no row always means the same resource. This may hurt a linear decoder. `game` is the other value. **This is my call, not the owner's. Measure both.**
- Seats are ego-centric: this seat, then turn order.
- `vote_mode` is `random`, `bot` (`lawOk`) or `policy`. Under the first two, votes never reach the caller.
- `move_rows` is off by default and appended after the base tables, so the base layout does not move.
- The end-turn row uses `predictNextTurn` averaged over the dice, because `Engine.step` would reveal the real roll.
- `law_every` is the chance of a law at turn start, 1 in N, and defaults to 8. The seat whose turn it is proposes. Seats vote in turn order before anything else. A strategy seat that gives no vote votes no.
- Declaring is offered only if a founding or library law reads a declared number. So on Island the engine accepts declarations the environment does not offer. The mask test must count these apart. A move while a vote is due is the same case.
- The end-turn mask bit is `isTurnOf`, justified by theorem `endTurnNow_some` and still to be checked by the mask test.
- `fair` weights: `acceptGoods` 1, `acceptNeed` 1, `acceptMargin` 1. `closed`: `acceptMargin` 10. Same as the evolve loop.
- Lineup entries are `caller`, a strategy name, or `a+b` (`a` in setup, `b` after). This is how setup and play get measured apart.
- Observations are built in Lean as `FloatArray` and copied by C, so the Lean code needs no `extern`.

PufferLib facts, read at the smoke worker's pinned commit `ea7f989`:

- The encoder is linear, with no activation.
- Each MinGRU layer computes `x @ W(3H x H)` to get hidden, gate and proj, then:
  - `z = sigmoid(gate)`
  - `h_tilde = hidden + 0.5` if `hidden >= 0`, else `sigmoid(hidden)`
  - `h = lerp(state, h_tilde, z)`
  - `s = sigmoid(proj)`
  - `out = s*h + (1-s)*x`
- The decoder is linear, `H` to actions + 1, the extra output being the value.
- `obs_t` may be float, `ACT_SIZES` is `{N}`, and `Agent.action_mask` is one byte per action.

## Known problems

- `fair`, `closed` and `hand` differ only in accepting offers. No seat in the environment makes offers, because the caller cannot and those three have `offerLimit` 0. So those three panels will play identical games on the same seeds. Eval must say so rather than present them as three results.
- The pool holds only `hand`. The night2 champion `s9x0` is not in the repo, so imitation can only target `hand`. Its strength also relied on offers.
- A linear decoder has one fixed output per action, which may not carry over to held-out maps with different spot numbering.
- The Linux `-shared` link against Lean's static runtime is unverified.
- No servers or Modal apps were started. Nothing has been pushed.
