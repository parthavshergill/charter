# The entity encoder, with a pointer decoder (`entity2`)

A compact policy for Charter: 170,016 parameters at layout version 2.

## The network

- **Encoder** (`charter_entity.cu`; `entity_torch.encode` is the reference):
  - For each base table of `rl/layout.json`, one shared layer per row: `relu(W_t x)`, 32 numbers (`CE_ENTITY_DIM`), no bias.
  - Then a mean over the table's real rows (column 0 above 0.5).
  - Then one layer, `W_out`, from all the means joined to the hidden size (128).
- **Residual block** (optional, `-DCE_RESID`, float32 builds; meta `"resid": 1`): after `W_out`,
  `out = o0 + W_r2 relu(W_r1 LayerNorm(o0))`, with a LayerNorm gain and bias (128 each) and `W_r1`, `W_r2` (128 x 128).
  It adds 33,024 numbers. `tools/graft_resid.py` adds it to a checkpoint with `W_r2 = 0`, so the network starts
  out playing exactly as before. PufferLib's Muon gives 1-D parameters a plain update that isn't rescaled, so the
  gain and bias barely move in training (about 1e-4 over 12M steps): in effect, the LayerNorm has no gain or bias.
- **GRU:** PufferLib's MinGRU, 1 layer.
- **Decoder:** PufferLib's linear decoder (one output per action, and the value). With `-DCE_POINTER` it also adds a score taken from the rows that an action names. Two reasons it helps:
  - a placement is an action by its row of `places`, and a fixed output per row cannot know what the row holds;
  - resource rows are shuffled each game, so a fixed output cannot know which resources a bank trade names.

  It computes `q = A h`, with `A` 96 x 128, split into `q_place`, `q_give` and `q_get`:

  ```
  logit[place p]     += q_place . relu(W_places x_p)
  logit[bank i -> j] += q_give . relu(W_res x_i) + q_get . relu(W_res x_j)
  ```

  Its gradient on those rows goes back into the encoder. The layout-1 version, which scored spots and links, is in the git history.
- **Checkpoint:** raw float32 blocks, each padded to a multiple of 8 floats, in this order: one `W_t` per table, `W_out`, decoder, `A`, GRU. The meta says `"format": "puffer-entity"`, `"pointer": 1` and `"layout": 2`. Eval's NumPy forward is `entity_numpy.py` (`policy.py`).

## Checks

`test_reference.py` builds the CUDA encoder, and the pointer decoder, as a library on a GPU. It compares the forward pass and every weight gradient with PyTorch on the same weights and inputs, in float and bf16. It then rebuilds with seeded errors, which must fail:
1. padding rows counted in the mean
2. padding rows get gradient
3. the decoder's gradient into the encoder rows dropped
4. a wrong gradient on `A`
5. (moves) the action column left in the encoder's input
6. (moves) a wrong gradient on the move query
7. (`--resid`) the LayerNorm's variance term dropped in its backward pass
8. (`--resid`) the skip connection's gradient dropped

Run it with `modal run entity/tools/modal_extra.py::reftest_main`, and add `--extra="--moves"` or `--extra="--resid"` for those builds.

## Training recipe (the best so far)

1. **Behaviour cloning of `hand` into this network.**
   ```
   bc_entity.py DATA --collect 400 --pointer [--vf-coef 1]
   ```
   It covers Island and Not Catan at 3 or 4 seats, with `declare_always`. `--vf-coef` also fits the value row to each seat's final reward.
2. **PPO from that warm start.**
   - optimiser: lr 5e-4, ent 5e-4, `vf_clip_coef` 2, `vf_coef` 4
   - opponents: `hand` (or `champion`) bots in half the games (`env.bot_share=0.5`, `env.bot_policy`), self-play otherwise
   - environment: `env.declare_always=1`, and the waiting-row fix (`--meta-extra '{"stale_wait": 1}'`, compile flag `CHARTER_STALE_WAIT`)

## Tools (`tools/`)

- `launch.sh RUN MINUTES DOLLARS E "TRAIN ARGS" ["EXTRA META"]`: a detached training run on Modal.
- `latest.sh entity2/RUN`: the newest checkpoint of a run.
- `quick_eval.sh CKPT LABEL STALE "ARGS"`: writes a layout-2 meta, then runs `rl/eval --quick` against `table` and `hand`, on dealt maps and on the server-like row (`--random-map 0 --laws off`), keeping saved games. `GAMES`, `MOVES=1`, `PRUNE=1`, `RESID=1`.
- `score.py REPORT.json ...`: the nine-world, clean (no subject declaration) and held-out numbers from `rl/eval`'s report; `--laws` for the wild sets.
- `graft_moves.py`, `graft_resid.py`: add the moves table, or the residual block, to a checkpoint without changing how it plays.
- `games.py`: plays full games and writes an action-by-action log. With `--count`, it splits wins into target wins and round-limit wins.
- `modal_extra.py`: Modal entry points for game logs, win counts, BC, metas and the reference test.

## Learning from the improved move (`expert_iter.py`, round 4)

- `collect`: the policy plus the decision-time blend (`logit + C·ΔV` over its 4 best moves, each tried with `Engine.step`)
  plays one seat against `table`, and every decision is recorded (observation, GRU state, mask, the moves tried and their
  ΔV, the table bot's move).
- `distill`: fits the policy to `softmax(logit + C·ΔV)` with the recorded GRU state, holding the value to the recording
  network's. `--no-declare-bonus` gives declarations no lookahead bonus; `--imitate W` adds the table bot's move where the
  improved move ends the turn and `table` builds or trades.
- Run on Modal with `modal_extra.py::ei_collect_main` and `::ei_distill_main`. CANDIDATE 10 is two rounds of it from
  CANDIDATE 9 (`candidates/c10`).
- The blend's two-step candidate (`#mix4c100+two`, `entity_numpy.py`): a bank trade scored with the build it makes legal.

`rl/puffer/charter.h` has a training-only switch, `learner_no_declare` (default 0): the learner's mask leaves out
declarations in training. Eval and the server are unchanged.
