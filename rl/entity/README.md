# The entity encoder, with a pointer decoder (`entity2`)

A compact policy for Charter: 170,016 parameters at layout version 2.

## The network

- **Encoder** (`charter_entity.cu`; `entity_torch.encode` is the reference):
  - For each base table of `rl/layout.json`, one shared layer per row: `relu(W_t x)`, 32 numbers (`CE_ENTITY_DIM`), no bias.
  - Then a mean over the table's real rows (column 0 above 0.5).
  - Then one layer, `W_out`, from all the means joined to the hidden size (128).
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

Run it with `modal run entity/tools/modal_extra.py::reftest_main`.

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
- `quick_eval.sh CKPT LABEL STALE "ARGS"`: writes a layout-2 meta, then runs `rl/eval --quick` against hand, random, champion and champion-closed, keeping saved games.
- `games.py`: plays full games and writes an action-by-action log. With `--count`, it splits wins into target wins and round-limit wins.
- `modal_extra.py`: Modal entry points for game logs, win counts, BC, metas and the reference test.
