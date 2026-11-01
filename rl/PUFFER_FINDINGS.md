# PufferLib smoke test: findings

Pinned commit: `PufferAI/PufferLib` `ea7f989371270d2948f96728bda8aec5e7634a4c`. File and line references are at this commit. The test's scripts are in `rl/puffer-smoke/`. It spent about $0.18 on Modal.

Each section says what ran and what was only read.

## Recommendation

Use PufferLib with small named changes. Write no training code.

| To write | Size | Status |
|---|---|---|
| Env wrapper around the Lean engine (`puf_init`, `puf_step`, masks, obs) | about 270 lines (`lean/leantiny.h`) plus a 60-line C shim | Ran on a toy game |
| `build.sh` branch to link Lean | 3 lines, or none with the shared runtime | Ran |
| Log fields `policy_0_score` and `draw_rate`, needed by `match` | a few lines per env | Not run with both added |
| Stop PPO training on frozen seats' rows | about 5 lines, an estimate | Read only, decide first |
| Warm start in `train`, only if imitation is wanted | about 5 lines, an estimate | Read only |
| Imitation loss, only if wanted | 60 to 100 lines, an estimate | Not written |
| Set encoder | 300 to 450 new lines, about 10 edited, an estimate | Read only |

## 1. Build and train on Modal: works (ran)

GPU: Tesla T4, driver 610.57.04, CUDA toolkit 12.9.86, `cpu=4`, 16 GB. Default bf16 precision ran on the T4. Build time was 9 to 10 s.

| Run | Steps | SPS | Time | Result |
|---|---|---|---|---|
| breakout | 54.9M | 1.2M | 48 s | score 1 to 765, perf 0.001 to 0.885 |
| chess, self-play | 89.7M | 299.6K | 299 s | small gain, below |

Chess checkpoints, about 1,000 games each: against a random mover, untrained 0.380 and trained 0.526. Trained against untrained: 0.642 (`hist_score`). During training, draw rate fell from 0.99 to 0.85, and invalid action rate was 0.

Flags passed to chess: `--vec.num_threads=4 --base.checkpoint_interval=20 --selfplay.opp_timeout_steps=10000000 --env.fen_curric_pct=0`. `resources/chess/fens.txt` is not in the repo at this commit, so the curriculum was off.

## 2. Four seats, one acting at a time: works with no trainer change (ran), with two costs

A tiny 4-seat, turn-based, non-zero-sum game on the Lean engine ran (`lean/leantiny.h`). Self-play and frozen seats both ran, with one past policy or three separate ones (`--vec.num_policies=4`).

Against Lean bots, after 20M steps (6.3 s, 3.2M SPS):

| Opponents | Untrained perf | Trained perf |
|---|---|---|
| random | 0.250 | 0.925 |
| greedy | 0.0085 | 0.210 |

How seats work (read):
- **Fixed policy per seat:** `Agent.policy` is read once at setup (`src/pufferl.cu:1048`, `:1073`). To avoid seat bias, the env must shuffle seats inside each game (`ocean/chess/chess.h:3450`).
- **`hist_policy_percent` counts envs, not agents** (`src/pufferl.cu:1042`). On the other envs every seat plays policy 0.
- **Shipped envs:** the ones that set `.policy` beyond 0 all have 2 seats. This test is the only evidence for 4.
- **Seats cannot be skipped.** Every seat gets a forward pass every tick (`src/pufferl.cu:830-877`). A waiting seat is masked to one no-op (`ocean/chess/chess.h:1707-1710`, `ocean/chain_reaction/chain_reaction.h:276-278`), and the env must write the mask for every seat.
- **A skip mode would be a large change,** because rollouts are a fixed `T x B` (`src/pufferl.cu:363-372`). Not recommended.

The two costs:
- **Cost 1 (follows from the code):** with 4 seats, 3 of 4 rows are waiting rows, so GPU work per real move is 4 times higher.
- **Cost 2 (read only, not tested):** rows from frozen seats appear to feed the PPO update. The buffer holds all `total_agents` rows (`src/pufferl.cu:1976-1977`), minibatches walk all of them (`:1502-1512`), and no filter by `policy_layout[1]` was found. With 25% frozen envs and 4 seats, about 19% of rows come from other policies; chess at 10% and 2 seats has 5%. The fix would limit rows to `policy_layout[1]` when `num_buffers = 1`.

`./puffer match` gave no 4-seat number. It needs `env/policy_0_score` and `env/draw_rate` in the env log (`src/pufferl.cu:2901`, `:2905`) and exits with `missing key` otherwise.

## 3. Scripted bots: works (ran). Imitation: does not exist

- **How bots work:** they live inside the env, in its `puf_step`. The env defines `PUF_HAS_BOT_POLICY` and `puf_set_bot_policy` (`src/pufferenv.h:51-57`).
- **The ladder:** after training it sets `env.num_agents=1` and `env.num_bots=1`, then walks `eval_bots` (`src/pufferl.cu:3289-3343`). `num_bots=1` is hard-coded, so a 4-seat env must treat `num_agents=1` as "bots fill the other seats". `leantiny.h` does.
- **Ran with two Lean bots:** `bot_eval policy=0 games=16384 perf=0.9217`, `policy=1 perf=0.2069`. An existing Lean bot would plug in the same way, as an `@[export]` function.
- **Imitation:** no behaviour cloning in `src/` or the config.
- **No warm start:** `load_model_path` is read only by eval and match (`src/pufferl.cu:2956-2964`), so `train` ignores it.

## 4. Policy shape and export: works (ran), except `--web`

- **Shape (read):** one linear encoder, `num_layers` MinGRU layers, and one linear decoder whose last output is the value (`src/algo.cu:1002-1046`). It is set by `hidden_size` and `num_layers`, and self-play forces frozen seats to the same shape (`src/pufferl.cu:3003-3010`).
- **Checkpoint (ran):** raw float32 with no header, each block starting on a multiple of 8 floats. The loader checks only the byte count.
- **`--cpu` (ran, no GPU attached):** `./build.sh breakout breakout_cpu --cpu`, and the player on trained weights scored 748 over 16 episodes, against 0 with no weights. It also ran with the Lean env: perf 0.932 against random bots over 500 games.
- **`--web` (not built):** it compiles the same `src/puffercpu.c` with emscripten and expects `resources/<env>/<env>_weights.bin` (read).
- **Another program (ran):** `policy_reader.py`, about 50 lines of plain Python, matches PufferLib's C forward pass to 4 decimals on all outputs over 3 GRU steps.

## 5. Linking Lean: works (ran)

Lean v4.35.0 on Linux x86_64, inside the trainer on 4 OpenMP threads.

Shared runtime, with no `build.sh` edit:

```
NVCC_EXTRA="-DSMOKE_LEAN SmokeGame.o smoke_shim.o -L$LEAN/lib/lean -lleanshared -lInit_shared -Xlinker=-rpath -Xlinker=$LEAN/lib/lean -Xlinker=-rpath -Xlinker=$LEAN/lib" ./build.sh leantiny puffer_shared
```

Static runtime: a 3-line branch in `build.sh`, like nethack's, adding `-Xlinker --start-group -lInit -lStd -lleanrt -Xlinker --end-group -lgmp -luv -l:libc++.a -l:libc++abi.a`. That binary holds both libc++ and libstdc++. It ran, but no exception path was tested.

Cost per call, plain C threads calling Lean:

| Threads | Scalar call | Step plus bot | Step, bot and obs |
|---|---|---|---|
| 1 | 1.29 ns | 240 ns | 1030 ns |
| 2 | 1.31 ns | 242 ns | 1040 ns |
| 4 | 1.29 ns | 243 ns | 1062 ns |

In the trainer, Env time per epoch of 32,768 env steps:

| Build | Env time | Per env step, wall |
|---|---|---|
| C game | 34 ms | 1.0 us |
| Lean, shared | 187 ms | 5.7 us |
| Lean, static | 182 ms | 5.6 us |

SPS stayed at 3.2M, because model and train time dominated the epoch. The gap between 5.6 us and the bench's 1 us is unexplained. The real engine's cost is unmeasured and will dominate these numbers. The C and Lean toy games gave the same training curve and the same bot results over 16,384 games.

Lean details:
- **Exports:** Lean 4.35 rejects `@&` on `@[export]`, so every export consumes its arguments. Reads go through a shim that calls `lean_inc` first (`lean/smoke_shim.c`).
- **Headers:** `lean_initialize_thread` is not declared in `lean.h`, but the symbol exists. `initialize_SmokeGame` takes only `builtin`.
- **Threads:** keep one `lean_initialize_thread` call per thread. `env_restart` and the workers use different OpenMP teams, so env objects can move between threads (read). Training ran with no crash.

## Encoder swap: easy in the trainer, needs a C copy for `--cpu` and `--web` (read only, nothing built)

`arch_forward` and `arch_backward` (`src/algo.cu:929-949`) call the encoder only through the vtable, and setup goes through it too (`:951-991`). Frozen policies get the same encoder through `build_arch` (`src/pufferl.cu:1948`). The GRU, decoder, PPO, self-play and sweeps need no change.

A set encoder already exists: `ocean/asteroids/asteroids.cu`, 319 lines. It is a shared layer per entity, then a layer and max pool. `ocean/minimal/minimal.cu` has one too, with an attention option.

What to add, with size estimates:
- **Encoder file:** new `ocean/<env>/<env>.cu` with the 7 functions, 200 to 320 lines. Mean pool is shorter; max pool needs tiled kernels and hand-written gradients, as asteroids does. Padded entity slots need a mask in the pool, about 20 lines more.
- **Hook:** `src/ocean.cu`, an include and a branch in `create_custom_encoder` (`:56`), about 4 lines.
- **CPU net:** new `<env>_net.h`, about 110 lines (`ocean/asteroids/asteroids_net.h` is 114), because `make_puffernet` assumes a linear encoder (`src/puffercpu.c:549-573`). Add a branch at each `PUF_*_NET` site in `src/puffercpu.c` (`:614`, `:753`, `:793`, `:816`, `:908`), about 10 lines. `--web` uses the same file.
- **Gradient check:** about 50 lines. Gradients are by hand, so a wrong one trains badly with no error. `tests/test_osrs_entity_encoders_cuda.cu` is a model.

Checkpoints and limits: the format follows the `reg_params` order, and old checkpoints will not load, because the byte count differs. The entity layout is fixed at compile time in asteroids (`:8-13`), and the env is compiled in, so packs with different entity sizes need a common layout or one binary per layout.

## Modal setup that worked

App `charter-puffer-smoke`, image in `rl/puffer-smoke/charter_puffer_smoke.py`:
- `modal.Image.debian_slim(python_version="3.12")`
- apt: `build-essential clang ccache git curl unzip gnupg libomp-dev libgl1-mesa-dev ca-certificates time`
- NVIDIA repo: `deb [trusted=yes] https://developer.download.nvidia.com/compute/cuda/repos/debian12/x86_64/ /`
- apt from that repo: `cuda-nvcc-12-9 cuda-libraries-dev-12-9 cuda-nvml-dev-12-9 cuda-nvtx-12-9 libnccl2 libnccl-dev`. `cuda-nvtx` is required (`nvtx3/nvToolsExt.h`).
- `ln -sf /usr/lib/x86_64-linux-gnu/libomp.so.5 /usr/lib/x86_64-linux-gnu/libomp5.so`
- `git clone` the repo, then check out the pinned commit.
- `PATH` includes `/usr/local/cuda/bin`.
- At run time: `ln -sf /usr/lib/x86_64-linux-gnu/libnvidia-ml.so.1 /usr/lib/x86_64-linux-gnu/libnvidia-ml.so`, and set `CUDA_HOME=/usr/local/cuda`. The driver mount has only the `.so.1`.
- Lean layer: `zstd binutils libgl1`, plus `lean-4.35.0-linux.tar.zst` from the Lean release, unpacked in `/opt`.

`[trusted=yes]` skips the apt signature check. Use the NVIDIA key for anything beyond a smoke test.

Spend check: `modal billing report --for today --json`, filtered to your own apps.

## Not tested

`--web`, sweeps, multi-GPU, and any GPU other than the T4. The real Charter engine: all Lean results are on a 12-cell toy game. Whether PPO on frozen rows really happens. `match` on 4 seats. Long chess training. Tuned settings for 4-seat games. Any encoder change, warm start, or imitation code.
