# CANDIDATE 4: `v2-long-champ` at 39.3M steps

- `policy.chpw`: the server's policy weights. It was made by `scripts/policy_weights.py` (branch `claude/confident-clarke-cx3ooo` at `b92458b`) from `/vol/entity2/v2-long-champ/ckpt/charter/1793573820777/0000000039321600.bin` on the volume `charter-rl`, with `--gru-state carry`.
- `policy.bin.json`: that checkpoint's meta. Its `commit` field is the commit that wrote the meta. The training code is `57eb573` (the waiting-row fix) and later, on branch `rl/entity2`. The env code is unchanged since then.
- Lineage (about 99M RL steps in all):
  1. BC of `hand` (`/vol/entity2/bc-v2/bc_pointer.bin`).
  2. `v2-stale`: 60M steps, the waiting-row fix, `hand` bots in 25% of games, lr 5e-4, ent 0.003.
  3. This run: 39.3M steps, the waiting-row fix, `champion` bots in 50% of games, lr 3e-4, ent 1e-3, `vf_clip_coef` 2, `vf_coef` 4.
- Shape: the same as CANDIDATE 3. Layout 2, entity encoder E 32, MinGRU 128, the linear decoder plus the pointer block (96 x 128), 170,016 parameters.
