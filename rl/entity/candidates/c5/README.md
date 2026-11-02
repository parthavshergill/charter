# CANDIDATE 5: `hero-v2` at 184.8M steps (its last checkpoint)

- `policy.chpw`: the server's policy weights. It was made by `scripts/policy_weights.py` (branch `claude/confident-clarke-cx3ooo` at `b92458b`) from `/vol/entity2/hero-v2/ckpt/charter/1793573211163/0000000184811520.bin` on the volume `charter-rl`, with `--gru-state carry`.
- `policy.bin.json`: that checkpoint's meta. Its `commit` field is the commit that wrote the meta. The training code is `7995aa3`, on branch `rl/entity2`.
- Recipe:
  1. BC of `hand` with value fitting (`/vol/entity2/bc-v2/bc_pointer_v.bin`).
  2. PPO with the waiting-row fix, `champion` bots in 50% of games, lr 5e-4, ent 5e-4, `vf_clip_coef` 2, `vf_coef` 4, a target of 200M steps.
  3. A checkpoint every 10 epochs, about 1M steps.
- Shape: the same as CANDIDATES 3 and 4. Layout 2, entity encoder E 32, MinGRU 128, the linear decoder plus the pointer block (96 x 128), 170,016 parameters.
