# CANDIDATE 3: `v2-fix` at 44.2M steps

- `policy.chpw`: the server's policy weights. It was made by `scripts/policy_weights.py` (branch `claude/confident-clarke-cx3ooo` at `b92458b`) from `/vol/entity2/v2-fix/ckpt/charter/1793572064307/0000000044236800.bin` on the volume `charter-rl`, with `--gru-state carry`.
- `policy.bin.json`: that checkpoint's meta. Its `commit` field is the commit that wrote the meta. The training code is `57eb573`, on branch `rl/entity2`.
- Shape: layout 2, entity encoder E 32, MinGRU 128, the linear decoder plus the pointer block (96 x 128), 170,016 parameters.
