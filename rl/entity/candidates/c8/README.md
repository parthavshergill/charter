# CANDIDATE 8: `r3-fixed` at 29.5M steps (round 3)

- `policy.bin`, `policy.bin.json`: from `/vol/entity2/r3-fixed/ckpt/charter/1793593909753/0000000029491200.bin` on the volume `charter-rl`.
- Shape: the same as CANDIDATE 6. Layout 2 with per-move rows, 180,064 parameters. See `../c6/README.md`.
- Training:
  1. CANDIDATE 6's run `r3-c`, at 50M steps.
  2. Then 29.5M more steps on `island,not-catan,pack-train` **with each world's own map** (`random_map=0`), with three `table` bots in 50% of games.
  3. Settings: lr 1e-3, ent 5e-4, `vf_clip_coef` 2, `vf_coef` 4, horizon 32, `stale_wait`, float32.
- No declaration loops: 0 declarations by the policy in 126 saved games, on fixed and dealt maps.
