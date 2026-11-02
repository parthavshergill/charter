# CANDIDATE 7: `r3-long2` at 41.3M steps (round 3)

- `policy.bin`, `policy.bin.json`: from `/vol/entity2/r3-long2/ckpt/charter/1793593242508/0000000041287680.bin` on the volume `charter-rl`.
- Shape: the same as CANDIDATE 6. Layout 2 with per-move rows, 180,064 parameters. See `../c6/README.md`.
- Training:
  1. CANDIDATE 6's run `r3-c`, at 50M steps.
  2. Then 41.3M more steps on `island,not-catan,pack-train` (dealt maps), with three `table` bots in 75% of games.
  3. Settings: lr 1.5e-3, ent 5e-4, `vf_clip_coef` 2, `vf_coef` 4, horizon 32, `stale_wait`, float32.
