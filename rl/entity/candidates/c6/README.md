# CANDIDATE 6: `r3-c` at 29.5M steps (round 3)

- `policy.bin`, `policy.bin.json`: a PufferLib checkpoint from `/vol/entity2/r3-c/ckpt/charter/1793590065940/0000000029491200.bin` on the volume `charter-rl`. There is no `.chpw` yet: the server path's `scripts/policy_weights.py` does not know per-move rows, and refuses the size.
- Shape: layout 2 **with per-move rows** (`move_rows=1`, observation 15177), 180,064 parameters, in this order:
  1. `W_t` for the 9 tables, the last being `moves` (32 x 58)
  2. `W_out` (128 x 288)
  3. the decoder (517 x 128)
  4. `A` (128 x 128): q_place, q_give, q_get, q_move
  5. the GRU (384 x 128)
- The moves table's `action` column is not a feature. The encoder reads it as 0, and it routes each moves row's score `q_move . relu(W_moves x_m)` to that action's logit. Reference: `rl/entity/entity_numpy.py` and `entity_torch.moves_logits`.
- Training:
  1. CANDIDATE 5 grafted with per-move rows (`rl/entity/tools/graft_moves.py`). The new parts start at 0, so it starts playing exactly as CANDIDATE 5.
  2. Then PPO on `island,not-catan,pack-train`, with `table` bots in 50% of games.
  3. Settings: `stale_wait`, lr 1e-3, ent 5e-4, `vf_clip_coef` 2, `vf_coef` 4, horizon 32, float32 (`PRECISION_FLOAT`), 29.5M steps.
