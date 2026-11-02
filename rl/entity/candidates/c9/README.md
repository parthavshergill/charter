# CANDIDATE 9: CANDIDATE 7's weights, played with the declaration switches on

- Weights: the same file as CANDIDATE 7, `../c7/policy.bin` (sha256 `278743e0…9f099e`). It is also at `/vol/entity2/c7-pruned/policy.bin` on the volume `charter-rl`.
- `policy.bin.json`: the meta. Its `settings` add `prune_declares: true` and `declare_once_per_turn: true` (harness `3b98ee8`). The policy must be played with these, as the eval did: a declaration that changes nothing is not offered, and each resource can be declared once a turn.
- Shape: layout 2 with per-move rows, 180,064 parameters (see `../c6/README.md`).
