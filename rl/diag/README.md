# Diagnostics for the plateau ADVICE (PR #11)

- `playcheck-record.patch`: applies to `claude/confident-clarke-cx3ooo` at `5b5da78`. Makes `charter-policy-check --vs-hand --record FILE` write, for the policy seat, each observation, the legal actions, the policy's move, the current table bot's move and the points.
- `pit.py WORLD...`: replays those records through CANDIDATE 5 in NumPy and splits each decision's logits into the linear decoder and the pointer.
- `health.py CKPTS WORLDS`: how well the value predicts the win (AUC), and encoder units that never fire, on the same records.
- `coverage.py WORLDS`: observation columns that never change on the training worlds but do elsewhere.
- Eval variants (`rl/entity/entity_numpy.py`): `<ckpt>#perm`, `#nolin`, `#nolinbank`, `#lookK`, `#look`, `#log`.

The scripts read their inputs from the session scratchpad (`S` in `pit.py`); change it to run elsewhere.
