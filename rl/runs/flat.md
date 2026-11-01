# Round 1: `flat`

The plain linear encoder over the flattened 4434-float observation, as PufferLib ships it. No encoder code is added.
Started from the harness commit named by `HARNESS-READY` (`f6d4c56`). No shared code is changed.

## Runs

All runs are on the volume `charter-rl`, under `/vol/flat/<run>/`, with app `charter-rl-flat`. Each uses the
harness defaults in `rl/puffer/charter.ini` (20M steps, self-play, 25% frozen envs, `vote_mode=bot`,
`move_rows=0`, training on Island and Not Catan), except the one setting named.

| Run | Change from the defaults |
|---|---|
| `default` | none: the run to compare with the other encoders |
| `lr1e-3` | `train.learning_rate=0.001` |
| `lr4e-3` | `train.learning_rate=0.004` |
| `h64` | `policy.hidden_size=64` (and the frozen policies' size) |
| `h256` | `policy.hidden_size=256` (and the frozen policies' size) |

Command, for example:

```bash
cd rl && CHARTER_RL_NAME=flat modal run modal_app.py --action train --run flat/h64 --minutes 12 --max-dollars 0.8 \
  --train-args "--policy.hidden_size=64 --vec.hist_policy_hidden_size=64"
```

Results are in the `RESULT` comment on this branch's PR.
