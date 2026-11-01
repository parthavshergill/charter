# How cloud agents work together here

The owner's laptop is closed and the lead session is away. Agents cannot message each other, so they coordinate only through GitHub on `parthavshergill/charter`. Read `rl/HANDOFF.md` and `rl/PUFFER_FINDINGS.md` first. `rl/puffer-smoke/` holds the smoke test's scripts, recovered from a transcript, so a late edit may be missing. Pinned PufferLib: `ea7f989371270d2948f96728bda8aec5e7634a4c`.

## Signals

| Who | What | Where |
|---|---|---|
| Harness builder | Draft PR titled `[RL] Shared harness`, from `rl-harness` to `main` | Opened early, as soon as it has a first push |
| Harness builder | A comment that starts `HARNESS-READY <full commit sha>` | On that PR, when the checks below pass |
| Architecture agent | Draft PR titled `[RL round 1] <name>`, from `rl/<name>` to `rl-harness` | Opened when it starts work |
| Architecture agent | A comment that starts `HARNESS-BUG`, with the exact error | On the harness PR |
| Architecture agent | A comment that starts `RESULT`, with the report below | On its own PR, when finished |
| Anyone | A comment that starts `BLOCKED`, with the exact error | On its own PR, when it cannot go on |

A later `HARNESS-READY` replaces an earlier one. Use the newest. Read PRs with `gh`, your GitHub tool or the REST API. The repo is public, so reading needs no token.

**Waiting:** an architecture agent checks for `HARNESS-READY` every 5 minutes, using a shell loop with `sleep` and short tool calls, for up to 90 minutes. If none appears, it posts `BLOCKED` and stops. The builder checks its PR for `HARNESS-BUG` every 5 minutes after signalling ready, for up to 60 minutes, and fixes each with a new `HARNESS-READY`.

## What `HARNESS-READY` means

All of these passed on Modal, and the comment gives the numbers:
- the action mask agrees with `Engine.step`, including a seeded error that the test catches
- same seed and actions give the same result
- one short training run on Tutorial Island through PufferLib, with the score moving
- `eval` on that policy, and on a random policy and the `hand` bot, producing the report

## Limits, for everyone

- **Spending:** builder $10, each architecture agent $15, on Modal only, for all of its runs. Set a hard limit and timeout on every job. Check `modal billing report --for today --json`, filtered to your own apps, before each large run. Stop at your limit and report it.
- **Time:** finish within about 90 minutes of your first action, unless your work is nearly done. Post what you have.
- **Modal:** name apps `charter-rl-<your name>`, and touch nothing else in that workspace. It holds other projects. Use the volume `charter-rl`, with one folder per run.
- **GitHub:** never merge anything, never push to `main`, never force-push, never close another agent's PR. Only the builder pushes to `rl-harness`.
- **The repo is public:** never commit or print a secret. No checkpoints, datasets or files over 1 MB. Those go on the volume.
- **The game:** no changes to the engine, game rules, or locked statement files (`scripts/statement_lock.sh`). Every action goes through `Engine.step`. Never write a second model of the rules.
- **No attribution lines** in commits, PRs or comments. No dates in commit messages or docs.
- **Reuse first:** don't write a trainer or a PPO. PufferLib has them.
- **Keep the Anthropic, Prime and Tinker keys out of this round.**

## Round 1: which encoder?

Fixed for all three: `vote_mode=bot`, per-move rows off, no names in observations, training on Tutorial Island and Not Catan, held out: Slime Parliament, The AI Bubble, Strike the Earth, The Pirate Republic. The same training steps and the same `eval` seeds, using the defaults in the harness at `HARNESS-READY`.

| `<name>` | Encoder |
|---|---|
| `flat` | PufferLib's plain linear encoder over the flattened input |
| `entity` | A shared network per entity with a masked pool. `ocean/asteroids/asteroids.cu` is the model |
| `attention` | A small attention encoder. `ocean/minimal/minimal.cu` has an attention option |

A custom encoder must pass the reference test: its forward outputs and hand-written gradients match a PyTorch version given the same weights and inputs. Keep the policy compact, and report its parameter count.

## The `RESULT` report

Keep it short: encoder and settings, parameter count, steps per second, steps trained, spend, the `eval` table with confidence intervals for training and held-out games, the reference test result, the policy's location on the volume, what failed, and what you would try next. Say plainly if it did not beat `hand`.
