# Round 3: play worlds it did not train on

`rl/CLOUD_PROTOCOL.md` still applies, except where this file changes it. The lead wrote this file for the owner's RL workstream. Read it with the latest `ADVICE` comments on PR #11, the last `RESULT` on PR #31 and the `NOTE` on PR #18.

## Where round 2 ended

RL improves only the two training worlds. Against 3 `table`, in `rl/eval`:

| subject | training worlds | held-out worlds |
|---|---|---|
| imitation (`hero-v2` at 0) | 13.6 | 14.2 |
| CANDIDATE 5 (`hero-v2` at 184.8M) | 34.0 | 16.1 |

Through the server, CANDIDATE 5 wins 18% on all nine worlds, and 7% on the three newest. An equal player wins 25%.

## The number that counts

Win % against 3 `table` on `main`'s nine worlds, with `rl/eval --worlds main`. Report target wins and limit wins apart. Report Pirate Republic apart too: the table bot never declares, so the hat is uncontested there.

## Rules

- `pack-train` worlds are allowed in training. The owner's plan includes generated environments. `gen-*` games stay for "can it play" only.
- Shipped worlds other than Island and Not Catan stay out of training. `pack-val` is for choosing settings.
- Everything else from `rl/ROUND2.md` stands: no fallback bot, no names in observations, the policy never proposes rules, and the anti-reward-hacking rules are not weakened. Read real games at each milestone. Hollow limit wins do not count.
- Nothing is merged, and the default bot does not change. That decision is the owner's.

## Who does what

| Name | Job | Modal limit, this round |
|---|---|---|
| `entity3` | Plans A and B below. It may continue in the `entity2` session and on PR #18 | $25 |

## Plan A: wider worlds

Continue CANDIDATE 5 on `--env.games=island,not-catan,pack-train` with `--env.bot_policy=6`, at harness `97cd048` or later. The recipe is in the `NOTE` on PR #18. Evaluate at 30M and 50M steps. Stop if held-out worlds are under 19% at 50M.

## Plan B: score every action from what it does

Use `move_rows=1` and a pointer over `moves` rows, so that end turn, bank trades, declarations and builds are all scored from their exact result. Keep the linear part small or remove it. Check the gradients against PyTorch in `test_reference.py`, with seeded errors. Start with imitation of `table`, then RL on Plan A's worlds. Stop if The Pit stays at 0 of 40 and held-out worlds gain under 3 points. Report the time per decision on CPU and what the server path needs.

## Then

Combine what works, and train long. A larger learning rate is a cheap side test, because the clip fraction stayed near 0.001. A decision-time blend (`logit + c·(V(s′) − V(s))`, about c = 30) is on PR #11; it may be added to a later candidate if a fresh seed set confirms it.

## Reporting

Post `PROGRESS` on PR #18 at each evaluation, with the nine-world table and a `REVIEW` of real games. Post `CANDIDATE` with `.chpw` weights for anything that beats CANDIDATE 5 on the number that counts. It is then tested through the server.

## Part 2: more seeds, and worlds like the weak ones

Part 1 ended with the `RESULT` on PR #18. This part uses the rest of the round's $25. The rules above stand. The number that counts is now the server-like row (`rl/eval --worlds main --random-map 0 --laws off`), with 800 games per world for any `CANDIDATE`. The bar is CANDIDATE 9: 21.7 on nine worlds, and 15.9 held out. Evaluate with `prune_declares` and `declare_once_per_turn` on, and read every summary line.

1. **Several seeds.** Fixed Island ranges from 10 to 36% across neighbouring checkpoints, so one run's best is partly luck. Run CANDIDATE 7's recipe from `r3-c` at 50M with the switches on, at 3 seeds. Train on fixed and dealt maps together. Report the spread between seeds, and do not choose a checkpoint on a world's score alone.
2. **Worlds like the weak ones.** When `speed` posts `HARNESS-READY` with pack worlds that have upgrade chains and fast targets, add them to training. Report The Pit and AI Bubble apart. Do not count The Pit's lone auction bids or Pirate Republic's uncontested hat as strength.
3. **Seat 3.** Add games where the policy sits last in setup, if this is cheap.
4. **Encoder, if money remains.** LayerNorm and residual blocks (item 4 on PR #11), with gradients checked against PyTorch. It changes the shape, so say what warm start you use and what the server path needs. Stop if held-out gains under 2 points at equal steps.

If the table bot on `main` changes, `speed` will say so. Do not compare numbers across that change.
