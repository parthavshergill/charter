# Round 2: tune, and go longer

`rl/CLOUD_PROTOCOL.md` still applies, except where this file changes it. Read it first, with `rl/README.md`, and the `RESULT` comments on PRs #13, #14 and #15, and the builder's summary on PR #11.

## Where round 1 ended

Runs were 7 to 8 minutes at 20M steps, and no policy came near `hand`: on training games, flat and entity won 1.5% against 3 `hand` and about 52% against 3 random. The environment is the speed limit: the network's size made no difference to steps per second, at about 50K on a T4 with 8 CPUs. Most agents spent under $2 of $15.

## Roles

| Name | Job | Modal limit, this round |
|---|---|---|
| `speed` | Make the environment faster, and add the stronger opponent. It is the only agent that pushes to `rl-harness` | $10 |
| `flat2` | Tune and train the flat encoder for much longer | $25 |
| `entity2` | The same, for the per-entity encoder from `rl/entity` | $25 |
| `attention2` | The same, for the attention encoder from `rl/attention` | $25 |

Open a draft PR titled `[RL round 2] <name>`, from `rl/<name>` to `rl-harness`, when you start.

## `speed`

Signal with a comment starting `HARNESS-READY` on PR #11, as before.

1. **Environment speed:** the builder's list on PR #11: cache a proposal's preview, which is the same for every voter; work out `freeMap` and `reachMap` once per decision; skip writing zero observations for waiting seats. Then profile for anything else that's large. Report steps per second before and after. All mask, determinism and renaming tests must still pass.
2. **A stronger opponent, as soon as you can, even before speed work is finished:** `rl/opponents/night2_champion.lean` is the best strategy from the earlier evolution run (`g10w44`), and `night2_champion.json` holds its constants and weights. It won about 70% against 3 `fair`, and about 50% with no offers (`closed`), against 25% for an equal player. Build it into the environment and `rl/eval` as the opponent `champion`, using its weights. It is for training and evaluation only, and must never reach the server build. The code imports `Server.BotCore`, and its namespace may need adjusting. Report its eval row. If it depends on offers, say so, and report how it does without them.
3. Fix `HARNESS-BUG` reports.

Don't block the others: they start without you, and pick up your improvements at a sensible point, by rebasing onto a new `HARNESS-READY` between runs.

## `flat2`, `entity2`, `attention2`

1. **Tune, then train long.** Use up to about $5 on tuning at 30M to 50M steps: learning rate, entropy, GAE and gamma, minibatch and horizon, network size. PufferLib's sweep (`./puffer sweep`, Protein) is there to be used, if you can get it to work cheaply; a small grid is fine. Self-play settings are part of this: `hist_policy_percent` and the pool's size and refresh.
2. **Then train the best settings for as long as is useful,** aiming for at least 500M steps. Keep one run at a shared set of settings, the harness's defaults unless `speed` changes them, at the same step count, so encoders can be compared directly. Name it `compare`, and run it to at least 100M steps.
3. **Try a warm start** from imitation (`rl/imitation`, patch `0002`), with its learning rate and entropy tuned, because round 1's warm start lost ground early. Report whether it gets further than starting from scratch, for the same spend.
4. **Reward:** if the policy doesn't learn from win and standing alone, try the small shaping setting and report the difference. Evaluation always stays on real results.

**Long jobs must survive your session.** Run them detached on Modal, with checkpoints to the volume at least every 30 minutes and a resume path, so nothing is lost if your session ends. Set each job's own spending limit and timeout before starting it. Watch for a stuck or falling score, and stop a run that isn't helping: **spend well, not fully.**

**Evaluate each milestone** with `rl/eval` at about 50M, 100M, 200M, 500M steps, against `hand`, `random`, and `champion` once it exists, on training and held-out games. Post a comment starting `PROGRESS` on your PR after each, with the one table, the steps and the spend. Then finish with the `RESULT` report, including a score-over-steps table and what you'd try next.

## Read the games: is it reward hacking, or real strategy?

The owner requires this. A rising score is not enough. At every `PROGRESS` milestone, read real games, not only numbers.

**`speed`:** make `rl/eval` save a small sample of full game logs per table, on the volume, in the event format `make spectate` replays, plus a short readable summary of each game: moves by type, what was built and when, trades, votes, points over time. Do this early, because the others need it.

**At each milestone, every training agent reads at least 5 games** across training and held-out games and different opponents, and adds a `REVIEW` section to its `PROGRESS` comment, quoting specific games. Answer these:
- **Why did it win or lose?** Can you describe its plan in a sentence, and does that plan make sense for this game?
- **Durable or hollow?** Does it build an economy, expand and convert it to points, and adapt to the board? Or does it win through one odd trick?
- **Warning signs:**
  - a win from something that isn't good play: an opponent bot's blind spot, the tie rule, or letting the round limit decide
  - stalling, ending turns with moves available, or games that run to the limit
  - repeated pointless actions, or bank trades that burn value
  - collecting shaped reward without winning more
  - strategies that beat one opponent but collapse against another
  - votes that follow one fixed pattern whatever the law says
  - performance from memorising seats or a board, and not holding up on random maps
- **Cross-play:** does the same policy hold up against opponents it didn't train with? A big gap is a warning sign.

**If you find reward hacking:** stop spending on that run, and post a comment starting `REWARD-HACK` on your PR, and on PR #11, with the games, the mechanism and the root cause. Then rethink the setup rather than tuning around it. The cause will be one of:
- **the training setup** (reward, opponents, self-play pool): fix it on your branch
- **the harness** (an observation, mask or evaluation problem): file `HARNESS-BUG` for `speed`
- **the game** (a rule that really is exploitable): don't change the rules. Report it in your `RESULT`, and in a comment starting `GAME-ISSUE` on PR #11, so that the owner can decide

Report what you changed and whether it worked. An honest "it's exploiting X" is a more useful result than a higher number.

**The goal:** beat `hand` clearly on training games, then `champion`, and do well on the held-out games, which are never used for tuning choices. Use the training games to choose settings, and only report held-out results.

Time limit: about 6 hours, or your spending limit, whichever comes first. Post what you have.
