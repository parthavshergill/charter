# Hero plot

![hero](hero.png)

One chart: how often the trained Charter bot wins, one bot against three opponents, across the checkpoints of one
training run (`entity2/hero-v2`). It shows three kinds of bot opponent and three Claude Sonnet seats.

## What the bot is

- **Network:** `entity2`'s entity encoder (E 32) with a pointer over placements and bank trades, MinGRU 128, and
  170,016 weights. Layout version 2, so it plays any game that passes `G.Valid`, at 2 to 6 seats.
- **Warm start:** behaviour cloning of `hand`, our rule-based bot, with the value also pretrained. This is step 0 on
  the plot. It is not "from scratch".
- **Then PPO:** with the waiting-row fix (`stale_wait`), self-play, and `champion` bots in half the games
  (`bot_share=0.5`).
- **What it can't do:** propose laws, talk, or make or accept offers. Its votes follow `hand`'s rule.
- **The evolved rival:** `champion` comes from evolutionary program synthesis: weights plus strategy rewrites, kept
  when they won in the arena. The plot shows `champion-closed`, which makes and accepts no offers, because our bot
  can't trade.

## What the points are

- **Bot opponents:** `rl/eval --quick`, greedy. 400 games per world on Island and Not Catan, so 800 per point, with
  the same seeds at every checkpoint. The bands are 95% Wilson intervals.
- **Sonnet:** three Claude Sonnet subagents, one per seat, on Tutorial Island. They play against the bot seat of a
  local server built from PR #31 (`CHARTER_BOT=policy`, weights converted with `--gru-state carry`).
  - The bot rotates through every seat.
  - Each Sonnet seat gets the same plain prompt (`sonnet_seat_prompt.md`): the rules from
    `Server/player_rules.md` and the seat commands.
  - `seat.py --mode restricted` gives Sonnet only the bot's moves: end turn, bank trades, placements and
    declarations. It refuses everything else in code. Neither side can propose a law, so no vote ever comes up.

## Files

| File | What it does |
|---|---|
| `plot.py` | Draws `hero.png`, `hero-dark.png` and `hero.svg` from `data/` |
| `stage.sh` | Copies checkpoints to `/vol/hero/ckpt/<run>/` on volume `charter-rl`, each with its own meta, so eval never touches the training agents' folders |
| `fetch.sh`, `collect.py` | Fetch the eval reports from `/vol/hero/<run>/e<step>/`, and write `data/eval.csv` (one row per checkpoint, world and opponent, with target and round-limit wins) |
| `seat.py` | The HTTP client for one seat, used by the Sonnet subagents |
| `sonnet_seat_prompt.md` | The prompt each Sonnet seat gets (`_full.md`: the same, with talk, offers and laws) |
| `games/<CODE>.json` | Each Sonnet game: settings, result, final view and event log |
| `data/sonnet_games.txt`, `sonnet_csv.py`, `data/sonnet.csv` | Which games count, and their totals by checkpoint |
| `summarize.py` | A short reading of a saved game: moves by type, and what each seat built, in order |

`data/` is in `.gitignore`, so its files are force-added.

## How to reproduce

Stage the checkpoints:

```bash
rl/hero/stage.sh entity2/hero-v2/ckpt/charter/1793573211163 1 "<train args>" 0 4915200 9830400
```

Evaluate one checkpoint (repeat for each step):

```bash
cd rl && CHARTER_RL_NAME=hero modal run modal_app.py --action eval --run hero/hero-v2 --eval-name e<16-digit step> --subjects hero/ckpt/hero-v2/<16-digit step>.bin --games 400 --quick --opponents hand,random,champion-closed,champion
```

Fetch the reports and draw the plot:

```bash
rl/hero/fetch.sh /tmp/hero-reports && python3 rl/hero/sonnet_csv.py && python3 rl/hero/plot.py
```

Eval runs on Modal CPU containers (8 CPUs each), with no GPU. `rl/entity/policy.py` and `entity_numpy.py` are copied
from `rl/entity2` so that `rl/eval` on `rl-harness` can load entity checkpoints.
