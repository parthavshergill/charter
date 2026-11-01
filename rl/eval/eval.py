"""One command, one report: how well a policy plays Charter against fixed opponents.

    python3 rl/eval/eval.py SUBJECT [SUBJECT ...] [--games N] [--out DIR] [--jobs J]

A SUBJECT is `random` (a random legal action), `hand` (the hand bot, played by the environment), or a policy file:
a PufferLib `.bin` checkpoint or an `.npz`, each with a JSON `meta` next to it (`<file>.json`). rl/README.md gives
the format.

Everything is fixed, so two runs and two subjects see the same games:
- Opponents: three `hand` bots, then three random players. `fair` and `closed` differ from `hand` only in accepting
  offers, and no seat here makes offers, so they would play exactly the games `hand` plays. They are not run.
- Games: training (`island`, `not-catan`) and held out (`slime-parliament`, `ai-bubble`, `strike-the-earth`,
  `pirate-republic`), four seats each.
- Seeds: game k of a table has its own seed, made from the game's name and k, and the subject sits at seat k mod 4,
  so every seat gets exactly the same number of games and no two games share a seed. Wilson intervals assume this.
- Phases: `whole` (the subject plays the whole game), `setup` (the subject places the opening pieces, then `hand`
  plays on for it) and `play` (`hand` places the opening pieces, then the subject plays on).
- Laws: with laws (`law_every` 8) and without (0). Votes follow `vote_mode` from the policy's meta, `bot` otherwise.
"""
import argparse
import hashlib
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "env"))
sys.path.insert(0, os.path.join(HERE, ".."))

TRAIN = ["island", "not-catan"]
HELD_OUT = ["slime-parliament", "ai-bubble", "strike-the-earth", "pirate-republic"]
SEATS = 4
OPPONENTS = ["hand", "random"]
PHASES = ["whole", "setup", "play"]
NOTE_SAME = ("`fair`, `closed` and `hand` play identically when nobody makes offers, and no seat here makes "
             "offers, so only `hand` is shown. It stands for all three.")


def seed_of(game, k, laws, phase, opponent):
    """Game k's seed. The same for every subject; different for every game of a table."""
    text = f"{game}/{k}/{laws}/{phase}/{opponent}".encode()
    return int.from_bytes(hashlib.sha256(text).digest()[:6], "little")


def wilson(wins, n, z=1.96):
    """The 95% Wilson interval of a win rate."""
    if n == 0:
        return (0.0, 0.0)
    p = wins / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return (max(0.0, c - h), min(1.0, c + h))


# ---- Subjects ----------------------------------------------------------------------------------------------

class RandomPlayer:
    name = "random"

    def __init__(self, seed):
        self.rng = np.random.default_rng(seed)

    def reset(self):
        pass

    def act(self, game):
        legal = game.legal()
        return int(legal[self.rng.integers(len(legal))])


def load_subject(spec):
    """What `spec` names, as (label, maker, settings). `maker(seed)` gives a fresh player; None means `hand`."""
    if spec == "random":
        return "random", RandomPlayer, {}
    if spec == "hand":
        return "hand", None, {}
    meta_path = spec + ".json"
    if not os.path.exists(meta_path):
        meta_path = os.path.splitext(spec)[0] + ".json"
    meta = json.load(open(meta_path))
    from reference.policy import load_policy
    net = load_policy(spec, meta)
    label = meta.get("name", os.path.basename(spec))
    return label, (lambda seed: net.player(seed)), meta.get("settings", {})


# ---- Playing -----------------------------------------------------------------------------------------------

def lineup_for(phase, opponent, at):
    """The environment's lineup with the subject at seat `at`. Random opponents are callers this script plays."""
    me = {"whole": "caller", "setup": "caller+hand", "play": "hand+caller"}[phase]
    other = "hand" if opponent == "hand" else "caller"
    return [me if s == at else other for s in range(SEATS)]


def play_table(task):
    """Play one table of games: one subject, one game, one opponent, one phase, one law setting."""
    from charter import Game
    spec, game_id, opponent, phase, laws, n, vote_mode, settings = task
    label, maker, _ = load_subject(spec)
    wins, by_seat, points, rounds, refused, decisions, ended = 0, [0] * SEATS, 0.0, 0.0, 0, 0, 0
    base = {"game": game_id, "lineup": ["caller"] * SEATS, "seed": 1, "vote_mode": vote_mode,
            "law_every": 8 if laws else 0}
    for key in ("slot_order", "move_rows", "random_map", "preview"):
        if key in settings:
            base[key] = settings[key]
    g = Game(base)
    for k in range(n):
        at = k % SEATS
        seed = seed_of(game_id, k, laws, phase, opponent)
        lineup = lineup_for(phase, opponent, at)
        g.restart(lineup, seed)
        subject = maker(seed) if maker else None
        others = RandomPlayer(seed + 1)
        if subject:
            subject.reset()
        while not g.over:
            seat = g.seat
            if seat == at:
                if subject is None:
                    a = g.suggest("hand")
                    if a < 0:
                        a = 0
                else:
                    a = subject.act(g)
                decisions += 1
            else:
                a = others.act(g)
            if not g.step(a):
                refused += 1
                g.step(int(g.legal()[0]))
        info = g.info()
        ended += int(info["over"])
        if int(info["winner"]) == at:
            wins += 1
            by_seat[at] += 1
        points += info[f"points{at}"]
        rounds += info["round"]
    return {"subject": label, "game": game_id, "opponent": opponent, "phase": phase, "laws": laws, "games": n,
            "wins": wins, "wins_by_seat": by_seat, "points": points / n, "rounds": rounds / n,
            "refused": refused, "decisions": decisions, "ended": ended}


# ---- Report ------------------------------------------------------------------------------------------------

def pct(x):
    return f"{100 * x:.1f}"


def table_rows(results, games, phase, laws):
    rows = []
    for opp in OPPONENTS:
        sel = [r for r in results if r["game"] in games and r["opponent"] == opp and r["phase"] == phase
               and r["laws"] == laws]
        if not sel:
            continue
        w = sum(r["wins"] for r in sel)
        n = sum(r["games"] for r in sel)
        lo, hi = wilson(w, n)
        seat = [sum(r["wins_by_seat"][s] for r in sel) / (n / SEATS) for s in range(SEATS)]
        pts = sum(r["points"] * r["games"] for r in sel) / n
        rows.append(f"| {opp} | {n} | {pct(w / n)} | {pct(lo)} to {pct(hi)} | "
                    + " / ".join(pct(x) for x in seat) + f" | {pts:.2f} |")
    return rows


def report(subject, meta_settings, results, seconds):
    out = [f"## {subject}", "", f"Settings: {json.dumps(meta_settings) if meta_settings else 'defaults'}. "
           f"Time: {seconds:.0f} s. A fair share is 25%.", ""]
    refused = sum(r["refused"] for r in results)
    unended = sum(r["games"] - r["ended"] for r in results)
    for laws in (True, False):
        for name, games in (("training games", TRAIN), ("held-out games", HELD_OUT)):
            for phase in PHASES:
                rows = table_rows(results, games, phase, laws)
                if not rows:
                    continue
                out += [f"**{name}, {'with' if laws else 'without'} laws, phase `{phase}`**", "",
                        "| opponents | games | win % | 95% interval | win % by seat 0/1/2/3 | points |",
                        "|---|---|---|---|---|---|"] + rows + [""]
    out += [f"Refused actions: {refused}. Games that did not end: {unended}.", ""]
    for g in TRAIN + HELD_OUT:
        sel = [r for r in results if r["game"] == g and r["phase"] == "whole" and r["laws"]]
        if sel:
            w = sum(r["wins"] for r in sel)
            n = sum(r["games"] for r in sel)
            out.append(f"- {g}, whole game, with laws: {pct(w / n)}% of {n} games")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("subjects", nargs="+")
    ap.add_argument("--games", type=int, default=200, help="games per table, a multiple of 4")
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--out", default="results/eval")
    ap.add_argument("--quick", action="store_true", help="whole games with laws only")
    args = ap.parse_args()
    n = max(SEATS, args.games - args.games % SEATS)
    os.makedirs(args.out, exist_ok=True)
    text = ["# Charter eval", "", NOTE_SAME, "",
            f"Each table has {n} games, with the subject at each seat in {n // SEATS} of them. "
            "Phases: `whole`, the subject plays all of it; `setup`, the subject places the opening pieces and "
            "`hand` plays on; `play`, `hand` places them and the subject plays on.", ""]
    everything = {}
    for spec in args.subjects:
        label, _, settings = load_subject(spec)
        vote_mode = settings.get("vote_mode", "bot")
        phases = ["whole"] if args.quick else PHASES
        lawset = [True] if args.quick else [True, False]
        tasks = [(spec, g, o, p, l, n, vote_mode, settings)
                 for g in TRAIN + HELD_OUT for o in OPPONENTS for p in phases for l in lawset
                 if not (label == "hand" and p != "whole")]
        t0 = time.time()
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(play_table, tasks))
        text.append(report(label, settings, results, time.time() - t0))
        everything[label] = results
        print(f"{label}: done in {time.time() - t0:.0f} s", flush=True)
    open(os.path.join(args.out, "report.md"), "w").write("\n".join(text))
    json.dump(everything, open(os.path.join(args.out, "report.json"), "w"), indent=1)
    print("\n".join(text))


if __name__ == "__main__":
    main()
