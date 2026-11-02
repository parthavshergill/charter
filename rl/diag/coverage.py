"""Which observation columns vary on which worlds: a column that never changes in training never gets a gradient.

    python3 rl/diag/coverage.py [--games 40] [--sets train=island,not-catan pack=pack-train main=main-the-pit,...]

Plays games through the real interface (rl/env/charter.py): random legal actions for the callers, three `table` bots
in half the games, with laws (law_every 8), dealt maps. Over the real rows of every table it records each column's
smallest and largest value. It prints:
- the columns that never vary on the first set (by default Island and Not Catan) but vary on some other set, and
  whether each other set makes them vary;
- whether some column varies on another set but never on the second set (by default the training pack);
- for each set, how many columns never vary there.
A column is a run of `layout.json`'s columns (for example `resources.holding` covers all its seat columns).
"""
import argparse
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "env"))
from charter import Game  # noqa: E402

LAYOUT = json.load(open(os.path.join(HERE, "..", "layout.json")))
MAIN_HELD = ["main-slime-parliament", "main-ai-bubble", "main-strike-the-earth", "main-pirate-republic", "main-the-pit",
             "main-omerta", "main-hill-and-chill"]
DEFAULT = {"train": ["main-island", "main-not-catan"], "pack": ["pack-train"], "main-held-out": MAIN_HELD}


def ranges(worlds, games, seed=0):
    """{(table, column): (min, max)} over every decision of these games."""
    lo, hi = {}, {}
    rng = np.random.default_rng(seed)
    for w in worlds:
        g = Game({"game": w, "lineup": ["caller"] * 4, "seed": 1, "vote_mode": "policy", "law_every": 8,
                  "declare_always": False})
        for k in range(games):
            lineup = ["caller"] * 4 if k % 2 == 0 else ["caller", "table", "table", "table"]
            g.restart(lineup, 40000 + 97 * k + seed)
            while not g.over:
                obs = g.obs()
                for t in LAYOUT["tables"]:
                    if t["name"] == "moves":
                        continue
                    x = obs[t["offset"]:t["offset"] + t["rows"] * t["width"]].reshape(t["rows"], t["width"])
                    real = x[:, 0] > 0.5
                    if not real.any():
                        continue
                    for c in t["cols"]:
                        v = x[real, c["at"]:c["at"] + c["width"]]
                        key = (t["name"], c["name"])
                        lo[key] = min(lo.get(key, np.inf), float(v.min()))
                        hi[key] = max(hi.get(key, -np.inf), float(v.max()))
                legal = g.legal()
                g.step(int(legal[rng.integers(len(legal))]))
    return {k: (lo[k], hi[k]) for k in lo}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--games", type=int, default=40, help="games per world")
    ap.add_argument("--sets", nargs="*", default=None, help="name=world,world ... (the first is the one checked)")
    args = ap.parse_args()
    sets = DEFAULT if not args.sets else dict(s.split("=", 1) for s in args.sets)
    sets = {k: (v.split(",") if isinstance(v, str) else v) for k, v in sets.items()}
    R = {name: ranges(ws, args.games) for name, ws in sets.items()}
    names = list(sets)
    first = names[0]
    keys = sorted(set().union(*[set(r) for r in R.values()]))
    varies = {n: {k for k in keys if k in R[n] and R[n][k][0] != R[n][k][1]} for n in names}
    print(f"Columns that never vary on `{first}` ({', '.join(sets[first])}) but vary elsewhere:\n")
    print("| table.column | " + " | ".join(f"varies on {n}" for n in names[1:]) + " |")
    print("|---|" + "---|" * (len(names) - 1))
    n = 0
    for k in keys:
        if k in varies[first]:
            continue
        if any(k in varies[o] for o in names[1:]):
            n += 1
            print(f"| {k[0]}.{k[1]} | " + " | ".join("yes" if k in varies[o] else "**no**" for o in names[1:]) + " |")
    print(f"\n{n} such columns.\n")
    if len(names) > 2:
        second = names[1]
        others = set().union(*[varies[o] for o in names if o != second])
        missing = sorted(f"{a}.{b}" for a, b in others - varies[second])
        print(f"Columns that vary on another set but never on `{second}`: {', '.join(missing) or 'none'}\n")
    for nm in names:
        never = [f"{a}.{b}" for a, b in keys if (a, b) not in varies[nm]]
        print(f"`{nm}`: {len(keys) - len(never)} of {len(keys)} columns vary; never: {', '.join(never) or 'none'}")


if __name__ == "__main__":
    main()
