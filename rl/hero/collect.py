"""Turn rl/eval reports into one CSV: one row per checkpoint, game and opponent.

    python3 rl/hero/collect.py REPORT_DIR... > rl/hero/data/eval.csv

Each REPORT_DIR is <run>/e<step>/ and holds an eval's report.json (from volume charter-rl, /hero/<run>/e<step>/).
"""
import csv
import json
import os
import re
import sys

FIELDS = ["run", "steps", "game", "opponent", "games", "wins", "target_wins", "limit_wins", "points", "best_other"]


def rows(path):
    data = json.load(open(os.path.join(path, "report.json")))
    run = os.path.basename(os.path.dirname(os.path.abspath(path)))
    steps = int(re.search(r"e(\d+)$", os.path.abspath(path)).group(1))
    for results in data.values():
        for r in results:
            if r["phase"] != "whole" or not r["laws"]:
                continue
            yield {"run": run, "steps": steps, "game": r["game"], "opponent": r["opponent"], "games": r["games"],
                   "wins": r["wins"], "target_wins": r["win_how"]["target"], "limit_wins": r["win_how"]["limit"],
                   "points": round(r["points"], 3), "best_other": round(r["best_other"], 3)}


def main():
    w = csv.DictWriter(sys.stdout, FIELDS)
    w.writeheader()
    out = [r for p in sys.argv[1:] if os.path.exists(os.path.join(p, "report.json")) for r in rows(p)]
    for r in sorted(out, key=lambda r: (r["run"], r["steps"], r["game"], r["opponent"])):
        w.writerow(r)


if __name__ == "__main__":
    main()
