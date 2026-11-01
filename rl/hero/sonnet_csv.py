"""Sum the Sonnet games listed in data/sonnet_games.txt into data/sonnet.csv.

    python3 rl/hero/sonnet_csv.py

Each game's record is games/<CODE>.json, written by seat.py when the game ends. A row per arm and checkpoint: games
finished, wins by the policy, wins at the target, and games still running.
"""
import csv
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
STEPS = {"c4-99M": 99287040, "v2fix-0": 0, "v2fix-44.2M": 44236800, "v2fix-60.0M": 59965440, "v2fix-29.5M": 29491200}


def main():
    rows = {}
    for line in open(os.path.join(HERE, "data", "sonnet_games.txt")):
        if not line.strip() or line.startswith("#"):
            continue
        code, arm = line.split()[:2]
        path = os.path.join(HERE, "games", f"{code}.json")
        if not os.path.exists(path):
            print(f"{code}: not finished")
            continue
        d = json.load(open(path))
        res, st = d["result"], d["settings"]
        key = (arm, st["world"], STEPS[st["weights_label"]])
        r = rows.setdefault(key, {"arm": arm, "world": st["world"], "steps": key[2], "games": 0, "wins": 0,
                                  "target_wins": 0, "codes": []})
        r["games"] += 1
        r["wins"] += int(res["policy_won"])
        r["target_wins"] += int(res["policy_won"] and res["how"] == "target reached")
        r["codes"].append(code)
        print(f"{code} {arm} {st['weights_label']} policy seat {res['policy_seat']}: winner {res['winner']} "
              f"({res['how']}), round {res['round']}, points {res['points']}")
    with open(os.path.join(HERE, "data", "sonnet.csv"), "w") as f:
        w = csv.DictWriter(f, ["arm", "world", "steps", "games", "wins", "target_wins", "codes"])
        w.writeheader()
        for r in rows.values():
            w.writerow(dict(r, codes=" ".join(r["codes"])))


if __name__ == "__main__":
    main()
