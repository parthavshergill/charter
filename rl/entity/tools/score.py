"""Summarise rl/eval report.json files the way rl/ROUND4.md judges them.

    python3 rl/entity/tools/score.py REPORT.json [REPORT2.json ...] [--opponent table]

For each subject, whole game, without laws, against the opponent:
- nine: the mean win % over main's nine worlds (each world weighs the same);
- clean: the same, counting only wins in games where the subject declared nothing. The table bot never declares,
  so a win with a declaration may be an uncontested one (ROUND4: do not count those). It is a lower bound;
- held out (7 worlds), without Pirate Republic (6), limit wins as a share of all wins, declarations per game;
- each world: win % (clean win %).
"""
import argparse
import json

TRAIN = ("main-island", "main-not-catan")
ORDER = ("main-island", "main-not-catan", "main-slime-parliament", "main-ai-bubble", "main-strike-the-earth",
         "main-pirate-republic", "main-the-pit", "main-omerta", "main-hill-and-chill")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("reports", nargs="+")
    ap.add_argument("--opponent", default="table")
    a = ap.parse_args()
    for path in a.reports:
        for subject, rows in json.load(open(path)).items():
            rows = [r for r in rows if r["opponent"] == a.opponent and r["phase"] == "whole" and not r["laws"]]
            by = {r["game"]: r for r in rows}
            if not all(w in by for w in ORDER):
                print(f"{subject}: not all nine worlds in {path}")
                continue
            pct = {w: 100 * by[w]["wins"] / by[w]["games"] for w in ORDER}
            clean = {w: 100 * by[w].get("wins_no_declare", float("nan")) / by[w]["games"] for w in ORDER}
            mean = lambda d, ws: sum(d[w] for w in ws) / len(ws)
            held = [w for w in ORDER if w not in TRAIN]
            nop = [w for w in held if w != "main-pirate-republic"]
            wins = sum(by[w]["wins"] for w in ORDER)
            limit = sum(by[w]["win_how"]["limit"] for w in ORDER)
            games = sum(by[w]["games"] for w in ORDER)
            decl = sum(by[w].get("declares", 0) for w in ORDER) / games
            most = max(by[w].get("most_declares_in_turn", 0) for w in ORDER)
            print(f"{subject}\n  nine {mean(pct, ORDER):.1f} | clean {mean(clean, ORDER):.1f} | held {mean(pct, held):.1f} "
                  f"| noPirate {mean(pct, nop):.1f} | limit wins {100 * limit / max(wins, 1):.0f}% of wins "
                  f"| declarations {decl:.2f} a game, most {most} in a turn | {by[ORDER[0]]['games']} games a world")
            print("  " + " | ".join(f"{w[5:]} {pct[w]:.1f} ({clean[w]:.1f})" for w in ORDER))


if __name__ == "__main__":
    main()
