"""Play a few full games and write what happened, for reading by a person.

    python3 rl/entity/tools/games.py SUBJECT --games-list island,slime-parliament --opponent hand --n 2 --out DIR

SUBJECT is `random`, `hand`, or a policy file with its `.json` meta, as in rl/eval. For each game it writes
DIR/<game>-<opponent>-<k>.txt: the seats, every action in order (round, seat, action), the points after each round,
counts of actions by type and seat, and the result. Same seeds and seats as rl/eval (game k: subject at seat k mod 4).
"""
import argparse
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
RL = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path[:0] = [RL, os.path.join(RL, "env"), os.path.join(RL, "eval")]

import eval as ev  # noqa: E402  rl/eval/eval.py

LAYOUT = json.load(open(os.path.join(RL, "layout.json")))
START = LAYOUT["actions"]
LIM = LAYOUT["limits"]
LEVELS = LAYOUT["declare_levels"]


def name(a):
    """A readable name for action index `a` (rl/layout.json `actions`)."""
    if a == START["end_turn"]:
        return "end_turn"
    if a == START["vote_no"]:
        return "vote_no"
    if a == START["vote_yes"]:
        return "vote_yes"
    if a >= START["spot"]:
        i = a - START["spot"]
        return f"spot {i % LIM['spots']} kind {i // LIM['spots']}"
    if a >= START["link"]:
        i = a - START["link"]
        return f"link {i % LIM['links']}" + (f" kind {i // LIM['links']}" if i >= LIM["links"] else "")
    if a >= START["declare"]:
        i = a - START["declare"]
        return f"declare res {i // len(LEVELS)} level {LEVELS[i % len(LEVELS)]}"
    if a >= START["bank"]:
        i = a - START["bank"]
        return f"bank give {i // LIM['resources']} get {i % LIM['resources']}"
    return f"noop {a}"


def kind(a):
    return name(a).split()[0]


def play(spec, game_id, opponent, k, laws=True):
    from charter import Game
    label, maker, settings = ev.load_subject(spec)
    at = k % ev.SEATS
    seed = ev.seed_of(game_id, k, laws, "whole", opponent)
    base = {"game": game_id, "lineup": ["caller"] * ev.SEATS, "seed": 1, "vote_mode": "bot",
            "law_every": 8 if laws else 0}
    for key in ("slot_order", "move_rows", "random_map", "preview"):
        if key in settings:
            base[key] = settings[key]
    g = Game(base)
    lineup = ev.lineup_for("whole", opponent, at)
    g.restart(lineup, seed)
    subject = maker(seed) if maker else None
    others = ev.RandomPlayer(seed + 1)
    if subject:
        subject.reset()
    lines, counts, last_round = [], Counter(), -1
    who = lambda s: "SUBJECT" if s == at else (opponent if opponent == "hand" else "random")
    lines.append(f"# {label} at seat {at} on {game_id}, against 3 {opponent}, seed {seed}, laws {'on' if laws else 'off'}")
    while not g.over:
        info = g.info()
        r = int(info["round"])
        if r != last_round:
            pts = [info.get(f"points{s}", 0) for s in range(ev.SEATS)]
            lines.append(f"-- round {r}: points {pts}")
            last_round = r
        seat = g.seat
        if seat == at:
            if subject is None:
                a = g.suggest("hand")
                a = 0 if a < 0 else a
            else:
                a = subject.act(g)
            nlegal = len(g.legal())
        else:
            a, nlegal = others.act(g), len(g.legal())
        ok = g.step(a)
        counts[(seat == at, kind(a))] += 1
        mark = "" if ok else "  REFUSED"
        if seat == at or kind(a) not in ("end_turn",):
            lines.append(f"r{r} s{seat} {who(seat):7s} {name(a)}  (of {nlegal} legal){mark}")
        if not ok:
            g.step(int(g.legal()[0]))
    info = g.info()
    pts = [info.get(f"points{s}", 0) for s in range(ev.SEATS)]
    lines.append(f"-- end, round {int(info['round'])}: points {pts}, winner seat {int(info['winner'])}"
                 f" ({'SUBJECT' if int(info['winner']) == at else 'other'})")
    lines.append("subject's actions by type: " + ", ".join(f"{k}={v}" for (me, k), v in sorted(counts.items()) if me))
    lines.append("others' actions by type: " + ", ".join(f"{k}={v}" for (me, k), v in sorted(counts.items()) if not me))
    lines.append("info: " + json.dumps({k: round(v, 3) for k, v in info.items()}))
    return "\n".join(lines), int(info["winner"]) == at


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("subject")
    ap.add_argument("--games-list", default="island,not-catan,slime-parliament,pirate-republic")
    ap.add_argument("--opponent", default="hand")
    ap.add_argument("--n", type=int, default=2, help="games per map")
    ap.add_argument("--first", type=int, default=0, help="first game index k")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    for gid in a.games_list.split(","):
        for k in range(a.first, a.first + a.n):
            text, won = play(a.subject, gid, a.opponent, k)
            path = os.path.join(a.out, f"{gid}-{a.opponent}-{k}.txt")
            open(path, "w").write(text + "\n")
            print(path, "WON" if won else "lost", text.splitlines()[-4])


if __name__ == "__main__":
    main()
