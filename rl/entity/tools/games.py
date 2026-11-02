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
    """A readable name for action index `a` (rl/layout.json `actions`, layout 2)."""
    if a == START["end_turn"]:
        return "end_turn"
    if a == START["vote_no"]:
        return "vote_no"
    if a == START["vote_yes"]:
        return "vote_yes"
    nres = LIM["resources"]
    if a >= START["place"]:
        return f"place row {a - START['place']}"
    if a >= START["declare"]:
        i = a - START["declare"]
        return f"declare res {i // len(LEVELS)} level {LEVELS[i % len(LEVELS)]}"
    if a >= START["bank"]:
        i = a - START["bank"]
        return f"bank give {i // nres} get {i % nres}"
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
    for key in ("slot_order", "move_rows", "random_map", "preview", "declare_always"):
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
    who = lambda s: "SUBJECT" if s == at else (opponent if opponent != "random" else "random")
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


# Each game's target and round limit (Charter/Games/*.lean: targetPoints, rounds).
TARGET = {"island": (10, 24), "not-catan": (10, 30), "slime-parliament": (10, 24), "ai-bubble": (25, 10),
          "strike-the-earth": (40, 10), "pirate-republic": (18, 10)}


def count_one(task):
    spec, gid, opp, k = task
    text, won = play(spec, gid, opp, k)
    end = text.splitlines()[-4]
    pts = [float(x) for x in end.split("points [")[1].split("]")[0].split(",")]
    rnd = int(end.split("round ")[1].split(":")[0])
    target, limit = TARGET[gid]
    return gid, opp, won, won and max(pts) >= target, rnd


def count(spec, games, opps, n, jobs):
    """Wins split into target wins (the winner reached the game's target) and limit wins (the round limit ended it)."""
    from concurrent.futures import ProcessPoolExecutor
    tasks = [(spec, g, o, k) for g in games for o in opps for k in range(n)]
    with ProcessPoolExecutor(jobs) as ex:
        res = list(ex.map(count_one, tasks))
    print("| game | opponents | games | wins | target wins | limit wins | mean rounds |")
    print("|---|---|---|---|---|---|---|")
    for g in games:
        for o in opps:
            r = [x for x in res if x[0] == g and x[1] == o]
            w = sum(x[2] for x in r)
            t = sum(x[3] for x in r)
            print(f"| {g} | {o} | {len(r)} | {w} | {t} | {w - t} | {sum(x[4] for x in r) / len(r):.1f} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("subject")
    ap.add_argument("--games-list", default="island,not-catan,slime-parliament,pirate-republic")
    ap.add_argument("--opponent", default="hand")
    ap.add_argument("--n", type=int, default=2, help="games per map")
    ap.add_argument("--first", type=int, default=0, help="first game index k")
    ap.add_argument("--out", default="")
    ap.add_argument("--count", action="store_true", help="only count wins: target wins against limit wins")
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    a = ap.parse_args()
    if a.count:
        return count(a.subject, a.games_list.split(","), a.opponent.split(","), a.n, a.jobs)
    os.makedirs(a.out, exist_ok=True)
    for gid in a.games_list.split(","):
        for k in range(a.first, a.first + a.n):
            text, won = play(a.subject, gid, a.opponent, k)
            path = os.path.join(a.out, f"{gid}-{a.opponent}-{k}.txt")
            open(path, "w").write(text + "\n")
            print(path, "WON" if won else "lost", text.splitlines()[-4])


if __name__ == "__main__":
    main()
