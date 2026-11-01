"""Play a few full games and write what happened in each, so a person can read how a policy wins or loses.

    python3 rl/eval/games.py SUBJECT --out DIR [--games 8] [--opponents hand,random] [--sets train,held]

SUBJECT is what rl/eval/eval.py takes: `random`, `hand`, or a policy file with its JSON meta. Seeds are eval's own
(`seed_of`, phase `whole`, with laws), so game k here is game k of eval's table for that game and opponent.

For each game it writes `DIR/<game>-<opponent>-<k>.json` (every decision of every seat: round, seat, action, what the
action is) and adds a section to `DIR/games.md`: the result and why the game ended, the subject's moves by type,
what it built and when (with the spot's pips), its bank trades, its votes, and every seat's points round by round.

Actions are named from rl/layout.json. Piece rows are shuffled each game, so a piece is named by what the
observation says of its row: `spot piece (1 pt)`, `upgrade (2 pt)`, `attach (0 pt)`, `link piece`.
"""
import argparse
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "env"))
sys.path.insert(0, os.path.join(HERE, ".."))

import numpy as np  # noqa: E402

from eval import HELD_OUT, SEATS, TRAIN, RandomPlayer, load_subject, seed_of  # noqa: E402

L = json.load(open(os.path.join(HERE, "..", "layout.json")))
A = L["actions"]
LIM = L["limits"]
TAB = {t["name"]: t for t in L["tables"]}
LEVELS = L["declare_levels"]


def col(table, name):
    t = TAB[table]
    c = next(c for c in t["cols"] if c["name"] == name)
    return t["offset"], t["width"], c["at"]


def obs_at(obs, table, row, name):
    off, w, at = col(table, name)
    return float(obs[off + row * w + at])


def kind_label(obs, row):
    """What a piece row is, from this observation's kinds table."""
    pts = round(obs_at(obs, "kinds", row, "points") * 5)
    if obs_at(obs, "kinds", row, "on_upgrade") > 0:
        what = "upgrade"
    elif obs_at(obs, "kinds", row, "on_attach") > 0:
        what = "attach"
    elif obs_at(obs, "kinds", row, "on_link") > 0:
        what = "link piece"
    else:
        what = "spot piece"
    return f"{what} ({pts} pt)"


def describe(a, obs):
    """(type, text) for action `a`, named with the observation the deciding seat saw."""
    if a == A["end_turn"]:
        return "end_turn", "end turn"
    if a == A["vote_no"]:
        return "vote_no", "vote no"
    if a == A["vote_yes"]:
        return "vote_yes", "vote yes"
    if a < A["declare"]:
        i = a - A["bank"]
        return "bank", f"bank trade: give row {i // LIM['resources']}, get row {i % LIM['resources']}"
    if a < A["link"]:
        i = a - A["declare"]
        return "declare", f"declare row {i // len(LEVELS)} at {LEVELS[i % len(LEVELS)]}"
    if a < A["spot"]:
        i = a - A["link"]
        row, link = i // LIM["links"], i % LIM["links"]
        return "link", f"{kind_label(obs, row)} on link {link}"
    i = a - A["spot"]
    row, spot = LIM["link_kinds"] + i // LIM["spots"], i % LIM["spots"]
    pips = round(obs_at(obs, "spots", spot, "pips") * 15)
    return "spot", f"{kind_label(obs, row)} on spot {spot} ({pips} pips)"


def play(spec, maker, settings, game_id, opponent, k):
    from charter import Game
    base = {"game": game_id, "lineup": ["caller"] * SEATS, "seed": 1,
            "vote_mode": settings.get("vote_mode", "bot"), "law_every": 8}
    for key in ("slot_order", "move_rows", "random_map", "preview"):
        if key in settings:
            base[key] = settings[key]
    g = Game(base)
    at = k % SEATS
    seed = seed_of(game_id, k, True, "whole", opponent)
    other = "hand" if opponent == "hand" else ("caller" if opponent == "random" else opponent)
    lineup = ["caller" if s == at else other for s in range(SEATS)]
    g.restart(lineup, seed)
    subject = maker(seed) if maker else None
    others = RandomPlayer(seed + 1)
    if subject:
        subject.reset()
    first = g.obs().copy()
    target = round(first[col("global", "target")[0] + col("global", "target")[2]] * 50)
    limit = round((first[4] + first[5]) * 60)
    log, points_by_round, last_round = [], [], -1
    while not g.over:
        info = g.info()
        r = int(info["round"])
        if r != last_round:
            points_by_round.append((r, [int(info[f"points{s}"]) for s in range(SEATS)]))
            last_round = r
        seat = g.seat
        obs = g.obs().copy()
        voting = g.voting
        if seat == at:
            if subject is None:
                a = g.suggest("hand")
                a = a if a >= 0 else int(g.legal()[0])
            else:
                a = subject.act(g)
        else:
            a = others.act(g)
        kind, text = describe(int(a), obs)
        n_legal = int(g.mask().sum())
        ok = g.step(a)
        if not ok:
            a = int(g.legal()[0])
            g.step(a)
            kind, text = describe(a, obs)
            text += " (refused, replaced)"
        after = g.info()
        log.append({"round": r, "seat": seat, "subject": seat == at, "action": int(a), "type": kind, "text": text,
                    "legal": n_legal, "voting": voting,
                    "points": [int(after[f"points{s}"]) for s in range(SEATS)]})
    info = g.info()
    final = [int(info[f"points{s}"]) for s in range(SEATS)]
    points_by_round.append((int(info["round"]), final))
    return {"game": game_id, "opponent": opponent, "k": k, "seed": seed, "subject_seat": at, "target": target,
            "round_limit": limit, "winner": int(info["winner"]), "rounds": int(info["round"]), "final": final,
            "laws_proposed": int(info["proposed"]), "laws_passed": int(info["passed"]),
            "points_by_round": points_by_round, "log": log}


def summary(r):
    at = r["subject_seat"]
    mine = [e for e in r["log"] if e["subject"]]
    types = Counter(e["type"] for e in mine)
    won = r["winner"] == at
    top = max(r["final"])
    if top >= r["target"]:
        ended = f"a seat reached the target of {r['target']}"
    elif r["rounds"] >= r["round_limit"]:
        ended = f"the round limit ({r['round_limit']}) ran out; nobody reached {r['target']}"
    else:
        ended = "it ended early"
    tied = r["final"].count(top) > 1
    out = [f"### {r['game']} vs 3 {r['opponent']}, game {r['k']} (seed {r['seed']}), subject at seat {at}", "",
           f"- Result: {'**won**' if won else 'lost'} (winner seat {r['winner']}), points by seat {r['final']}, "
           f"{r['rounds']} rounds; {ended}{'; a tie on points, decided by the tie rule' if tied else ''}. "
           f"Laws proposed {r['laws_proposed']}, passed {r['laws_passed']}.",
           f"- Subject's decisions: {len(mine)}; by type " + ", ".join(f"{k} {v}" for k, v in types.most_common()) + ".",
           ]
    builds = [e for e in mine if e["type"] in ("spot", "link")]
    out.append("- Built: " + ("; ".join(f"r{e['round']} {e['text']}" for e in builds) or "nothing") + ".")
    trades = [e for e in mine if e["type"] == "bank"]
    if trades:
        out.append(f"- Bank trades: {len(trades)}; " + "; ".join(f"r{e['round']} {e['text'][12:]}" for e in trades[:12])
                   + (" ..." if len(trades) > 12 else "") + ".")
    votes = [e for e in mine if e["type"] in ("vote_yes", "vote_no")]
    if votes:
        out.append(f"- Votes: {sum(e['type'] == 'vote_yes' for e in votes)} yes, "
                   f"{sum(e['type'] == 'vote_no' for e in votes)} no.")
    ends = [e for e in mine if e["type"] == "end_turn"]
    early = sum(1 for e in ends if e["legal"] > 1)
    out.append(f"- Ended its turn {len(ends)} times, {early} of them with other moves legal.")
    pts = r["points_by_round"]
    step = max(1, len(pts) // 12)
    out.append("- Points by round (seat 0/1/2/3): " + ", ".join(
        f"r{rd}: {'/'.join(map(str, p))}" for rd, p in pts[::step] + ([pts[-1]] if (len(pts) - 1) % step else [])) + ".")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("subject")
    ap.add_argument("--out", required=True)
    ap.add_argument("--games", type=int, default=2, help="games per game and opponent")
    ap.add_argument("--opponents", default="hand,random")
    ap.add_argument("--sets", default="train,held")
    ap.add_argument("--start", type=int, default=0, help="first game index k")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    label, maker, settings = load_subject(args.subject)
    ids = (TRAIN if "train" in args.sets else []) + (HELD_OUT if "held" in args.sets else [])
    text = [f"# Games of {label}", ""]
    wins = n = 0
    for gid in ids:
        for opp in args.opponents.split(","):
            for k in range(args.start, args.start + args.games):
                r = play(args.subject, maker, settings, gid, opp, k)
                json.dump(r, open(os.path.join(args.out, f"{gid}-{opp}-{k}.json"), "w"))
                text.append(summary(r))
                wins += r["winner"] == r["subject_seat"]
                n += 1
                print(f"{gid} vs {opp} #{k}: winner {r['winner']} (subject {r['subject_seat']}) {r['final']}",
                      flush=True)
    text.insert(2, f"{n} games, {wins} won.\n")
    open(os.path.join(args.out, "games.md"), "w").write("\n".join(text))
    print("\n".join(text))


if __name__ == "__main__":
    main()
