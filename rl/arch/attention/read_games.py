"""Play a few full games with a policy and write what happened in each, for a person to read.

    python3 rl/arch/attention/read_games.py SUBJECT --out DIR [--games island,pirate-republic] [--opponents hand,random]
                                            [--n 2] [--laws 1]

For each game it writes one block of plain text (DIR/games.md) and one JSON record (DIR/games.json):
- who won, after how many rounds, the final points, and whether the game ran to the round limit;
- the subject's moves, counted by type, and those of the random seats (`hand` seats are played inside the
  environment, so only their points show);
- every piece the subject placed, with its round and what the piece is (points and yield read from the `kinds` row);
- the subject's bank trades (which resource row it gave and got, with each row's `worth` from the observation);
- how often the subject ended its turn while it could still place a piece;
- every seat's points at the end of each round.

Seeds and seats come from rl/eval (`seed_of`, seat k mod 4), with phase `whole`, so these are the eval's games.
Under `vote_mode = bot` the policy never votes: `hand`'s rule votes for it, so votes are counted, not judged.
"""
import argparse
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RL = os.path.join(HERE, "..", "..")
sys.path.insert(0, os.path.join(RL, "env"))
sys.path.insert(0, os.path.join(RL, "eval"))
sys.path.insert(0, RL)

from eval import SEATS, RandomPlayer, load_subject, seed_of  # noqa: E402

LAYOUT = json.load(open(os.path.join(RL, "layout.json")))
A = LAYOUT["actions"]
MAX_RES, MAX_SPOTS, MAX_LINKS = LAYOUT["limits"]["resources"], LAYOUT["limits"]["spots"], LAYOUT["limits"]["links"]
LEVELS = LAYOUT["declare_levels"]
TABLE = {t["name"]: t for t in LAYOUT["tables"]}


def col(table, name):
    for c in TABLE[table]["cols"]:
        if c["name"] == name:
            return c["at"]
    raise KeyError(name)


def row(obs, table, r):
    t = TABLE[table]
    return obs[t["offset"] + r * t["width"]: t["offset"] + (r + 1) * t["width"]]


def kind_text(obs, r):
    k = row(obs, "kinds", r)
    what = "upgrade" if k[col("kinds", "on_upgrade")] > 0.5 else "link" if k[col("kinds", "on_link")] > 0.5 else "spot"
    return f"kind row {r} ({what}, points {k[col('kinds', 'points')]:g}, yield {k[col('kinds', 'yield')]:g})"


def kind_of(a):
    """(type, detail) of action `a`, as rl/lean/CharterRL/Actions.lean decodes it."""
    if a == A["end_turn"]:
        return "end_turn", None
    if a == A["vote_no"]:
        return "vote_no", None
    if a == A["vote_yes"]:
        return "vote_yes", None
    if a < A["declare"]:
        i = a - A["bank"]
        return "bank", (i // MAX_RES, i % MAX_RES)
    if a < A["link"]:
        i = a - A["declare"]
        return "declare", (i // len(LEVELS), LEVELS[i % len(LEVELS)])
    if a < A["spot"]:
        i = a - A["link"]
        return "link", (0, i % MAX_LINKS)
    if a < 695:
        i = a - A["spot"]
        return "spot", (1 + i // MAX_SPOTS, i % MAX_SPOTS)
    return "noop", None


def play(spec, maker, game_id, opponent, k, laws, settings):
    from charter import Game
    cfg = {"game": game_id, "lineup": ["caller"] * SEATS, "seed": 1, "vote_mode": settings.get("vote_mode", "bot"),
           "law_every": 8 if laws else 0}
    for key in ("slot_order", "move_rows", "random_map", "preview"):
        if key in settings:
            cfg[key] = settings[key]
    g = Game(cfg)
    at = k % SEATS
    seed = seed_of(game_id, k, laws, "whole", opponent)
    lineup = ["caller" if s == at else ("caller" if opponent == "random" else opponent) for s in range(SEATS)]
    g.restart(lineup, seed)
    subject = maker(seed) if maker else None
    others = RandomPlayer(seed + 1)
    if subject:
        subject.reset()
    moves, other_moves = {}, {}
    builds, trades, declares = [], [], []
    end_with_build, turns_ended, decisions = 0, 0, 0
    points, last_round = [], -1
    refused = 0
    g_round = col("global", "round")
    while not g.over:
        info = g.info()
        r = int(info["round"])
        if r != last_round:
            points.append([r] + [int(info[f"points{s}"]) for s in range(SEATS)])
            last_round = r
        seat = g.seat
        obs = g.obs().copy()
        legal = g.legal()
        if seat == at:
            a = (g.suggest("hand") if subject is None else subject.act(g))
            a = a if a >= 0 else 0
            decisions += 1
            t, d = kind_of(a)
            moves[t] = moves.get(t, 0) + 1
            if t == "end_turn":
                turns_ended += 1
                if any(kind_of(int(x))[0] in ("spot", "link") for x in legal):
                    end_with_build += 1
            elif t in ("spot", "link"):
                builds.append({"round": r, "what": kind_text(obs, d[0]), "where": f"{t} {d[1]}"})
            elif t == "bank":
                give, get = row(obs, "resources", d[0]), row(obs, "resources", d[1])
                trades.append({"round": r, "give_row": d[0], "get_row": d[1],
                               "give_worth": float(give[col("resources", "worth")]),
                               "get_worth": float(get[col("resources", "worth")]),
                               "give_stock": float(give[col("resources", "stock")])})
            elif t == "declare":
                declares.append({"round": r, "row": d[0], "level": d[1]})
        else:
            a = others.act(g)
            t, _ = kind_of(a)
            other_moves[t] = other_moves.get(t, 0) + 1
        if not g.step(a):
            refused += 1
            g.step(int(g.legal()[0]))
    info = g.info()
    obs = g.obs()
    final = [int(info[f"points{s}"]) for s in range(SEATS)]
    points.append(["end"] + final)
    rounds_left = None
    try:
        rounds_left = float(obs[TABLE["global"]["offset"] + col("global", "rounds_left")])
    except Exception:  # noqa: BLE001
        pass
    return {"game": game_id, "opponent": opponent, "laws": laws, "k": k, "seed": seed, "subject_seat": at,
            "winner": int(info["winner"]), "won": int(info["winner"]) == at, "rounds": int(info["round"]),
            "final_points": final, "rounds_left_at_end": rounds_left, "laws_proposed": int(info["proposed"]),
            "laws_passed": int(info["passed"]), "decisions": decisions, "refused": refused,
            "moves": moves, "other_moves": other_moves, "builds": builds, "bank_trades": trades,
            "declares": declares, "turns_ended": turns_ended, "ended_with_build_on_offer": end_with_build,
            "points_by_round": points}


def text_of(rec):
    me = rec["subject_seat"]
    out = [f"### {rec['game']} vs 3 {rec['opponent']}, game {rec['k']}, laws {'on' if rec['laws'] else 'off'}, "
           f"subject at seat {me}",
           f"- winner: seat {rec['winner']}{' (the subject)' if rec['won'] else ''}, after {rec['rounds']} rounds; "
           f"final points {rec['final_points']}; rounds left at the end: {rec['rounds_left_at_end']}",
           f"- laws proposed {rec['laws_proposed']}, passed {rec['laws_passed']}",
           f"- subject's moves: {dict(sorted(rec['moves'].items()))} over {rec['decisions']} decisions; refused {rec['refused']}",
           f"- turns ended with a piece still placeable: {rec['ended_with_build_on_offer']} of {rec['turns_ended']}"]
    if rec["other_moves"]:
        out.append(f"- random seats' moves: {dict(sorted(rec['other_moves'].items()))}")
    out.append("- built: " + ("; ".join(f"r{b['round']} {b['what']} at {b['where']}" for b in rec["builds"]) or "nothing"))
    if rec["bank_trades"]:
        out.append("- bank trades: " + "; ".join(
            f"r{t['round']} row {t['give_row']} (worth {t['give_worth']:g}, stock {t['give_stock']:g}) -> row "
            f"{t['get_row']} (worth {t['get_worth']:g})" for t in rec["bank_trades"]))
    if rec["declares"]:
        out.append("- declarations: " + "; ".join(f"r{d['round']} row {d['row']} level {d['level']}" for d in rec["declares"]))
    pts = rec["points_by_round"]
    step = max(1, len(pts) // 12)
    out.append("- points by round (round: seat 0..3): " + ", ".join(
        f"{p[0]}: {p[1:]}" for i, p in enumerate(pts) if i % step == 0 or i == len(pts) - 1))
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("subject")
    ap.add_argument("--out", required=True)
    ap.add_argument("--games", default="island,not-catan,slime-parliament,ai-bubble,strike-the-earth,pirate-republic")
    ap.add_argument("--opponents", default="hand,random")
    ap.add_argument("--n", type=int, default=2, help="games per game and opponent; game k puts the subject at seat k mod 4")
    ap.add_argument("--laws", type=int, default=1)
    a = ap.parse_args()
    label, maker, settings = load_subject(a.subject)
    recs = []
    for game_id in a.games.split(","):
        for opp in a.opponents.split(","):
            for k in range(a.n):
                recs.append(play(a.subject, maker, game_id, opp, k, bool(a.laws), settings))
    os.makedirs(a.out, exist_ok=True)
    json.dump(recs, open(os.path.join(a.out, "games.json"), "w"), indent=1)
    wins = sum(r["won"] for r in recs)
    head = [f"# Games of {label}", "", f"{len(recs)} games, the subject won {wins}.", ""]
    open(os.path.join(a.out, "games.md"), "w").write("\n".join(head) + "\n".join(text_of(r) for r in recs))
    print("\n".join(head) + "\n".join(text_of(r) for r in recs))


if __name__ == "__main__":
    main()
