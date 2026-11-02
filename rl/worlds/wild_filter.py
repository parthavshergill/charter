"""The honesty filter for `pack-wild`: play each wild world, reject the dishonest ones, and write CharterRL.WildOk.

    python3 rl/worlds/wild_filter.py run --set train --start 0 --count 1000 --jobs 4 --out part.jsonl
    python3 rl/worlds/wild_filter.py write part1.jsonl part2.jsonl ...  # write rl/lean/CharterRL/WildOk.lean
    python3 rl/worlds/wild_filter.py summary part1.jsonl ...            # rejection rates by style and reason
    python3 rl/worlds/wild_filter.py check                              # fail if WildOk is for another generator

Each world is played at 4 seats (or the nearest count it allows), with the training settings: bot votes, a law put to
a vote 1 turn in 8, 1 vote in 3 a repeal (`repeal_every = 3`), dealt maps. Two kinds of game, 8 of each, with the
tested seat moving round the table:
- `idle` against `table`: `idle` places its setup pieces as `table` does, then never builds, trades or declares.
- a random seat against `table`: it picks among its legal actions at random.

A world is rejected for each of these reasons:
- `idle`: the idle seat won a game. Doing nothing after setup must not win, so setup and luck do not decide it.
- `random`: the random seat won 2 or more of 8, at least the share of one `table` seat (the 3 share the rest).
- `setup`: a game ended before round 3.
- `no-winner`: more than half of the games had no winner.
- `layout`: a decision had more legal placements than the layout's 128 rows of `places`.
- `long`: a game took more than 6000 events, too slow for training.
A world the generator could not make at all is not in the set: its seed is skipped, as in the pack.
"""
import argparse
import collections
import hashlib
import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "env"))
WILD = os.path.join(HERE, "..", "lean", "CharterRL", "Wild.lean")
OUT = os.path.join(HERE, "..", "lean", "CharterRL", "WildOk.lean")
SIZES = {"train": 65536, "val": 8192}
STYLES = ["economy", "laws", "island", "not-catan"]
GAMES = 8
SETTINGS = {"vote_mode": "bot", "law_every": 8, "repeal_every": 3, "random_map": True}


MARK = b"/-! ## Dealing and describing"


def generator_hash():
    """The SHA-256 of Wild.lean up to its dealing section: the part that decides what each world is."""
    text = open(WILD, "rb").read()
    return hashlib.sha256(text[:text.index(MARK)]).hexdigest()


def world_id(set_, n):
    return f"pack-wild-{n}" if set_ == "train" else f"pack-wild-val-{n}"


def judge(set_, n):
    """One world's verdict: its numbers and the reasons it was rejected (none if accepted)."""
    from charter import Game
    wid = world_id(set_, n)
    rng = np.random.default_rng(1000003 * (1 if set_ == "train" else 2) + n)
    out = {"set": set_, "n": n, "style": STYLES[n % 4]}
    game = None
    for seats in (4, 3, 5, 2, 6):
        try:
            game = Game(dict(SETTINGS, game=wid, lineup=["table"] * seats, seed=1))
            break
        except Exception as e:  # noqa: BLE001 (a seat count the world does not allow)
            err = str(e)
    if game is None:
        out.update(reasons=["unplayable"], error=err[:200])
        return out
    out["seats"] = seats
    wins = collections.Counter()
    early = no_winner = over = long_ = 0
    rounds, target_wins, proposed, passed, lapsed = [], 0, [], [], []
    for kind in ("idle", "random"):
        for k in range(GAMES):
            at = k % seats
            lineup = ["table"] * seats
            lineup[at] = "idle" if kind == "idle" else "caller"
            game.restart(lineup, 7000 + 31 * k + (0 if kind == "idle" else 500))
            while not game.over:
                legal = game.legal()
                game.step(int(legal[rng.integers(len(legal))]))
            i = game.info()
            w = int(i["winner"])
            if w == at:
                wins[kind] += 1
            if w < 0:
                no_winner += 1
            elif i[f"points{w}"] >= i["target"]:
                target_wins += 1
            if i["round"] < 3:
                early += 1
            over += int(i["place_over"] > 0)
            long_ += int(i["events"] > 6000)
            rounds.append(i["round"])
            proposed.append(i["proposed"])
            passed.append(i["passed"])
            lapsed.append(i["lapsed"])
    reasons = []
    if wins["idle"] >= 1:
        reasons.append("idle")
    if wins["random"] >= 2:
        reasons.append("random")
    if early:
        reasons.append("setup")
    if no_winner > GAMES:
        reasons.append("no-winner")
    if over:
        reasons.append("layout")
    if long_:
        reasons.append("long")
    out.update(reasons=reasons, idle_wins=wins["idle"], random_wins=wins["random"], round=float(np.mean(rounds)),
               round_limit=i["round_limit"], target=i["target"], target_wins=target_wins,
               proposed=float(np.mean(proposed)), passed=float(np.mean(passed)), lapsed=float(np.mean(lapsed)))
    return out


def _judge(args):
    return judge(*args)


def run(args):
    todo = [(args.set, n) for n in range(args.start, min(args.start + args.count, SIZES[args.set]))]
    with open(args.out, "w") as f, ProcessPoolExecutor(args.jobs) as pool:
        for v in pool.map(_judge, todo, chunksize=8):
            f.write(json.dumps(v) + "\n")
            f.flush()


def load(paths):
    rows = {}
    for p in paths:
        for line in open(p):
            if line.strip():
                v = json.loads(line)
                rows[(v["set"], v["n"])] = v
    return rows


def hex_of(rows, set_):
    bits = [0] * SIZES[set_]
    for (s, n), v in rows.items():
        if s == set_ and not v["reasons"]:
            bits[n] = 1
    digits = []
    for i in range(0, len(bits), 4):
        digits.append("%x" % (bits[i] | bits[i + 1] << 1 | bits[i + 2] << 2 | bits[i + 3] << 3))
    return "".join(digits)


def write(args):
    rows = load(args.files)
    for s in SIZES:
        have = sum(1 for k in rows if k[0] == s)
        if have != SIZES[s]:
            sys.exit(f"{s}: {have} of {SIZES[s]} worlds judged; judge them all before writing")
    text = open(OUT).read()
    head = text[:text.index("def generator")]
    tail = text[text.index("private def digits"):]
    body = (f'def generator : String := "{generator_hash()}"\n\n'
            f'def trainHex : String := "{hex_of(rows, "train")}"\n\n'
            f'def valHex : String := "{hex_of(rows, "val")}"\n\n')
    open(OUT, "w").write(head + body + tail)
    print(f"wrote {os.path.relpath(OUT)}")


def summary(args):
    rows = load(args.files)
    print("| set | style | worlds | accepted | idle | random | setup | no winner | layout | long | unplayable |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for s in SIZES:
        for st in STYLES + ["all"]:
            vs = [v for (k, _), v in rows.items() if k == s and (st == "all" or v["style"] == st)]
            if not vs:
                continue
            c = collections.Counter(r for v in vs for r in v["reasons"])
            ok = sum(1 for v in vs if not v["reasons"])
            print(f"| {s} | {st} | {len(vs)} | {ok} ({100 * ok / len(vs):.0f}%) | " +
                  " | ".join(f"{100 * c[r] / len(vs):.1f}%" for r in
                             ["idle", "random", "setup", "no-winner", "layout", "long", "unplayable"]) + " |")
    acc = [v for v in rows.values() if not v["reasons"]]
    if acc:
        print("\nAccepted worlds, mean per game: " + ", ".join(
            f"{k} {np.mean([v[k] for v in acc]):.1f}" for k in
            ["round", "round_limit", "target", "proposed", "passed", "lapsed"]) +
            f"; games ended at the target {np.mean([v['target_wins'] for v in acc]) / (2 * GAMES):.0%}")


def check(_args):
    text = open(OUT).read()
    have = text.split('def generator : String := "', 1)[1].split('"', 1)[0]
    if have != generator_hash():
        print(f"WildOk.lean is for another Wild.lean ({have[:12] or 'none'}, now {generator_hash()[:12]}): "
              "run the filter again")
        sys.exit(1)
    print("WildOk.lean is up to date")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--set", choices=list(SIZES), default="train")
    r.add_argument("--start", type=int, default=0)
    r.add_argument("--count", type=int, default=100)
    r.add_argument("--jobs", type=int, default=os.cpu_count())
    r.add_argument("--out", required=True)
    for name in ("write", "summary"):
        p = sub.add_parser(name)
        p.add_argument("files", nargs="+")
    sub.add_parser("check")
    args = ap.parse_args()
    {"run": run, "write": write, "summary": summary, "check": check}[args.cmd](args)


if __name__ == "__main__":
    main()
