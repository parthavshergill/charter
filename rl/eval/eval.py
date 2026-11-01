"""One command, one report: how well a policy plays Charter against fixed opponents.

    python3 rl/eval/eval.py SUBJECT [SUBJECT ...] [--games N] [--out DIR] [--jobs J] [--opponents a,b] [--logs K]

A SUBJECT is `random` (a random legal action), `hand` (the hand bot), `champion` or `champion-closed` (the earlier
evolution run's best strategy, played by the environment, with and without offers), or a policy file: a PufferLib
`.bin` checkpoint or an `.npz`, each with a JSON `meta` next to it (`<file>.json`). rl/README.md gives the format.

Everything is fixed, so two runs and two subjects see the same games:
- Opponents: three `hand` bots, three random players, and three `champion` bots. `fair` and `closed` differ from
  `hand` only in accepting offers, and `hand` makes none, so they would play exactly the games `hand` plays. They are
  not run. `champion` makes offers and accepts them, among its own seats: the policy has no action for offers.
  `--opponents` picks others, for example `champion-closed`, which makes and accepts none.
- Games: training (`island`, `not-catan`) and held out (`slime-parliament`, `ai-bubble`, `strike-the-earth`,
  `pirate-republic`), four seats each.
- Seeds: game k of a table has its own seed, made from the game's name and k, and the subject sits at seat k mod 4,
  so every seat gets exactly the same number of games and no two games share a seed. Wilson intervals assume this.
- Phases: `whole` (the subject plays the whole game), `setup` (the subject places the opening pieces, then `hand`
  plays on for it) and `play` (`hand` places the opening pieces, then the subject plays on).
- Laws: with laws (`law_every` 8) and without (0). Votes follow `vote_mode` from the policy's meta, `bot` otherwise.

Can it play (`--can-play`, on by default): a separate check from how well it plays. The subject plays made-up
games that pass `G.Valid` (rl/lean/CharterRL/Gen.lean: at the engine's limits, tiny, and odd sizes) at every seat
count from 2 to 6, at every seat, against random players. It reports games that did not end, refused actions and
errors. It says nothing about strength.

Saved games (`--logs K`, default 2): the first K games of every table are kept in `OUT/games/`, each as
`<code>.jsonl`, the server's event log, which `charter-rl-logs OUT/games` turns into `<code>.db` for
`make spectate RESULTS=OUT/games`, and as `<code>.md`, a short summary: moves by type, what was built and when,
trades, votes, and points by round. `OUT/games/index.md` lists them. This script runs `charter-rl-logs` when it can
find it.
"""
import argparse
import hashlib
import json
import math
import os
import subprocess
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
OPPONENTS = ["hand", "random", "champion"]
# Step a policy's recurrent state on a zero observation each time another caller seat decides, as training does
# (every agent's row goes through the network on every tick; a waiting agent sees zeros). Bots inside the environment
# take no ticks, in training or here. `--wait-steps 0` turns it off.
WAIT_STEPS = [1]
BOTS = ["hand", "champion", "champion-closed"]   # subjects and opponents the environment plays itself
PHASES = ["whole", "setup", "play"]
NOTE_WEAK = ("`hand` is a weak opponent on some held-out games: in the builder's run, random players beat three `hand` "
             "bots in 69% of Pirate Republic games and matched them on Strike the Earth. Read held-out results by game.")
NOTE_SAME = ("`fair`, `closed` and `hand` play identically when nobody makes offers, and `hand` makes none, "
             "so only `hand` is shown. It stands for all three. `champion` makes and accepts offers among its own "
             "seats; the subject cannot make or accept one.")


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
    if spec in BOTS:
        return spec, None, {}
    meta_path = spec + ".json"
    if not os.path.exists(meta_path):
        meta_path = os.path.splitext(spec)[0] + ".json"
    meta = json.load(open(meta_path))
    from reference.policy import load_policy
    net = load_policy(spec, meta)
    label = meta.get("name", os.path.basename(spec))
    return label, (lambda seed: net.player(seed)), meta.get("settings", {})


# ---- Playing -----------------------------------------------------------------------------------------------

def lineup_for(phase, opponent, at, bot=None):
    """The environment's lineup with the subject at seat `at`. Random opponents are callers this script plays.
    `bot` names a subject the environment plays itself; `hand` stays a caller that plays the hand bot's suggestion, as
    before, so its rows compare with earlier reports."""
    me = bot if bot and bot != "hand" else "caller"
    me = {"whole": me, "setup": f"{me}+hand", "play": f"hand+{me}"}[phase]
    other = "caller" if opponent == "random" else opponent
    return [me if s == at else other for s in range(SEATS)]


def table_code(game_id, opponent, phase, laws, k):
    """A table code for a saved game: letters only, fixed by the table and k."""
    h = hashlib.sha256(f"{game_id}/{opponent}/{phase}/{laws}/{k}".encode()).digest()
    letters = "ABCDEFGHJKMNPQRSTUVWXYZ"
    return "".join(letters[b % len(letters)] for b in h[:6])


def how_won(info, winner):
    """How the game was won: `target` if the winner reached the target, `limit` if the round limit ended it, `law`
    if a law ended it, `other` if none of these (for example a stuck game)."""
    if winner < 0:
        return "none"
    if info[f"points{winner}"] >= info["target"]:
        return "target"
    if info["round"] >= info["round_limit"]:
        return "limit"
    if info["law_ends"]:
        return "law"
    return "other"


def play_table(task):
    """Play one table of games: one subject, one game, one opponent, one phase, one law setting."""
    from charter import Game
    spec, game_id, opponent, phase, laws, n, vote_mode, settings, logs, log_dir = task
    label, maker, _ = load_subject(spec)
    bot = spec if spec in BOTS else None
    wins, by_seat, points, rounds, refused, decisions, ended = 0, [0] * SEATS, 0.0, 0.0, 0, 0, 0
    win_how = {"target": 0, "limit": 0, "law": 0, "other": 0}
    games_how = {"target": 0, "limit": 0, "law": 0, "other": 0, "none": 0}
    best_other = 0.0
    base = {"game": game_id, "lineup": ["caller"] * SEATS, "seed": 1, "vote_mode": vote_mode,
            "law_every": 8 if laws else 0}
    for key in ("slot_order", "move_rows", "random_map", "preview", "declare_always"):
        if key in settings:
            base[key] = settings[key]
    plain = Game(base)
    recorded = Game(dict(base, record=True)) if logs else None
    saved = []
    for k in range(n):
        at = k % SEATS
        seed = seed_of(game_id, k, laws, phase, opponent)
        lineup = lineup_for(phase, opponent, at, bot)
        g = recorded if k < logs else plain
        g.restart(lineup, seed)
        subject = maker(seed) if maker else None
        others = RandomPlayer(seed + 1)
        if subject:
            subject.reset()
            subject.stale_wait = bool(settings.get("stale_wait"))
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
                if subject is not None and WAIT_STEPS[0] and hasattr(subject, "wait"):
                    subject.wait(g.obs_size)
            if not g.step(a):
                refused += 1
                g.step(int(g.legal()[0]))
        info = g.info()
        if k < logs:
            saved.append(save_game(g, log_dir, label, game_id, opponent, phase, laws, k, at, seed, lineup, info))
        ended += int(info["over"])
        how = how_won(info, int(info["winner"]))
        games_how[how] += 1
        if int(info["winner"]) == at:
            wins += 1
            by_seat[at] += 1
            win_how[how] += 1
        points += info[f"points{at}"]
        best_other += max(info[f"points{s}"] for s in range(SEATS) if s != at)
        rounds += info["round"]
    return {"subject": label, "game": game_id, "opponent": opponent, "phase": phase, "laws": laws, "games": n,
            "wins": wins, "wins_by_seat": by_seat, "points": points / n, "rounds": rounds / n,
            "win_how": win_how, "games_how": games_how, "best_other": best_other / n,
            "refused": refused, "decisions": decisions, "ended": ended, "saved": saved}


# ---- Can it play -------------------------------------------------------------------------------------------

CAN_PLAY = ["gen-limits-1", "gen-limits-2", "gen-tiny-1", "gen-tiny-2", "gen-tiny-3"] + [f"gen-odd-{i}" for i in range(8)]


def can_play_task(task):
    """Play one made-up game at one seat count, the subject at each seat in turn, the others random."""
    from charter import Game
    spec, game_id, seats, n, vote_mode = task
    label, maker, _ = load_subject(spec)
    bot = spec if spec in BOTS else None
    out = {"game": game_id, "seats": seats, "games": 0, "ended": 0, "refused": 0, "errors": 0, "decisions": 0,
           "first_error": ""}
    try:
        g = Game({"game": game_id, "lineup": ["caller"] * seats, "seed": 1, "vote_mode": vote_mode})
    except Exception as e:  # noqa: BLE001
        out["errors"] += 1
        out["first_error"] = f"could not start: {e}"
        return out
    for k in range(n):
        at = k % seats
        me = bot if bot and bot != "hand" else "caller"
        lineup = [me if s == at else "caller" for s in range(seats)]
        try:
            g.restart(lineup, 7000 + k)
            subject = maker(7000 + k) if maker else None
            if subject:
                subject.reset()
            others = RandomPlayer(7001 + k)
            steps = 0
            while not g.over and steps < 50000:
                steps += 1
                if g.seat == at:
                    a = subject.act(g) if subject else g.suggest("hand")
                    if a < 0:
                        a = int(g.legal()[0])
                    out["decisions"] += 1
                    if not g.step(a):
                        out["refused"] += 1
                        if not out["first_error"]:
                            out["first_error"] = f"game {k}: action {a} refused"
                        g.step(int(g.legal()[0]))
                else:
                    g.step(others.act(g))
                    if subject is not None and WAIT_STEPS[0] and hasattr(subject, "wait"):
                        subject.wait(g.obs_size)
            out["games"] += 1
            out["ended"] += int(g.info()["over"]) and int(g.over)
        except Exception as e:  # noqa: BLE001
            out["errors"] += 1
            if not out["first_error"]:
                out["first_error"] = f"game {k}: {type(e).__name__}: {e}"
    return out


def can_play_report(label, rows):
    bad = sum(r["games"] - r["ended"] + r["refused"] + r["errors"] for r in rows)
    out = [f"**Can it play: {label}** (made-up games that pass `G.Valid`, 2 to 6 seats, at every seat, against "
           f"random players). {'PASS' if bad == 0 else 'FAIL'}: {sum(r['games'] for r in rows)} games, "
           f"{sum(r['ended'] for r in rows)} ended, {sum(r['refused'] for r in rows)} refused actions, "
           f"{sum(r['errors'] for r in rows)} errors, {sum(r['decisions'] for r in rows)} decisions by the subject.", ""]
    problems = [r for r in rows if r["games"] - r["ended"] + r["refused"] + r["errors"]]
    if problems:
        out += ["| game | seats | games | ended | refused | errors | first error |", "|---|---|---|---|---|---|---|"]
        out += [f"| {r['game']} | {r['seats']} | {r['games']} | {r['ended']} | {r['refused']} | {r['errors']} | "
                f"{r['first_error']} |" for r in problems]
        out.append("")
    return "\n".join(out) + "\n"


# ---- Saved games -------------------------------------------------------------------------------------------

def seat_names(label, lineup, at):
    names = []
    for s, who in enumerate(lineup):
        if s == at:
            names.append(f"subject {label}")
        else:
            names.append(f"{'random' if who == 'caller' else who} {s}")
    return names


def save_game(g, log_dir, label, game_id, opponent, phase, laws, k, at, seed, lineup, info):
    """Write one game's server log and its summary. Returns a row for the index."""
    code = table_code(game_id, opponent, phase, laws, k)
    names = seat_names(label, lineup, at)
    log = g.saved_log(code, names)
    state = g.saved_state()
    sub = os.path.join(log_dir, label.replace("/", "_"))
    os.makedirs(sub, exist_ok=True)
    open(os.path.join(sub, f"{code}.jsonl"), "w").write(log)
    events = [json.loads(l) for l in log.splitlines() if l]
    text = summary(events, state, names, at, info, game_id, opponent, phase, laws, seed)
    open(os.path.join(sub, f"{code}.md"), "w").write(text)
    winner = int(info["winner"])
    return {"code": code, "dir": os.path.basename(sub), "game": game_id, "opponent": opponent, "phase": phase,
            "laws": laws, "k": k, "seat": at, "seed": seed, "won": winner == at,
            "winner": names[winner] if 0 <= winner < len(names) else "nobody",
            "points": [int(info[f"points{s}"]) for s in range(SEATS)], "rounds": int(info["round"])}


def move_kind(m):
    t = m.get("t", "?")
    if t == "place":
        return f"build {m.get('kind', '?')}"
    return {"bankTrade": "bank trade", "endTurn": "end turn"}.get(t, t)


def summary(events, state, names, at, info, game_id, opponent, phase, laws, seed):
    """A short readable account of one saved game, from its log and the state after each event."""
    play = events[len(events) - len(state):]   # the game's own events, after create, joins and start
    seats = len(names)
    kinds = [{} for _ in range(seats)]
    builds = [[] for _ in range(seats)]
    trades = []
    votes = {}
    proposals = []
    laws_before = None
    for ev, st in zip(play, state):
        rnd, setup, nlaws = st[0], st[1], st[2]
        when = "setup" if setup else f"r{rnd}"
        t = ev.get("t")
        if t == "move":
            s, m = ev["seat"], ev["move"]
            name = move_kind(m)
            kinds[s][name] = kinds[s].get(name, 0) + 1
            if m.get("t") == "place":
                where = m.get("spot", m.get("link", m.get("on", "")))
                builds[s].append(f"{when} {m.get('kind')} at {where}")
            elif m.get("t") in ("bankTrade", "offer", "accept"):
                trades.append(f"{when} {names[s]}: {m.get('t')} {json.dumps({k: v for k, v in m.items() if k != 't'})}")
        elif t == "propose":
            proposals.append({"id": None, "by": names[ev["seat"]], "text": ev.get("text", ""), "when": when,
                              "laws_before": nlaws - 0})
        elif t == "vote":
            votes.setdefault(ev["id"], []).append((names[ev["seat"]], ev["yes"], nlaws))
        laws_before = nlaws
    out = [f"# {game_id}, against {opponent}, phase `{phase}`, {'with' if laws else 'without'} laws", "",
           f"Seed {seed}. Subject at seat {at}. Rounds: {int(info['round'])}. "
           f"Winner: {names[int(info['winner'])] if int(info['winner']) >= 0 else 'nobody'}. "
           "Points: " + ", ".join(f"{names[s]} {int(info[f'points{s}'])}" for s in range(seats)) + ".", ""]
    out += ["## Moves by type", "", "| seat | " + " | ".join(["moves"]) + " |", "|---|---|"]
    for s in range(seats):
        out.append(f"| {names[s]} | " + ", ".join(f"{k} {v}" for k, v in sorted(kinds[s].items())) + " |")
    out += ["", "## Points at the end of each round", "", "| round | " + " | ".join(names) + " |",
            "|---|" + "---|" * seats]
    last = {}
    for st in state:
        if not st[1]:
            last[st[0]] = st[3:3 + seats]
    for r in sorted(last):
        out.append(f"| {r} | " + " | ".join(str(x) for x in last[r]) + " |")
    out += ["", "## Built", ""]
    for s in range(seats):
        out.append(f"- **{names[s]}**: " + ("; ".join(builds[s]) if builds[s] else "nothing"))
    out += ["", f"## Trades ({len(trades)})", ""] + [f"- {t}" for t in trades[:60]]
    if len(trades) > 60:
        out.append(f"- ... and {len(trades) - 60} more")
    out += ["", f"## Laws proposed ({len(proposals)}) and votes", ""]
    for i, p in enumerate(proposals):
        out.append(f"- {p['when']}, {p['by']}: `{p['text']}`")
    for pid, vs in sorted(votes.items()):
        yes = [n for n, y, _ in vs if y]
        no = [n for n, y, _ in vs if not y]
        passed = vs[-1][2] > vs[0][2] if vs else False
        out.append(f"- proposal {pid}: yes {yes}, no {no}" + (" (laws in force rose: passed)" if passed else ""))
    return "\n".join(out) + "\n"


def write_index(log_dir, everything):
    rows = ["# Saved games", "", "Each game has a server log (`.jsonl`) and a summary (`.md`). "
            "`charter-rl-logs DIR` makes the `.db` files that `make spectate RESULTS=DIR` opens.", "",
            "| subject | game | opponents | phase | laws | seat | won | winner | points | rounds | summary |",
            "|---|---|---|---|---|---|---|---|---|---|---|"]
    for label, results in everything.items():
        for r in results:
            for x in r.get("saved", []):
                rows.append(f"| {label} | {x['game']} | {x['opponent']} | {x['phase']} | {'yes' if x['laws'] else 'no'} "
                            f"| {x['seat']} | {'yes' if x['won'] else 'no'} | {x['winner']} | "
                            f"{'/'.join(map(str, x['points']))} | {x['rounds']} | [{x['code']}]({x['dir']}/{x['code']}.md) |")
    open(os.path.join(log_dir, "index.md"), "w").write("\n".join(rows) + "\n")


def make_dbs(log_dir):
    """Run charter-rl-logs on each subject's folder of saved games, when it is built."""
    here = os.path.join(HERE, "..", "..", ".lake", "build", "bin", "charter-rl-logs")
    exe = os.environ.get("CHARTER_RL_LOGS", here)
    if not os.path.exists(exe):
        print(f"charter-rl-logs not found at {exe}: the .db files are not made")
        return None
    ok = True
    for d in sorted(os.listdir(log_dir)):
        p = os.path.join(log_dir, d)
        if os.path.isdir(p):
            r = subprocess.run([exe, p], capture_output=True, text=True)
            last = (r.stdout.strip().splitlines() or [""])[-1]
            print(f"saved games, {d}: {last}")
            ok = ok and r.returncode == 0
    return ok


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
        best = sum(r["best_other"] * r["games"] for r in sel) / n
        tw = sum(r["win_how"]["target"] for r in sel)
        tlo, thi = wilson(tw, n)
        limit_w = sum(r["win_how"]["limit"] for r in sel)
        other_w = w - tw - limit_w
        share = (f"{pct(tw / w)} / {pct(limit_w / w)} / {pct(other_w / w)}" if w else "n/a")
        limit_games = sum(r["games_how"]["limit"] for r in sel)
        rows.append(f"| {opp} | {n} | {pct(w / n)} | {pct(lo)} to {pct(hi)} | {pct(tw / n)} ({pct(tlo)} to {pct(thi)}) | "
                    f"{share} | {pct(limit_games / n)} | " + " / ".join(pct(x) for x in seat) +
                    f" | {pts:.2f} | {best:.2f} |")
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
                        "| opponents | games | win % | 95% interval | target wins % (95%) | wins at target / at round "
                        "limit / other | games ending at the limit % | win % by seat 0/1/2/3 | points | best opponent "
                        "points |",
                        "|---|---|---|---|---|---|---|---|---|---|"] + rows + [""]
    out += [f"Refused actions: {refused}. Games that did not end: {unended}.", "",
            "*Target wins* count only games the subject won by reaching the game's target points. A win at the round "
            "limit goes to the leader on points (ties broken by the rules), often with a low score; *other* is a win "
            "when a law ended the game. *Best opponent points* is the mean of the highest other seat's points.", ""]
    out += ["**By game, whole game, with laws** (win %, 95% interval, target wins %, points against the best "
            "opponent's points)", "",
            "| game | " + " | ".join(OPPONENTS) + " |", "|---|" + "---|" * len(OPPONENTS)]
    for g in TRAIN + HELD_OUT:
        cells = []
        for opp in OPPONENTS:
            sel = [r for r in results if r["game"] == g and r["opponent"] == opp and r["phase"] == "whole" and r["laws"]]
            w, n = sum(r["wins"] for r in sel), sum(r["games"] for r in sel)
            if n:
                lo, hi = wilson(w, n)
                pts = sum(r["points"] * r["games"] for r in sel) / n
                best = sum(r["best_other"] * r["games"] for r in sel) / n
                tw = sum(r["win_how"]["target"] for r in sel)
                cells.append(f"{pct(w / n)} ({pct(lo)} to {pct(hi)}), target {pct(tw / n)}, {pts:.1f} vs {best:.1f}")
            else:
                cells.append("")
        out.append(f"| {g}{' (held out)' if g in HELD_OUT else ''} | " + " | ".join(cells) + " |")
    out.append("")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("subjects", nargs="+")
    ap.add_argument("--games", type=int, default=200, help="games per table, a multiple of 4")
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--out", default="results/eval")
    ap.add_argument("--quick", action="store_true", help="whole games with laws only")
    ap.add_argument("--opponents", default=",".join(OPPONENTS),
                    help="comma-separated: hand, random, champion, champion-closed")
    ap.add_argument("--logs", type=int, default=2, help="games kept per table, with logs and summaries")
    ap.add_argument("--wait-steps", type=int, default=1,
                    help="1: step the policy's recurrent state on zeros when another caller decides, as in training")
    ap.add_argument("--can-play", type=int, default=1, help="1 to run the can-it-play check on made-up games")
    ap.add_argument("--can-play-games", type=int, default=6, help="games per made-up game and seat count")
    args = ap.parse_args()
    OPPONENTS[:] = args.opponents.split(",")
    WAIT_STEPS[0] = args.wait_steps
    log_dir = os.path.join(args.out, "games")
    n = max(SEATS, args.games - args.games % SEATS)
    os.makedirs(args.out, exist_ok=True)
    text = ["# Charter eval", "", NOTE_SAME, "", NOTE_WEAK, "",
            f"Each table has {n} games, with the subject at each seat in {n // SEATS} of them. "
            "Phases: `whole`, the subject plays all of it; `setup`, the subject places the opening pieces and "
            "`hand` plays on; `play`, `hand` places them and the subject plays on.", ""]
    everything = {}
    for spec in args.subjects:
        label, _, settings = load_subject(spec)
        vote_mode = settings.get("vote_mode", "bot")
        phases = ["whole"] if args.quick else PHASES
        lawset = [True] if args.quick else [True, False]
        tasks = [(spec, g, o, p, l, n, vote_mode, settings, min(args.logs, n), log_dir)
                 for g in TRAIN + HELD_OUT for o in OPPONENTS for p in phases for l in lawset
                 if not (label in BOTS and p != "whole")]
        t0 = time.time()
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(play_table, tasks))
        text.append(report(label, settings, results, time.time() - t0))
        if args.can_play:
            cp_tasks = [(spec, gid, seats, args.can_play_games, vote_mode) for gid in CAN_PLAY for seats in range(2, 7)]
            with ProcessPoolExecutor(max_workers=args.jobs) as pool:
                cp = list(pool.map(can_play_task, cp_tasks))
            text.append(can_play_report(label, cp))
            print(f"{label}: can it play done", flush=True)
        everything[label] = results
        print(f"{label}: done in {time.time() - t0:.0f} s", flush=True)
    if args.logs:
        write_index(log_dir, everything)
        text.append(f"Saved games: {log_dir}/index.md." + ("" if make_dbs(log_dir) is not False else
                                                             " Some saved games did not replay: see the output."))
    open(os.path.join(args.out, "report.md"), "w").write("\n".join(text))
    json.dump(everything, open(os.path.join(args.out, "report.json"), "w"), indent=1)
    print("\n".join(text))


if __name__ == "__main__":
    main()
