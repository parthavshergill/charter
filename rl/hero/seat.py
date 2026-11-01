#!/usr/bin/env python3
"""Play one seat of a Charter game over the server's HTTP API, one decision at a time.

A language-model agent drives this with a shell, one seat per agent. A trained policy bot plays
one more seat on the server itself (start the server with CHARTER_BOT=policy).

Commands:

  seat.py new --server URL --world island --policy-seat K --weights-label X [--mode restricted|full]
      Make a 4-seat game. Seats other than K join as players; seat K is the server's bot.
      Prints the game code. The game starts at once.
  seat.py wait --game CODE --seat S
      Wait until this seat has something to decide, or the game is over. Then print the state as
      this seat sees it and a numbered list of the moves it may make.
  seat.py play --game CODE --seat S N
      Make move N of the last list. The list is checked again against the server first.
  seat.py result --game CODE
      Who won, everyone's points, and which seat was the policy. Saves the game to games/CODE.json.

Full mode only (refused in restricted mode):

  seat.py say --game CODE --seat S [--to T] TEXT     talk to the table, or privately to seat T
  seat.py offer --game CODE --seat S --give brick:1,wool:1 --get ore:1 [--to T]
  seat.py propose --game CODE --seat S (--text RULE | --sample ID)

Modes. The mode is chosen once, by `new`, and kept with the game; later commands use it.

  restricted  The seat has exactly the trained policy's actions: end turn, bank trades, declarations
              (at the policy's levels) and placing pieces. No laws, offers, deals, votes or talk.
              The list shows only those, and `play` refuses anything else.
  full        Every move the server allows a player: also votes, deals, accepting and making offers,
              proposing laws and talk.

The seat tokens are kept in a state folder ($CHARTER_SEAT_STATE, or ~/.cache/charter-seat), not
printed. Only the Python standard library is used.
"""

import argparse
import json
import math
import os
import random
import sys
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
GAMES_DIR = os.path.join(HERE, "games")
STATE_DIR = os.environ.get("CHARTER_SEAT_STATE") or os.path.expanduser("~/.cache/charter-seat")

# The trained policy's declaration levels (Server/Policy/Layout.lean, `declareLevels`).
DECLARE_LEVELS = [0, 1, 2, 3, 4, 6, 8, 12]
# Move kinds the policy has an action for. Everything else is refused in restricted mode.
RESTRICTED_KINDS = {"place", "bankTrade", "declare", "endTurn"}


class SeatError(Exception):
    """A problem to report to the agent in one line."""


# ---------------------------------------------------------------------------
# HTTP


def http(server, method, path, body=None, token=None, timeout=60):
    """Send one request and return the JSON answer. Raise SeatError on a refusal."""
    url = server.rstrip("/") + path
    data = None
    headers = {}
    if body is not None:
        data = json.dumps(body).encode()
        headers["Content-Type"] = "application/json"
    if token:
        headers["X-Charter-Token"] = token
    req = urllib.request.Request(url, data=data, method=method, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            text = r.read().decode()
    except urllib.error.HTTPError as e:
        text = e.read().decode()
    except urllib.error.URLError as e:
        raise SeatError(f"cannot reach the server at {server}: {e.reason}")
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        raise SeatError(f"the server sent something that is not JSON: {text[:200]}")


def check_ok(answer):
    """The server answers {"ok": false, "error": ...} when it refuses."""
    if isinstance(answer, dict) and answer.get("ok") is False:
        raise SeatError(answer.get("error") or "refused")
    if isinstance(answer, dict) and "error" in answer and answer.get("ok") is not True:
        raise SeatError(answer["error"])
    return answer


# ---------------------------------------------------------------------------
# Local state: the game's settings and the seats' tokens


def state_path(code):
    return os.path.join(STATE_DIR, f"{code.upper()}.json")


def load_game(code):
    try:
        with open(state_path(code)) as f:
            return json.load(f)
    except FileNotFoundError:
        raise SeatError(f"no game {code} made by `seat.py new` on this machine")


def save_json(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=1)
    os.replace(tmp, path)


def listing_path(code, seat):
    return os.path.join(STATE_DIR, f"{code.upper()}.seat{seat}.last.json")


def seat_token(game, seat):
    tok = game["tokens"].get(str(seat))
    if tok is None:
        if seat == game["policy_seat"]:
            raise SeatError(f"seat {seat} is the policy bot's seat; the server plays it")
        raise SeatError(f"no seat {seat} in this game")
    return tok


def view_of(game, seat=None):
    token = seat_token(game, seat) if seat is not None else None
    v = http(game["server"], "GET", f"/api/games/{game['code']}/view", token=token)
    if "phase" not in v:
        check_ok(v)
        raise SeatError("the server sent no game view")
    return v


# ---------------------------------------------------------------------------
# What a seat may do


def move_kind(item):
    return item["move"]["t"] if item["type"] == "move" else item["type"]


def options(view, seat, mode, game):
    """The numbered choices this seat has now, as a list of dicts with a `type` and a `label`."""
    out = []
    my_turn = view.get("turn") == seat and view.get("phase") != "ended"
    if my_turn:
        for m in view.get("legalMoves", []):
            mv = m["move"]
            if mode == "restricted" and mv["t"] not in RESTRICTED_KINDS:
                continue
            out.append({"type": "move", "move": mv, "label": move_label(view, m, game)})
        decl = view.get("declarations") or {}
        if decl.get("can"):
            top = decl.get("max", 12)
            levels = DECLARE_LEVELS if mode == "restricted" else list(range(0, top + 1))
            for res in view.get("resources", []):
                for n in levels:
                    if n <= top:
                        out.append({"type": "move", "move": {"t": "declare", "res": res, "n": n},
                                    "label": f"Declare {n} {res}"})
    if mode == "full" and view.get("phase") != "ended":
        if not my_turn:
            # Accepting an offer is a move, and the engine allows it out of turn.
            for o in view.get("offers", []):
                if o.get("canAccept"):
                    out.append({"type": "move", "move": {"t": "accept", "id": o["id"]},
                                "label": f"Accept offer {o['id']} from seat {o['from']}: "
                                         f"you get {bundle(o['give'])}, you give {bundle(o['get'])}"})
        for p in view.get("proposals", []):
            if p.get("canVote") and not any(v["seat"] == seat for v in p.get("votes", [])):
                for yes in (True, False):
                    out.append({"type": "vote", "id": p["id"], "yes": yes,
                                "label": f"Vote {'YES' if yes else 'NO'} on law {p['id']} \"{p['title']}\""})
            if p.get("canSign"):
                out.append({"type": "sign", "id": p["id"], "label": f"Sign deal {p['id']} \"{p['title']}\""})
        for d in view.get("deals", []):
            if d.get("canExit"):
                out.append({"type": "exit", "id": d["id"], "label": f"Give notice on deal {d['id']} \"{d['title']}\""})
        if not my_turn and out:
            out.append({"type": "pass", "label": "Do nothing now (wait for your turn)"})
    return out


def pending_for(view, seat, mode):
    """Ids of things that need this seat out of turn (full mode): laws to vote on, deals to sign,
    offers it can accept. Used so `wait` stops once for each."""
    if mode != "full":
        return []
    keys = []
    for p in view.get("proposals", []):
        if p.get("canVote") and not any(v["seat"] == seat for v in p.get("votes", [])):
            keys.append(f"vote{p['id']}")
        if p.get("canSign"):
            keys.append(f"sign{p['id']}")
    for o in view.get("offers", []):
        if o.get("canAccept"):
            keys.append(f"offer{o['id']}")
    return keys


# ---------------------------------------------------------------------------
# Reading the board


def spot_tiles(view):
    """For each spot, the tiles it touches, from the board's positions (a spot is a hex corner)."""
    board = view.get("board") or {}
    tiles = board.get("tiles", [])
    out = []
    for s in board.get("spots", []):
        near = [t for t in tiles if abs(math.hypot(t["x"] - s["x"], t["y"] - s["y"]) - 1.0) < 0.05]
        out.append(near)
    return out


def tile_text(t):
    if t.get("number") is None:
        return f"{t.get('res') or 'desert'}"
    return f"{t['res']} {t['number']}"


def spot_text(view, game, v):
    near = game.setdefault("_spots", spot_tiles(view))
    tiles = near[v] if v < len(near) else []
    paying = [t for t in tiles if t.get("number") is not None and t.get("res")]
    pips = sum(t.get("pips", 0) for t in paying)
    return f"spot {v} [{', '.join(tile_text(t) for t in paying) or 'pays nothing'}; pips {pips}]"


def bundle(b):
    return ", ".join(f"{x['n']} {x['res']}" for x in b) or "nothing"


def move_label(view, entry, game):
    mv = entry["move"]
    if mv["t"] == "place":
        cost = entry.get("cost") or []
        price = f" (costs {bundle(cost)})" if cost else " (free)"
        if "spot" in mv:
            ys = entry.get("yields")
            if ys is not None:
                pips = sum(y.get("pips", 0) for y in ys)
                pays = ", ".join("%s %s" % (y["res"], y["number"]) for y in ys) or "pays nothing"
                where = f"spot {mv['spot']} [{pays}; pips {pips}]"
            else:
                where = spot_text(view, game, mv["spot"])
            return f"Place {mv['kind']} at {where}{price}"
        a, b = mv["link"]
        return f"Place {mv['kind']} on link {a}-{b}{price}"
    return entry.get("label") or json.dumps(mv)


def seat_name(view, i):
    for s in view.get("seats", []):
        if s["seat"] == i:
            return s.get("name", f"seat {i}")
    return f"seat {i}"


def hand_text(h):
    return ", ".join(f"{k} {v}" for k, v in h.items() if v) or "nothing"


def render(view, seat, game, opts):
    """The state as this seat sees it, and the numbered choices."""
    lines = []
    pol = game["policy_seat"]
    turn = view.get("turn")
    lines.append(f"Game {view['code']} ({view['game']['name']}), mode {game['mode']}. You are seat {seat}.")
    lines.append(f"Round {view.get('round')} of {view.get('rounds')}. Target {view.get('target')} points. "
                 f"Phase: {view.get('phase')}. Turn: seat {turn}{' (YOU)' if turn == seat else ''}. "
                 f"Last roll: {view.get('lastRoll')}. Bank rate: {view.get('bankRate')} for 1. "
                 f"Actions left this turn: {view.get('actionsLeft')}.")
    if view.get("prompt"):
        lines.append(f"Prompt: {view['prompt']}")
    lines.append("")
    lines.append("Seats (in turn order):")
    by_seat = {}
    for p in view.get("pieces", []):
        by_seat.setdefault(p["owner"], []).append(p)
    for s in view.get("seats", []):
        i = s["seat"]
        tag = " <- you" if i == seat else (" (trained policy bot)" if i == pol else "")
        pieces = ", ".join(f"{k} {v}" for k, v in s.get("pieces", {}).items() if v) or "none"
        lines.append(f"  seat {i} {s.get('name')}{tag}: {s.get('points')} points; hand: {hand_text(s.get('hand', {}))}; "
                     f"pieces: {pieces}")
    lines.append("")
    lines.append("Board tiles (resource number): " +
                 "; ".join(tile_text(t) for t in (view.get("board") or {}).get("tiles", [])))
    lines.append("Pieces on the board:")
    for s in view.get("seats", []):
        i = s["seat"]
        ps = by_seat.get(i, [])
        if not ps:
            continue
        where = []
        for p in ps:
            if "spot" in p:
                where.append(f"{p['kind']} at {spot_text(view, game, p['spot'])}")
            else:
                where.append(f"{p['kind']} on {p['link'][0]}-{p['link'][1]}")
        lines.append(f"  seat {i}: " + "; ".join(where))
    worth = view.get("worth") or []
    if worth:
        lines.append("Resources worth points: " + ", ".join(f"{w['res']} = {w['points']}" for w in worth))
    laws = view.get("laws") or []
    lines.append("")
    lines.append("Laws in force: " + ("none" if not laws else ""))
    for L in laws:
        lines.append(f"  law {L['id']} \"{L['title']}\": {L['text']}")
    props = view.get("proposals") or []
    if props:
        lines.append("Open proposals:")
        for p in props:
            votes = ", ".join(f"seat {v['seat']} {'yes' if v['yes'] else 'no'}" for v in p.get("votes", [])) or "no votes"
            lines.append(f"  {p['kind']} {p['id']} by seat {p['by']} \"{p['title']}\": {p['text']}  "
                         f"[{votes}; {p.get('yesNeeded')} more yes needed]")
    offers = view.get("offers") or []
    if offers:
        lines.append("Open offers:")
        for o in offers:
            to = "anyone" if o.get("to") is None else f"seat {o['to']}"
            lines.append(f"  offer {o['id']} from seat {o['from']} to {to}: gives {bundle(o['give'])}, "
                         f"wants {bundle(o['get'])}")
    deals = view.get("deals") or []
    if deals:
        lines.append("Running deals:")
        for d in deals:
            lines.append(f"  deal {d['id']} \"{d['title']}\": {d['english']}")
    decl = view.get("declarations") or {}
    if decl.get("rows"):
        lines.append("Declared this round: " + ", ".join(f"seat {r['seat']} {r['n']} {r['res']}" for r in decl["rows"]))
    if game["mode"] == "full" and game.get("_talk"):
        lines.append("Recent talk:")
        for t in game["_talk"][-10:]:
            lines.append(f"  {t}")
    lines.append("")
    if opts:
        lines.append("Your moves (answer with: seat.py play --game CODE --seat S N):")
        for n, o in enumerate(opts):
            lines.append(f"  {n}: {o['label']}")
    else:
        lines.append("You have no moves now.")
    if game["mode"] == "full":
        lines.append("")
        lines.append("Also (full mode): seat.py say/offer/propose; see seat.py --help.")
    return "\n".join(lines)


def talk_lines(game, seat):
    try:
        t = http(game["server"], "GET", f"/api/games/{game['code']}/talk", token=seat_token(game, seat))
    except SeatError:
        return []
    out = []
    for l in t.get("lines", []):
        who = f"seat {l.get('seat')}" if "seat" in l else l.get("from", "?")
        to = f" (to seat {l['to']})" if l.get("to") is not None else ""
        out.append(f"{who}{to}: {l.get('text')}")
    return out


# ---------------------------------------------------------------------------
# Results and the saved game


def result_of(view, game):
    seats = view.get("seats", [])
    winner = view.get("winner")
    target = view.get("target")
    points = {s["seat"]: s.get("points") for s in seats}
    ended = view.get("phase") == "ended"
    how = None
    if ended:
        if view.get("endedBy"):
            how = f"a law ended the game ({view['endedBy']})"
        elif winner is not None and target is not None and points.get(winner, 0) >= target:
            how = "target reached"
        else:
            how = "round limit"
    return {
        "code": view["code"], "world": view["game"]["id"], "mode": game["mode"],
        "ended": ended, "winner": winner, "how": how, "round": view.get("round"),
        "rounds": view.get("rounds"), "target": target, "points": points,
        "policy_seat": game["policy_seat"], "weights_label": game.get("weights_label"),
        "policy_won": ended and winner == game["policy_seat"],
    }


def save_game_log(game, view):
    """Write the finished game to games/CODE.json: our settings, the result, the last view and the log."""
    try:
        events = http(game["server"], "GET", f"/api/games/{game['code']}/events")
    except SeatError:
        events = None
    doc = {"result": result_of(view, game), "settings": {k: v for k, v in game.items()
                                                       if k not in ("tokens",) and not k.startswith("_")},
           "final_view": view, "events": events}
    path = os.path.join(GAMES_DIR, f"{game['code']}.json")
    save_json(path, doc)
    return path


def result_text(r):
    pts = ", ".join(f"seat {k}: {v}" for k, v in sorted(r["points"].items()))
    if not r["ended"]:
        return f"Game {r['code']} is not over: round {r['round']} of {r['rounds']}. Points: {pts}."
    return (f"GAME OVER. Game {r['code']}: winner seat {r['winner']} ({r['how']}), round {r['round']} of "
            f"{r['rounds']}, target {r['target']}. Points: {pts}. Policy seat: {r['policy_seat']}"
            f"{' (WON)' if r['policy_won'] else ''}.")


# ---------------------------------------------------------------------------
# Commands


def cmd_new(a):
    if a.policy_seat < 0 or a.policy_seat >= a.seats:
        raise SeatError(f"--policy-seat must be 0 to {a.seats - 1}")
    made = check_ok(http(a.server, "POST", "/api/games", {"seats": a.seats, "game": a.world}))
    code = made["code"]
    tokens = {}
    for i in range(a.seats):
        if i == a.policy_seat:
            r = check_ok(http(a.server, "POST", f"/api/games/{code}/bot", {}))
        else:
            r = check_ok(http(a.server, "POST", f"/api/games/{code}/join",
                              {"name": f"{a.name_prefix}{i}", "nonce": random.getrandbits(53)}))
            tokens[str(i)] = r["token"]
        if r.get("seat") != i:
            raise SeatError(f"seat {i} was given seat {r.get('seat')}; the table is not as planned")
    game = {"code": code, "server": a.server, "world": a.world, "seats": a.seats, "mode": a.mode,
            "policy_seat": a.policy_seat, "weights_label": a.weights_label, "created": time.time(),
            "tokens": tokens}
    save_json(state_path(code), game)
    v = view_of(game, next(int(s) for s in tokens))
    print(json.dumps({"code": code, "world": a.world, "mode": a.mode, "policy_seat": a.policy_seat,
                      "player_seats": sorted(int(s) for s in tokens), "weights_label": a.weights_label,
                      "phase": v.get("phase"), "rounds": v.get("rounds"), "target": v.get("target")}))


def check_mode(game, a):
    if a.mode and a.mode != game["mode"]:
        raise SeatError(f"this game was made in {game['mode']} mode; the mode cannot change")


def cmd_wait(a):
    game = load_game(a.game)
    check_mode(game, a)
    seat = a.seat
    seat_token(game, seat)
    lp = listing_path(game["code"], seat)
    try:
        with open(lp) as f:
            seen = set(json.load(f).get("seen", []))
    except (FileNotFoundError, json.JSONDecodeError):
        seen = set()
    start = time.time()
    while True:
        v = view_of(game, seat)
        if v.get("phase") == "ended":
            path = save_game_log(game, view_of(game))
            print(result_text(result_of(v, game)))
            print(f"Saved to {path}")
            return
        mine = v.get("phase") != "lobby" and v.get("turn") == seat
        news = [k for k in pending_for(v, seat, game["mode"]) if k not in seen]
        if mine or news:
            break
        if a.timeout and time.time() - start > a.timeout:
            print(f"Still waiting after {a.timeout} s: it is seat {v.get('turn')}'s turn. Run wait again.")
            return
        time.sleep(a.poll)
    if game["mode"] == "full":
        game["_talk"] = talk_lines(game, seat)
    opts = options(v, seat, game["mode"], game)
    save_json(lp, {"version": v.get("version"), "options": opts,
                   "seen": sorted(seen | set(pending_for(v, seat, game["mode"])))})
    print(render(v, seat, game, opts))


def submit(game, seat, opt):
    tok = seat_token(game, seat)
    base = f"/api/games/{game['code']}"
    t = opt["type"]
    if t == "move":
        return http(game["server"], "POST", base + "/move", {"token": tok, "move": opt["move"]})
    if t == "vote":
        return http(game["server"], "POST", base + "/vote", {"token": tok, "id": opt["id"], "yes": opt["yes"]})
    if t == "sign":
        return http(game["server"], "POST", base + "/sign", {"token": tok, "id": opt["id"]})
    if t == "exit":
        return http(game["server"], "POST", base + "/exit", {"token": tok, "dealId": opt["id"]})
    raise SeatError(f"unknown choice {t}")


def same(o1, o2):
    return {k: v for k, v in o1.items() if k != "label"} == {k: v for k, v in o2.items() if k != "label"}


def cmd_play(a):
    game = load_game(a.game)
    check_mode(game, a)
    seat = a.seat
    lp = listing_path(game["code"], seat)
    try:
        with open(lp) as f:
            last = json.load(f)
    except FileNotFoundError:
        raise SeatError("run `seat.py wait` first, to get the list of moves")
    opts = last["options"]
    if a.n < 0 or a.n >= len(opts):
        raise SeatError(f"no move {a.n}: the list has 0 to {len(opts) - 1}")
    choice = opts[a.n]
    if game["mode"] == "restricted" and move_kind(choice) not in RESTRICTED_KINDS:
        raise SeatError(f"restricted mode: the policy has no action of kind {move_kind(choice)}")
    v = view_of(game, seat)
    fresh = options(v, seat, game["mode"], game)
    if not any(same(choice, f) for f in fresh):
        raise SeatError("that move is no longer on offer (the state changed). Run `seat.py wait` again.")
    if choice["type"] == "pass":
        print("OK: you wait.")
        last["options"] = []
        save_json(lp, last)
        return
    r = submit(game, seat, choice)
    if r.get("ok") is False or ("error" in r and r.get("ok") is not True):
        print(f"REFUSED: {choice['label']}: {r.get('error')}")
        sys.exit(1)
    # A used list is spent: the next decision needs a fresh `wait`.
    last["options"] = []
    save_json(lp, last)
    v = view_of(game, seat)
    me = next((s for s in v.get("seats", []) if s["seat"] == seat), {})
    status = "game over" if v.get("phase") == "ended" else (
        "still your turn" if v.get("turn") == seat else f"now seat {v.get('turn')}'s turn")
    print(f"OK: {choice['label']}. You have {me.get('points')} points; hand: {hand_text(me.get('hand', {}))}; "
          f"{status}. Run `seat.py wait` for your next decision.")


def full_only(game, what):
    if game["mode"] != "full":
        raise SeatError(f"restricted mode: the policy cannot {what}")


def cmd_say(a):
    game = load_game(a.game)
    check_mode(game, a)
    full_only(game, "talk")
    body = {"token": seat_token(game, a.seat), "text": " ".join(a.text)}
    if a.to is not None:
        body["to"] = a.to
    check_ok(http(game["server"], "POST", f"/api/games/{game['code']}/talk", body))
    print("OK: said.")


def parse_bundle(text):
    out = []
    for part in filter(None, (p.strip() for p in text.split(","))):
        res, _, n = part.partition(":")
        out.append({"res": res.strip(), "n": int(n or 1)})
    return out


def cmd_offer(a):
    game = load_game(a.game)
    check_mode(game, a)
    full_only(game, "make offers")
    mv = {"t": "offer", "to": a.to, "give": parse_bundle(a.give), "get": parse_bundle(a.get)}
    r = http(game["server"], "POST", f"/api/games/{game['code']}/move", {"token": seat_token(game, a.seat), "move": mv})
    check_ok(r)
    print("OK: offer made. It goes away at the end of your turn.")


def cmd_propose(a):
    game = load_game(a.game)
    check_mode(game, a)
    full_only(game, "propose laws")
    body = {"token": seat_token(game, a.seat)}
    if a.sample:
        body["sample"] = a.sample
    elif a.text:
        body["text"] = a.text
    else:
        raise SeatError("give --text RULE or --sample ID")
    if a.check:
        print(json.dumps(http(game["server"], "POST", f"/api/games/{game['code']}/check", body), indent=1))
        return
    check_ok(http(game["server"], "POST", f"/api/games/{game['code']}/propose", body))
    print("OK: proposed.")


def cmd_result(a):
    game = load_game(a.game)
    v = view_of(game)
    r = result_of(v, game)
    if r["ended"]:
        r["saved"] = save_game_log(game, v)
    print(result_text(r))
    print(json.dumps(r))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    n = sub.add_parser("new", help="make a game with the policy bot in one seat")
    n.add_argument("--server", default=os.environ.get("CHARTER_SERVER", "http://127.0.0.1:8787"))
    n.add_argument("--world", default="island")
    n.add_argument("--seats", type=int, default=4)
    n.add_argument("--policy-seat", type=int, required=True)
    n.add_argument("--weights-label", default="")
    n.add_argument("--mode", choices=["restricted", "full"], default="restricted")
    n.add_argument("--name-prefix", default="Seat ")
    n.set_defaults(fn=cmd_new)

    def seat_args(q):
        q.add_argument("--game", required=True)
        q.add_argument("--seat", type=int, required=True)
        q.add_argument("--mode", choices=["restricted", "full"], default=None,
                       help="must match the mode the game was made with")

    w = sub.add_parser("wait", help="wait for this seat's next decision and list its moves")
    seat_args(w)
    w.add_argument("--poll", type=float, default=1.0, help="seconds between looks at the server")
    w.add_argument("--timeout", type=float, default=0, help="give up after this many seconds (0: never)")
    w.set_defaults(fn=cmd_wait)

    pl = sub.add_parser("play", help="make move N of the last list")
    seat_args(pl)
    pl.add_argument("n", type=int)
    pl.set_defaults(fn=cmd_play)

    s = sub.add_parser("say", help="(full mode) talk to the table")
    seat_args(s)
    s.add_argument("--to", type=int, default=None)
    s.add_argument("text", nargs="+")
    s.set_defaults(fn=cmd_say)

    o = sub.add_parser("offer", help="(full mode) offer a trade on your turn, e.g. --give brick:1 --get ore:1")
    seat_args(o)
    o.add_argument("--give", required=True)
    o.add_argument("--get", required=True)
    o.add_argument("--to", type=int, default=None)
    o.set_defaults(fn=cmd_offer)

    pr = sub.add_parser("propose", help="(full mode) propose a law in the rule language, or a sample law")
    seat_args(pr)
    pr.add_argument("--text")
    pr.add_argument("--sample")
    pr.add_argument("--check", action="store_true", help="only check the text and show its preview")
    pr.set_defaults(fn=cmd_propose)

    r = sub.add_parser("result", help="the game's result; saves it to games/CODE.json when over")
    r.add_argument("--game", required=True)
    r.set_defaults(fn=cmd_result)

    a = p.parse_args()
    try:
        a.fn(a)
    except SeatError as e:
        print(f"ERROR: {e}")
        sys.exit(2)


if __name__ == "__main__":
    main()
