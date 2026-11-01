#!/usr/bin/env python3
"""Checks that what the server sends goes through `observe`, the one function that says what a seat may know.

`Server/SecrecyPromise.lean` proves what `observe` hides. This checks the step after it, which no theorem
covers: that the server builds what it sends from `observe`. It has three parts.

1. The code. In the files that build what is sent, every read of the true state, the true chronicle or a
   saved state is on the list below, with the reason it is safe. A new read fails the check until someone
   adds it with a reason.
2. The routes. Every route in `Server/Main.lean` is on the list below, with what it sends. A new route fails
   the check until someone adds it.
3. A real game. It plays High Card over HTTP with two people and checks what each one is sent, after every
   event: no other seat's card, no other seat's bet, no other seat's roll. Then it checks that a replay
   hides them until the game ends, and shows them after.

`ServerTests.lean` imports `Server/SecrecyCheck.lean`, which compares everything sent to a seat at two
tables that differ only in hidden things. This script adds the HTTP layer.
"""
import json, os, re, shutil, sys, tempfile

sys.dont_write_bytecode = True

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smoke import Server, check, free_port  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# The files that build what a seat, a spectator, a Claude seat, the clerk or a bot is given.
OUTPUT_FILES = ["Server/View.lean", "Server/Seat.lean", "Server/Formalize.lean", "Server/Suggest.lean",
                "Server/Main.lean", "Server/Clerk.lean", "Server/Describe.lean", "Server/Bots.lean",
                "Server/Player.lean", "Server/Talk.lean"]
TRUE_STATE = re.compile(r"\.state\b(?!\.(get|modify))|\.live\b|\.chronicle\b|\.opened\b")

# Each read of the true state in those files, and why it is safe. Keyed by file and the line's text.
ALLOWED = {
    ("Server/View.lean", "let stale := match g.opened.find? (·.1 == id) with"):
        "a saved state goes only to Preview.seatPreview, which observes it",
    ("Server/View.lean", '    , ("chronicle", Json.arr ((if reveal then g.chronicle else g.chronicleFor you).map lineJson)) ]'):
        "the whole chronicle only for a replay of a game that has ended",
    ("Server/View.lean", "match g.state.map (observe sec you) with"): "the view's state, through observe",
    ("Server/View.lean", "let phase := match g.state with"): "the summary sends only the phase",
    ("Server/Seat.lean", "let s := sit.state"): "a situation's state is observed, in Player.situation",
    ("Server/Seat.lean", "if sit.state.phase == .setup then"): "a situation's state is observed",
    ("Server/Seat.lean", "let m := Bots.setupMove sit.state sit.legal.get"): "a situation's state is observed",
    ("Server/Seat.lean", "if w.to != seat && sit.state.turnOrder.contains w.to then"): "a situation's state is observed",
    ("Server/Seat.lean", "let events := if sit.state.phase == .setup && placesHere then"): "a situation's state is observed",
    ("Server/Seat.lean", "let majors := ((g.chronicle.toList.filter (·.major)).reverse.take 120).reverse.map (Clerk.oneLine ·.text)"):
        "the interview after the game has ended, when nothing is hidden",
    ("Server/Seat.lean", "let some s := g.state | return"): "the interview after the game has ended",
    ("Server/Main.lean", "let ended := match g.state with"): "only whether the game has ended",
    ("Server/Main.lean", "let s := (if e.game.ended then g.state else g.seenBy none).getD (emptyBoard g.spec)"):
        "a replay's scene shows the true state only once the whole game has ended",
    ("Server/Main.lean", 'if e.game.state.isNone then return ← respondErr "The game has not started."'): "only whether it started",
    ("Server/Main.lean", "match e.game.state with"): "only the phase, to refuse a suggestion",
    ("Server/Bots.lean", "match g.state with"): "in a game that hides something, each bot is given its own observation",
    ("Server/Player.lean", "match g.state with"): "the rule-based seats decide from Player.situation, which observes",
}

# Every route, and what it sends. "observe" means its state goes through observe.
ROUTES = {
    '["api", "games"]': "the list of tables, only for tests and spectate runs",
    '["api", "games", code]': "a table's summary: its phase and seat count",
    '"view", false': "observe: View.view, through Game.seenBy; a replay hides until the whole game has ended",
    '"talk", false': "Talk.canSee: public talk, the viewer's own private lines, and confessions only for spectators of a table with no people",
    '"talk", true': "writes talk",
    '"scene", false': "observe: the scene is drawn from Game.seenBy",
    '"draft", false': "observe: the draft's preview is View.reviewJson, through Game.seenBy",
    '"draft", true': "observe: the clerk's prompt is built from Game.seenBy",
    '"suggest", true': "observe: the clerk's prompt is built from Game.seenBy and the seat's own chronicle",
    '"draft-cancel", true': "sends nothing about the game",
    '"draft-clear", true': "sends nothing about the game",
    '"events", false': "the log, with sealed numbers left out until the game ends: View.eventSeen. The dice are not in the log",
    '"join", true': "the seat and its token",
    '"bot", true': "the seat",
    '"claude", true': "the seat",
    '"start", true': "the version",
    '"move", true': "the version, or why it was refused: View.explain, through Game.seenBy",
    '"propose", true': "the version, or why it was refused",
    '"check", true': "observe: View.checkText, through Game.seenBy",
    '"vote", true': "the version, or why it was refused",
    '"sign", true': "the version, or why it was refused",
    '"exit", true': "the version, or why it was refused",
    '["api", "island"]': "the empty board",
    '["api", "defs"]': "the games",
    '["api", "defs", id, "scene"]': "an empty board",
    '["api", "version"]': "the build and a count of tables",
    '["assets", name]': "a pack's mesh file",
}


def check_code():
    found = set()
    for rel in OUTPUT_FILES:
        for n, line in enumerate(open(os.path.join(ROOT, rel), encoding="utf-8"), 1):
            text = line.strip()
            if text.startswith("--") or not TRUE_STATE.search(line):
                continue
            key = (rel, text)
            if key not in ALLOWED and (rel, line.rstrip("\n")) not in ALLOWED:
                raise SystemExit(f"FAILED: {rel}:{n} reads the true state, and the check does not know why that is safe:\n  {text}\n"
                                 "Read it through Game.seenBy or observe, or add it to ALLOWED with the reason.")
            found.add(key if key in ALLOWED else (rel, line.rstrip("\n")))
    stale = [k for k in ALLOWED if k not in found]
    check(not stale, f"every read of the true state in the {len(OUTPUT_FILES)} files that build what is sent has a reason ({len(found)} reads)")
    if stale:
        raise SystemExit(f"stale entries: {stale}")


def check_routes():
    src = open(os.path.join(ROOT, "Server/Main.lean"), encoding="utf-8").read()
    body = src[src.index("def route "):src.index("def handler ")]
    top = re.findall(r'^  \| (\[[^\]]*\])', body, re.M)
    actions = re.findall(r'^    \| ("[a-z-]+", (?:true|false))', body, re.M)
    routes = [r for r in top if r != '["api", "games", code, action]'] + actions
    missing = [r for r in routes if r not in ROUTES]
    gone = [r for r in ROUTES if r not in routes]
    if missing:
        raise SystemExit(f"FAILED: these routes are not in ROUTES, so nobody has said what they send: {missing}")
    if gone:
        raise SystemExit(f"FAILED: ROUTES lists routes that no longer exist: {gone}")
    check(True, f"all {len(routes)} routes are listed with what they send")


def play_high_card(srv):
    """Two people play High Card over HTTP. Each bets one more chip than its seat number."""
    code = srv.post("/api/games", {"seats": 2, "game": "high-card"})["code"]
    tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 7 + i})["token"] for i, n in enumerate(["Ada", "Ben"])]
    view = lambda i: srv.get(f"/api/games/{code}/view?token={tokens[i]}")
    post = lambda i, action, body: srv.post(f"/api/games/{code}/{action}", dict(body, token=tokens[i]))
    checked = 0
    bet = set()
    for _ in range(400):
        v0, v1, spec = view(0), view(1), srv.get(f"/api/games/{code}/view")
        for me, v in ((0, v0), (1, v1), (None, spec)):
            other = [s for s in v["seats"] if s["seat"] != me]
            if v["phase"] == "ended":
                continue
            assert all("card" not in s.get("hand", {}) for s in other), f"seat {me} sees another seat's card"
            assert "card" not in v.get("bank", {}) and "card" not in v.get("treasury", {}), f"seat {me} sees the bank's cards"
            assert all(r["seat"] == me for r in v["declarations"]["rows"]), f"seat {me} sees another seat's bet"
            if v["phase"] == "actions" and v["turn"] != me:
                assert v["lastRoll"] is None, f"seat {me} sees another seat's roll"
            mine = None if me is None else ["Ada", "Ben"][me]
            for line in v["chronicle"]:
                m = re.match(r"(\w+) rolled (\d+)", line["text"])
                assert not m or m.group(1) == mine, f"seat {me} is told another seat's roll: {line['text']}"
        checked += 1
        if v0["phase"] == "ended":
            break
        turn = v0["turn"]
        vt = v0 if turn == 0 else v1
        if vt["phase"] == "setup":
            place = next((m["move"] for m in vt["legalMoves"] if m["move"]["t"] == "place"), None)
            post(turn, "move", {"move": place or {"t": "endTurn"}})
        elif (vt["round"], turn) not in bet:
            bet.add((vt["round"], turn))
            check_ok = post(turn, "move", {"move": {"t": "declare", "res": "chips", "n": turn + 1}})["ok"]
            assert check_ok, "a seat can declare its bet"
        else:
            post(turn, "move", {"move": {"t": "endTurn"}})
    check(checked > 20, f"neither seat, nor a spectator, saw another seat's card, bet or roll, at any of {checked} moments of a High Card game")
    return code, tokens


def replay_and_events(srv, code, tokens):
    v = srv.get(f"/api/games/{code}/view")
    check(v["phase"] == "ended", "the game of High Card ended")
    check(all("card" in s["hand"] for s in v["seats"]), "after the end, everyone sees every hand")
    events = srv.get(f"/api/games/{code}/events")
    bets = [e for e in events if e.get("t") == "move" and e["move"]["t"] == "declare"]
    check(bets and all(isinstance(e["move"]["n"], int) for e in bets), "after the end, the log shows every bet")


def replay_while_running(srv):
    """A replay of a game still being played hides what a spectator may not see."""
    code = srv.post("/api/games", {"seats": 2, "game": "high-card"})["code"]
    tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 3 + i})["token"] for i, n in enumerate(["Cy", "Di"])]
    post = lambda i, action, body: srv.post(f"/api/games/{code}/{action}", dict(body, token=tokens[i]))
    for _ in range(20):
        v = srv.get(f"/api/games/{code}/view?token={tokens[0]}")
        if v["phase"] == "actions" and v["turn"] == 0:
            break
        vt = srv.get(f"/api/games/{code}/view?token={tokens[v['turn']]}")
        place = next((m["move"] for m in vt["legalMoves"] if m["move"]["t"] == "place"), None) if vt["phase"] == "setup" else None
        post(v["turn"], "move", {"move": place or {"t": "endTurn"}})
    post(0, "move", {"move": {"t": "declare", "res": "chips", "n": 2}})
    n = len(srv.get(f"/api/games/{code}/events"))
    r = srv.get(f"/api/games/{code}/view?at={n}")
    check(all("card" not in s.get("hand", {}) for s in r["seats"]) and r["lastRoll"] is None and not r["declarations"]["rows"],
          "a replay of a running game shows no card, roll or bet")
    events = srv.get(f"/api/games/{code}/events")
    check(all(e["move"]["n"] is None for e in events if e.get("t") == "move" and e["move"]["t"] == "declare"),
          "while the game runs, the log shows no bet")
    check(srv.get(f"/api/games/{code}/view?token={tokens[0]}")["declarations"]["rows"] == [{"seat": 0, "res": "chips", "n": 2}],
          "a seat sees its own bet")
    trade = post(0, "move", {"move": {"t": "bankTrade", "give": "chips", "get": "card"}})
    check(not trade["ok"], "the bank will not sell a hidden card")


def main():
    check_code()
    check_routes()
    data = tempfile.mkdtemp(prefix="charter-secrecy-")
    srv = Server(free_port(), data)
    try:
        code, tokens = play_high_card(srv)
        replay_and_events(srv, code, tokens)
        replay_while_running(srv)
    finally:
        srv.stop()
        shutil.rmtree(data, ignore_errors=True)
    print("secrecy check passed")


if __name__ == "__main__":
    main()
