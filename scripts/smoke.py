#!/usr/bin/env python3
"""Plays full games through the HTTP API, and checks the result: one human and three bots, tables of
bots on both games, Claude seats with no key, table talk, replay, the turn timer and vote pacing.

It starts its own server on a free port with a temporary data folder, and stops it at the end.
It uses only moves the server lists as legal. It also restarts the server to check that the game
replays from its log, and checks each scene stream when Node is available.
"""
import hashlib, json, os, shutil, socket, sqlite3, subprocess, sys, tempfile, time, urllib.error, urllib.request

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, ".lake", "build", "bin", "charter-server")
SCENES = []


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class Server:
    def __init__(self, port, data, stderr=None, hold=0, turn_ms=None):
        env = dict(os.environ, PORT=str(port), CHARTER_ROOT=ROOT, CHARTER_LIST_GAMES="1", CHARTER_DATA=data, CHARTER_BOT_DELAY_MS="0", CHARTER_VOTE_HOLD_MS=str(hold),
                   ANTHROPIC_API_KEY="", CHARTER_ENV_FILE=os.path.join(data, "no-such-file"))
        env.pop("CHARTER_COMMIT", None)
        if turn_ms is not None:
            env["CHARTER_TURN_MS"] = str(turn_ms)
        self.port = port
        self.proc = subprocess.Popen([BIN], env=env, stdout=subprocess.DEVNULL, stderr=stderr)
        for _ in range(200):
            try:
                self.raw("/api/games")
                return
            except OSError:
                time.sleep(0.05)
        raise SystemExit("the server did not start")

    def raw(self, path, body=None):
        data = None if body is None else json.dumps(body).encode()
        req = urllib.request.Request(f"http://127.0.0.1:{self.port}{path}", data=data,
                                     headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=60) as r:
            return r.read()

    def get(self, path):
        return json.loads(self.raw(path))

    def post(self, path, body):
        return json.loads(self.raw(path, body))

    def stop(self):
        self.proc.terminate()
        self.proc.wait(timeout=10)


def check(ok, what):
    if not ok:
        raise SystemExit(f"FAILED: {what}")
    print(f"ok: {what}")


def version_route(srv, code, token):
    """`/api/version` names the build and counts the tables, and says nothing about any one table."""
    with urllib.request.urlopen(f"http://127.0.0.1:{srv.port}/api/version", timeout=60) as r:
        cache, body = r.headers["Cache-Control"], r.read().decode()
    v = json.loads(body)
    check(set(v) == {"commit", "webBuild", "uptimeMs", "restoreMs", "tables"}, "the version route has its fields and no others")
    check(v["commit"] == "unknown", "with no CHARTER_COMMIT the commit is unknown")
    check(f'/v/{v["webBuild"]}/' in srv.raw("/").decode(), "the version route names the web build the page uses")
    check(isinstance(v["uptimeMs"], int) and v["uptimeMs"] >= 0, "the version route gives the uptime")
    check(v["restoreMs"] is None, "with no mirror there is no restore time")
    check(v["tables"] == len(srv.get("/api/games")) and v["tables"] >= 1, "the version route counts the tables")
    check(code not in body and token not in body, "the version route has no table code or token")
    check(cache == "no-store", "the version route is not stored")


def buy_from_a_bot(srv, code, post, v, you, need):
    """Offer a bot one of a spare resource for one of `need`, and wait for its answer. Bots take an
    offer that gives them at least what it asks. Returns whether the seat now has more of `need`."""
    hand = v["seats"][you]["hand"]
    spare = sorted((k for k, n in hand.items() if n > 0 and k not in ("grain", "wool")), key=lambda k: -hand[k])
    spare += sorted((k for k, n in hand.items() if n > 1 and k in ("grain", "wool") and k != need), key=lambda k: -hand[k])
    sellers = [s["seat"] for s in v["seats"] if s["seat"] != you and s["hand"][need] > 0]
    if not spare or not sellers:
        return False
    offer = {"t": "offer", "to": sellers[0], "give": [{"res": spare[0], "n": 1}], "get": [{"res": need, "n": 1}]}
    if not post("move", {"move": offer})["ok"]:
        return False
    for _ in range(200):
        now = srv.get(f"/api/games/{code}/view?token={v['token']}")
        if now["seats"][you]["hand"][need] > hand[need]:
            return True
        if not any(o["from"] == you for o in now["offers"]) and now["turn"] == you:
            return False
        time.sleep(0.005)
    for o in srv.get(f"/api/games/{code}/view?token={v['token']}")["offers"]:
        if o["from"] == you:
            post("move", {"move": {"t": "cancel", "id": o["id"]}})
    return False


def settle_value(m):
    """How much a corner pays, with most weight on grain and wool."""
    return sum(y["pips"] * (3 if y["res"] in ("grain", "wool") else 1) for y in m.get("yields", []))


def play(srv, code, token):
    """Play the human seat until the game ends, using laws, deals, offers and trades on the way. The
    seat settles where the dice pay and saves its resources until it has proposed everything, because
    the bots can win in about thirteen rounds. Trades with the bank and with bots get it what is short."""
    did = {"law": False, "piece": False, "deal": False, "form": False, "offer": False, "built": False, "setupEnd": False}
    post = lambda action, body: srv.post(f"/api/games/{code}/{action}", dict(body, token=token))
    deadline = time.time() + 300
    seen = -1
    asked_this_turn = 0
    turn_seen = None
    while time.time() < deadline:
        v = srv.get(f"/api/games/{code}/view?token={token}")
        if v["phase"] == "ended":
            return v, did
        if v["version"] != seen:
            seen = v["version"]
            picks = [m["pick"] for m in v["legalMoves"] if m["pick"] is not None]
            SCENES.append((srv.raw(f"/api/games/{code}/scene?token={token}"), picks, []))
        you = v["you"]
        for p in v["proposals"]:
            if p["canVote"]:
                post("vote", {"id": p["id"], "yes": True})
            if p["canSign"]:
                post("sign", {"id": p["id"]})
        if v["turn"] != you:
            time.sleep(0.005)
            continue
        moves = v["legalMoves"]
        turn_key = (v.get("round"), v["turn"], v.get("rollsMade"))
        if turn_key != turn_seen:
            turn_seen = turn_key
            asked_this_turn = 0
        if v["phase"] == "actions":
            hand = v["seats"][you]["hand"]
            other = (you + 1) % len(v["seats"])
            rich = [k for k, n in hand.items() if n >= 3]
            if not did["law"] or not did["piece"]:
                if hand["grain"] >= 1 and hand["wool"] >= 1:
                    key = "law" if not did["law"] else "piece"
                    sample = "bank-rate" if key == "law" else "lighthouse"
                    check(post("propose", {"sample": sample})["ok"], f"the sample law {sample} can be proposed")
                    did[key] = True
                    continue
                need = "grain" if hand["grain"] < 1 else "wool"
                trade = [m for m in moves if m["move"]["t"] == "bankTrade" and m["move"]["get"] == need]
                if trade:
                    check(post("move", {"move": trade[0]["move"]})["ok"], "a legal bank trade is accepted")
                    continue
                if asked_this_turn < 2:
                    asked_this_turn += 1
                    if buy_from_a_bot(srv, code, post, dict(v, token=token), you, need):
                        check(True, f"a bot sold this seat the {need} it needed")
                        continue
            if not did["offer"] and rich:
                offer = {"t": "offer", "to": None, "give": [{"res": rich[0], "n": 1}], "get": [{"res": rich[0], "n": 1}]}
                check(post("move", {"move": offer})["ok"], "an offer can be made")
                did["offer"] = True
                continue
            if not did["deal"] and rich:
                text = (f'(deal "A gift" (signers {you} {other}) (rounds 2) (exit-notice 0) '
                        f'(deposits ({you} {rich[0]} 3)) (every-round (pay {you} {other} {rich[0]} 1)))')
                check(post("propose", {"text": text})["ok"], "a funded deal can be proposed from the formal text")
                did["deal"] = True
                continue
            if not did["form"] and rich:
                form = {"with": other, "give": [{"res": rich[0], "n": 1}], "get": [], "rounds": 1, "exitNotice": 0}
                check(post("propose", {"dealForm": form})["ok"], "a deal can be proposed from the form")
                did["form"] = True
                continue
        place = [m for m in moves if m["move"]["t"] == "place"]
        # Promise IX: a seat can always end its turn, even in setup with a free piece still to place. The
        # page hides End turn then (setupPieceWaiting in web/app.js), so the server's list must not change.
        if v["phase"] == "setup" and place and not did["setupEnd"]:
            check(any(m["move"]["t"] == "endTurn" for m in moves), "in setup the server still lists end turn beside a free piece")
            did["setupEnd"] = True
        attach = [m for m in place if m["move"]["kind"] == "lighthouse"]
        spots = sorted(place, key=settle_value, reverse=True)
        chosen = (attach or spots)[:1]
        # Build only once everything is proposed. Setup pieces are free, so they do not count.
        saving = v["phase"] == "actions" and not all(did[k] for k in ("law", "piece", "deal", "form", "offer"))
        if chosen and not saving:
            r = post("move", {"move": chosen[0]["move"]})
            if not r["ok"]:
                raise SystemExit(f"FAILED: a listed legal move was rejected: {chosen[0]} {r}")
            continue
        r = post("move", {"move": {"t": "endTurn"}})
        if not r["ok"]:
            raise SystemExit(f"FAILED: end turn was rejected: {r}")
    raise SystemExit("FAILED: the game did not end in time")


def bots_only(srv, seats, game="island", small="settlement"):
    """A table of bots plays by itself to the end."""
    code = srv.post("/api/games", {"seats": seats, "game": game})["code"]
    for _ in range(seats):
        check(srv.post(f"/api/games/{code}/bot", {})["ok"], "a bot can join")
    deadline = time.time() + 300
    while time.time() < deadline:
        v = srv.get(f"/api/games/{code}/view")
        if v["phase"] == "ended":
            w = v["seats"][v["winner"]]
            pieces = [p for p in v["pieces"] if p["kind"] == small]
            check(True, f"{seats} bots finished {game}: {w['name']} won with {w['points']} points in round {v['round']}, with {len(pieces)} {small}s on the board")
            return code, v
        time.sleep(0.05)
    raise SystemExit(f"FAILED: {seats} bots did not finish")


def extension_pack(srv):
    """Not Catan: a pack with founding laws. Its laws are in force from the first view, its seats are
    limited, a counter stays off the screen, and bots play it to the end. Returns a table to check after
    a restart."""
    defs = {d["id"]: d for d in srv.get("/api/defs")}
    check(list(defs) == ["island", "not-catan", "slime-parliament", "ai-bubble", "strike-the-earth", "pirate-republic", "omerta"], "the lobby lists the base game first, then the packs")
    check(all(d["name"] and d["blurb"] for d in defs.values()), "each pack has a name and a sentence")
    check(defs["not-catan"]["minSeats"] == 3 and defs["not-catan"]["maxSeats"] == 4, "a pack says how many seats it supports")
    for n in (2, 5):
        check(srv.post("/api/games", {"seats": n, "game": "not-catan"})["ok"] is False, f"Not Catan refuses a table of {n}")
    t = srv.post("/api/games", {"seats": 3, "game": "not-catan"})["code"]
    token = srv.post(f"/api/games/{t}/join", {"name": "Mara", "nonce": 1})["token"]
    srv.post(f"/api/games/{t}/bot", {})
    check(srv.post(f"/api/games/{t}/start", {"token": token})["ok"] is False, "Not Catan cannot start with 2 of its 3 seats")
    srv.post(f"/api/games/{t}/bot", {})
    v = srv.get(f"/api/games/{t}/view?token={token}")
    check(v["game"]["name"] == "Not Catan" and v["game"]["blurb"], "the view names the pack")
    check(len(v["laws"]) == 4 and all(l["description"]["status"] == "pack" and l["description"]["text"] and l["by"] is None for l in v["laws"]), "founding laws are in force from the start, in the pack's own words")
    check([l["id"] for l in v["laws"]] == list(range(4)), "founding laws take the first ids")
    check(sum(l["text"].startswith("In force from the founding") for l in v["chronicle"]) == 4, "the chronicle states each founding law")
    check("laurel" in v["resources"], "a good a piece costs is on the screen")
    check("marksUp" not in v, "the view has no mark by the dice")
    check(all(y["number"] != 7 for m in v["legalMoves"] for y in m.get("yields", [])), "no corner pays on a 7")
    check(len(v["board"]["tiles"]) == 19 and sum(1 for x in v["board"]["tiles"] if x["res"] is None) == 1, "the board has 19 hexes and one desert")
    scene = srv.raw(f"/api/games/{t}/scene?token={token}")
    picks = [x["pick"] for x in v["legalMoves"] if x["pick"] is not None]
    SCENES.append((scene, picks, ["Law 0", "Law 3"]))
    code = None
    for n in (3, 4):
        code, end = bots_only(srv, n, "not-catan", "settlement")
        check(end["target"] == 10 and end["bankRate"] == 4, "the pack keeps its target and bank rate")
        check(end["bank"].get("timber", 0) + sum(s["hand"]["timber"] for s in end["seats"]) + end["treasury"].get("timber", 0) == 19, "19 timber are in the game, wherever they are")
        sevens = [l["text"] for l in end["chronicle"] if l["text"].endswith("rolled 7.")]
        paid = [l["text"] for l in end["chronicle"] if l["text"].startswith("By law") and ", on a 7," in l["text"]]
        check(len(sevens) > 0, f"bots saw {len(sevens)} sevens, and {len(paid)} of them cost a big hand")
    return code


def second_game(srv):
    """Slime Parliament is a different game: other resources, pieces and laws. Bots play it to the end at
    each table size, and its scenes draw. Returns a table to check after a restart."""
    check(srv.post("/api/games", {"seats": 4, "game": "no-such-game"})["ok"] is False, "a table cannot play a game that does not exist")
    code = None
    for n in (2, 4):
        code, v = bots_only(srv, n, "slime-parliament", "node")
        check(v["game"]["id"] == "slime-parliament" and v["resources"] == ["oatmeal", "dew", "rot", "pollen"], "the view says which game this is")
        check({d["name"] for d in v["pieceDefs"]} >= {"tendril", "node", "swelling", "puffball"}, "the view lists the game's own pieces")
        SCENES.append((srv.raw(f"/api/games/{code}/scene"), [], []))
    t = srv.post("/api/games", {"seats": 2, "game": "slime-parliament"})["code"]
    token = srv.post(f"/api/games/{t}/join", {"name": "Mara", "nonce": 1})["token"]
    srv.post(f"/api/games/{t}/join", {"name": "Ada", "nonce": 2})
    v = srv.get(f"/api/games/{t}/view?token={token}")
    m = [x for x in v["legalMoves"] if x["move"]["t"] == "place"]
    picks = [x["pick"] for x in m if x["pick"] is not None]
    check(len(picks) > 0, "the game offers places to build")
    SCENES.append((srv.raw(f"/api/games/{t}/scene?token={token}"), picks, []))
    r = srv.post(f"/api/games/{t}/check", {"token": token, "text": '(law "x" (set-cost tendril (bundle (grain 1))))'})
    check(r["ok"] is False and "oatmeal, dew, rot and pollen" in r["error"] if "error" in r else False, "a law in this game cannot name the Island's resources")
    r = srv.post(f"/api/games/{t}/check", {"token": token, "text": '(law "x" (set-cost tendril (bundle (dew 1))))'})
    check(r["ok"] is True and not r["problems"], "a law in this game can name its own resources")
    return code


def slime_pack(srv):
    """A reskin: its look reaches the browser as data, its mesh files come by hash, and bots play it to the end."""
    d = next(x for x in srv.get("/api/defs") if x["id"] == "slime-parliament")
    check("oatmeal" in d["look"]["icons"] and d["look"]["tokens"]["vellum"].startswith("#"), "a pack's icons and colours are in the list of games")
    check(srv.raw("/api/defs/slime-parliament/scene")[:4] == b"GPC1", "a pack has a backdrop for the title page")
    mesh_dir = os.path.join(ROOT, "packs", "slime-parliament", "meshes")
    names = sorted(os.listdir(mesh_dir))
    check(names and all(hashlib.sha256(open(os.path.join(mesh_dir, n), "rb").read()).hexdigest() + ".mesh" == n for n in names), "each mesh file is named by its hash")
    with urllib.request.urlopen(f"http://127.0.0.1:{srv.port}/assets/{names[0]}", timeout=60) as r:
        check("immutable" in r.headers["Cache-Control"] and r.read()[:4] == b"GPM1", "a mesh file is served at a path made from its hash, and can be kept for ever")
    for bad in ("0" * 64 + ".mesh", "..%2f..%2fMakefile", names[0][:-5]):
        try:
            srv.raw(f"/assets/{bad}")
            check(False, f"no mesh file is served for {bad}")
        except urllib.error.HTTPError as e:
            check(e.code == 404, f"no mesh file is served for {bad}")
    code = None
    for n in (2, 4):
        code, v = bots_only(srv, n, "slime-parliament", "node")
        check(v["game"]["id"] == "slime-parliament" and v["resources"] == ["oatmeal", "dew", "rot", "pollen"], "the view says which game this is")
        check(v["look"]["icons"] and "tendril" in v["look"]["quietPieces"], "the view carries the pack's look")
        check(len(v["laws"]) >= 4, "the founding laws stand")
        SCENES.append((srv.raw(f"/api/games/{code}/scene"), [], ["Law 0"]))
    return code


def bubble_pack(srv):
    """The AI Bubble: its laws fire with bots, and hype and the bubble are on the screen."""
    d = next(x for x in srv.get("/api/defs") if x["id"] == "ai-bubble")
    check("hype" in d["look"]["icons"] and "bubble" in d["look"]["icons"], "the pack draws its goods")
    check(srv.raw("/api/defs/ai-bubble/scene")[:4] == b"GPC1", "the pack has a backdrop for the title page")
    code = None
    for n in (3, 4):
        code, v = bots_only(srv, n, "ai-bubble", "datacenter")
        check(v["game"]["id"] == "ai-bubble" and {"hype", "bubble", "inference"} <= set(v["resources"]), "hype, the bubble and inference are on the screen")
        check(len(v["laws"]) >= 4, "the founding laws stand")
        check(v["round"] <= 10, "the game ends within its 10 rounds")
        SCENES.append((srv.raw(f"/api/games/{code}/scene"), [], ["Law 0"]))
    return code


def strike_pack(srv):
    """A second reskin, with goods no hex pays. Its laws stand, its score is renown, and bots play it to the end."""
    d = next(x for x in srv.get("/api/defs") if x["id"] == "strike-the-earth")
    check("renown" in d["look"]["icons"] and "danger" in d["look"]["icons"], "the pack draws its score and its danger")
    for n in (2, 4):
        code, v = bots_only(srv, n, "strike-the-earth", "hall")
        check(v["game"]["id"] == "strike-the-earth" and "renown" in v["resources"] and "danger" in v["resources"], "renown and danger are on the screen")
        check(len(v["laws"]) >= 4 and v["worth"] == [{"res": "renown", "points": 1}], "the founding laws stand, and renown is worth a point")
        check(v["treasury"]["danger"] >= v["round"] - 1, "the danger rose with the rounds")
        SCENES.append((srv.raw(f"/api/games/{code}/scene"), [], ["Law 0"]))


def pirate_pack(srv):
    """The Pirate Republic: its mesh files are served, and bots play it to the end. The Navy burns a wharf."""
    d = next(x for x in srv.get("/api/defs") if x["id"] == "pirate-republic")
    check("hat" in d["look"]["icons"], "the hat has its own mark")
    code, v = bots_only(srv, 4, "pirate-republic", "wharf")
    check(v["round"] <= 10 and len(v["laws"]) >= 4, "the pack ends by round 10 with its laws in force")
    check(any("lost a wharf" in (l if isinstance(l, str) else l.get("text", "")) for l in v["chronicle"]), "the Navy burns a wharf at the end of round 5")
    SCENES.append((srv.raw(f"/api/games/{code}/scene"), [], ["Law 0"]))


def omerta_pack(srv):
    """Omertà: bots play it to the end. Rolls and rackets fill the reward, and rackets pay their owners."""
    d = next(x for x in srv.get("/api/defs") if x["id"] == "omerta")
    check("dirt" in d["look"]["icons"] and "racket" in d["look"]["icons"], "dirt and the racket have their own marks")
    check(d["look"]["tagline"] == "Everybody swears. Somebody talks.", "the tagline is the pack's own")
    code, v = bots_only(srv, 4, "omerta", "front")
    check(v["round"] <= 8 and len(v["laws"]) >= 3, "the pack ends by round 8 with its laws in force")
    check(v["treasury"]["cash"] >= 8 * 4 - 4, "every roll put cash in the reward")
    check({"dirt", "cash"} <= set(v["resources"]), "dirt and cash are on the screen")
    SCENES.append((srv.raw(f"/api/games/{code}/scene"), [], ["Law 0"]))


def claude_with_no_key(srv):
    """With no key a Claude seat still plays: it falls back to safe legal actions, and the game ends.
    This makes no network call."""
    code = srv.post("/api/games", {"seats": 2})["code"]
    token = srv.post(f"/api/games/{code}/claude", {})
    check(token["ok"], "a Claude seat can join")
    srv.post(f"/api/games/{code}/claude", {})
    deadline = time.time() + 120
    while time.time() < deadline:
        v = srv.get(f"/api/games/{code}/view")
        if v["phase"] == "ended":
            break
        time.sleep(0.05)
    check(v["phase"] == "ended", f"Claude seats with no key play safely to the end, in round {v.get('round')}")
    check(all(s["kind"] == "claude" and s["points"] >= 1 for s in v["seats"]), "each seat placed its setup pieces")
    return code


def talk_and_replay(srv, code, token, last):
    """Talk is no game event, and a replay shows the game as it was."""
    before = srv.get(f"/api/games/{code}/view?token={token}")["version"]
    check(srv.post(f"/api/games/{code}/talk", {"token": token, "text": "Good game."})["ok"], "a player can talk")
    check(srv.get(f"/api/games/{code}/view?token={token}")["version"] == before, "talk is not a game event")
    check(srv.get(f"/api/games/{code}/talk")["lines"][-1]["text"] == "Good game.", "a public line can be read")
    early = srv.get(f"/api/games/{code}/view?at=10")
    check(early["replay"] == {"at": 10, "total": before} and early["phase"] == "setup" and early["you"] is None, "a replay can show the game after any event")
    check(early["serverSeed"] is None, "a replay of a step before the end holds no seed")
    end = srv.get(f"/api/games/{code}/view?at={before}")
    check(end["pieces"] == last["pieces"] and end["chronicle"] == last["chronicle"], "the last step of a replay is the game")
    check(len(srv.raw(f"/api/games/{code}/scene?at=10")) > 1000, "a replay step can be drawn")
    SCENES.append((srv.raw(f"/api/games/{code}/scene?at=10"), [], []))


def turn_timer(data_root):
    """Only the server can end someone else's turn, when the turn's deadline passes."""
    data = tempfile.mkdtemp(prefix="charter-timer-", dir=data_root)
    srv = Server(free_port(), data, turn_ms=400)
    try:
        code = srv.post("/api/games", {"seats": 2})["code"]
        tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 3})["token"] for n in ("Mara", "Ada")]
        v = srv.get(f"/api/games/{code}/view?token={tokens[0]}")
        turn, other = v["turn"], 1 - v["turn"]
        check(v["turnLeftMs"] is not None and v["turnLeftMs"] <= 400, "the view says how long the turn has left")
        taken = len(v["chronicle"])
        try:
            r = srv.post(f"/api/games/{code}/force", {"token": tokens[other]})
        except urllib.error.HTTPError as e:
            r = {"ok": False, "status": e.code}
        check(r["ok"] is False, "no route lets a client force a turn")
        forged = srv.post(f"/api/games/{code}/move", {"token": tokens[other], "move": {"t": "forceEndTurn"}})
        check(forged["ok"] is False, "a client cannot send the timer's event as a move")
        ended = srv.post(f"/api/games/{code}/move", {"token": tokens[other], "move": {"t": "endTurn"}})
        check(ended["ok"] is False, "a seated client cannot end another seat's turn")
        v = srv.get(f"/api/games/{code}/view?token={tokens[0]}")
        check(v["turn"] == turn and "The timer ended" not in " ".join(l["text"] for l in v["chronicle"]), "the turn is still running")
        start = time.time()
        while time.time() - start < 5:
            v = srv.get(f"/api/games/{code}/view?token={tokens[0]}")
            if v["turn"] != turn:
                break
            time.sleep(0.01)
        waited = time.time() - start
        check(v["turn"] != turn and waited < 2, f"the timer ends an idle turn at its deadline, after {waited:.2f} s")
        check(any("The timer ended" in l["text"] for l in v["chronicle"][taken:]), "the chronicle says the timer ended it")
        events = srv.get(f"/api/games/{code}/events")
        check(sum(1 for e in events if e["t"] == "forceEndTurn") >= 1, "the event is in the public log, so a replay runs it")
    finally:
        srv.stop()


def vote_pacing(data_root):
    """Bots hold their votes on a law until the person at the table has voted, or a time limit passes.
    This starts its own server with a real limit, since the others use none."""
    data = tempfile.mkdtemp(prefix="charter-pacing-", dir=data_root)
    srv = Server(free_port(), data, hold=1500)
    try:
        code = srv.post("/api/games", {"seats": 3})["code"]
        token = srv.post(f"/api/games/{code}/join", {"name": "Mara", "nonce": 1})["token"]
        for _ in range(2):
            srv.post(f"/api/games/{code}/bot", {})
        post = lambda action, body: srv.post(f"/api/games/{code}/{action}", dict(body, token=token))
        laws = iter([("bank-rate", True), ("settlement-worth", False)])
        current = next(laws)
        done = set()
        deadline = time.time() + 120
        while time.time() < deadline and len(done) < 2:
            v = srv.get(f"/api/games/{code}/view?token={token}")
            if v["phase"] == "ended":
                raise SystemExit("FAILED: the pacing game ended before its two laws were tried")
            if v["turn"] != 0:
                time.sleep(0.01)
                continue
            moves = v["legalMoves"]
            if v["phase"] == "setup":
                place = sorted((m for m in moves if m["move"]["t"] == "place"), key=settle_value, reverse=True)
                post("move", {"move": (place[0] if place else {"move": {"t": "endTurn"}})["move"]})
                continue
            hand = v["seats"][0]["hand"]
            if hand["grain"] < 1 or hand["wool"] < 1:
                need = "grain" if hand["grain"] < 1 else "wool"
                trade = [m for m in moves if m["move"]["t"] == "bankTrade" and m["move"]["get"] == need]
                post("move", {"move": trade[0]["move"] if trade else {"t": "endTurn"}})
                continue
            sample, person_votes = current
            turn = v["turn"]
            check(post("propose", {"sample": sample})["ok"], f"the person proposes {sample}")
            pid = [p["id"] for p in srv.get(f"/api/games/{code}/view?token={token}")["proposals"] if p["by"] == 0][-1]
            started = time.time()
            if person_votes:
                while time.time() - started < 0.7:
                    p = [x for x in srv.get(f"/api/games/{code}/view")["proposals"] if x["id"] == pid][0]
                    check(not p["votes"], "no bot votes before the person") if time.time() - started > 0.65 else None
                    if p["votes"]:
                        raise SystemExit("FAILED: a bot voted before the person")
                    time.sleep(0.02)
                check(post("vote", {"id": pid, "yes": True})["ok"], "the person's vote is in time")
                while True:
                    w = srv.get(f"/api/games/{code}/view?token={token}")
                    if not any(x["id"] == pid for x in w["proposals"]) or len([x for x in w["proposals"] if x["id"] == pid][0]["votes"]) > 1:
                        break
                    if time.time() - started > 1.4:
                        raise SystemExit("FAILED: the bots did not vote soon after the person")
                    time.sleep(0.01)
                check(True, f"the bots vote as soon as the person has voted, after {time.time() - started:.1f} s, under the time limit")
            else:
                while True:
                    w = srv.get(f"/api/games/{code}/view?token={token}")
                    open_ = [x for x in w["proposals"] if x["id"] == pid]
                    if not open_ or open_[0]["votes"]:
                        break
                    if time.time() - started > 10:
                        raise SystemExit("FAILED: the bots waited past the time limit")
                    time.sleep(0.01)
                waited = time.time() - started
                check(waited >= 1.3, f"the bots wait for a silent person until the time limit: {waited:.1f} s")
            done.add(sample)
            current = next(laws, current)
            post("move", {"move": {"t": "endTurn"}})
        check(len(done) == 2, "both cases of vote pacing were tried")
    finally:
        srv.stop()


# Laws the constitution refuses, with words its answer must hold. The propose route must say so.
REFUSED_LAWS = [
    ('(law "x" (new-piece flag (bundle (ore 1)) (points 1) (attach road) (yield 0) (limit 1)))', "could never be built"),
    ('(law "x" (new-piece flag (bundle (ore 1)) (points 1) spot (yield 0) (limit 0)))', "could never be built"),
    ('(law "x" (on-round-end (transfer actor treasury grain 1)))', "does not exist where this rule runs"),
    ('(law "x" (on-round-end (for-each-player true (transfer each each grain 1))))', "moves nothing"),
    ('(law "x" (on-round-end (transfer bank treasury grain (/ 4 0))))', "divide by zero"),
    ('(law "x" (set-bank-rate 3) (set-bank-rate 5))', "same rule twice"),
    ('(law "x" (on-round-end (for-each-player true ' + "(transfer bank each grain 1) " * 45 + ')))', "too many payments"),
    ('(law "x" (on-roll (transfer each treasury grain 1)))', "does not exist where this rule runs"),
    ('(law "x" (on-roll (transfer actor treasury res 1)))', "does not exist where this rule runs"),
    ('(law "x" (on-roll (transfer bank bank grain 1)))', "moves nothing"),
    ('(law "x" (on-roll (transfer bank treasury grain (/ rolled 0))))', "divide by zero"),
    ('(law "x" (on-roll (for-each-player true ' + "(transfer bank each grain 1) " * 45 + ')))', "too many payments"),
]


class TableRanOut(Exception):
    """The rounds ran out before the table reached the state a test needs. The dice decide that."""


def on_fresh_tables(test):
    """Run a test that needs certain cards in hand. If a table's rounds run out first, try a new table. A test
    still fails if any of its checks fail, and also if no table reaches the state it needs."""
    def run(srv):
        for _ in range(8):
            try:
                return test(srv)
            except TableRanOut:
                continue
        raise SystemExit(f"FAILED: {test.__name__}: no table reached the state this test needs")
    return run


def end_turn_until(srv, code, tokens, ok):
    """Play turns with no building until `ok` holds for the view, and return that view."""
    for _ in range(400):
        v = srv.get(f"/api/games/{code}/view?token={tokens[0]}")
        if ok(v):
            return v
        if v["phase"] == "ended":
            raise TableRanOut()
        seat = v["turn"]
        vs = srv.get(f"/api/games/{code}/view?token={tokens[seat]}")
        place = [m for m in vs["legalMoves"] if m["move"]["t"] == "place"]
        move = place[0]["move"] if vs["phase"] == "setup" and place else {"t": "endTurn"}
        r = srv.post(f"/api/games/{code}/move", {"token": tokens[seat], "move": move})
        if not r["ok"]:
            raise SystemExit(f"FAILED: a turn was refused: {r}")
    raise SystemExit("FAILED: the table never reached the state this test needs")


def held(v, seat):
    return [k for k, n in v["seats"][seat]["hand"].items() if n > 0]


@on_fresh_tables
def griefer_findings_stay_fixed(srv):
    """What a griefer table found hard to read: a law that waits, dice rows, a tie, a deal's end, an empty bank."""
    code = srv.post("/api/games", {"seats": 3})["code"]
    tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 7})["token"] for n in ("Mara", "Ada", "Grace")]
    view = lambda i=0: srv.get(f"/api/games/{code}/view?token={tokens[i]}")
    propose = lambda i, text: check(srv.post(f"/api/games/{code}/propose", {"token": tokens[i], "text": text})["ok"], f"seat {i} proposes {text[:32]}")
    def preview(words):
        return next(p["preview"] for p in view()["proposals"] if words in p["text"])
    def pass_last():
        pid = view()["proposals"][-1]["id"]
        for i in range(2):
            check(srv.post(f"/api/games/{code}/vote", {"token": tokens[i], "id": pid, "yes": True})["ok"], "a yes vote counts")
    end_turn_until(srv, code, tokens, lambda v: v["phase"] == "actions")

    propose(0, '(law "Late tax" (on-round-end (for-each-player (<= 50 round) (transfer each treasury grain 1))))')
    sleeper = preview("Late tax")
    check(not sleeper["nothing"] and any("may act later" in n for n in sleeper["notes"]), "a law that reads the round says it may act later")
    propose(1, '(law "Stop now" (end-game))')
    v = view()
    points = [s["points"] for s in v["seats"]]
    if points.count(max(points)) > 1:
        check("earlier in turn order" in preview("Stop now")["ending"], "an ending decided by a tie says how")
    propose(2, '(law "Roller gift" (on-roll (transfer bank actor grain 1)))')
    check(all(s["when"].endswith(", compared with today") for s in preview("Roller gift")["sections"] if s["dice"]), "a dice section is worded as a comparison")
    pid = next(p["id"] for p in view()["proposals"] if "Stop now" in p["text"])
    check(srv.post(f"/api/games/{code}/vote", {"token": tokens[0], "id": pid, "yes": False})["ok"], "the end of the game is voted down")
    check(srv.post(f"/api/games/{code}/vote", {"token": tokens[1], "id": pid, "yes": False})["ok"], "by a majority")

    # The figures note comes only when a law's figures depend on declarations.
    propose(1, '(law "Grain auction" (on-round-end (for-each-player (< 0 (declared each grain)) (transfer each treasury grain 1))))')
    pass_last()
    end_turn_until(srv, code, tokens, lambda v: any(1 <= s["hand"]["grain"] <= 3 for s in v["seats"]) and not v["proposals"])
    propose(2, '(law "Bank rate" (set-bank-rate 3))')
    check(not any("declarations" in n for n in preview("Bank rate")["notes"]), "a law with nothing to do with declarations has no such note")
    propose(1, '(law "Grain levy" (on-round-end (for-each-player true (transfer each treasury grain 5))))')
    check(any("declarations" in n for n in preview("Grain levy")["notes"]), "a law whose figures depend on declarations says so")
    pass_last()

    # A deal's end, and a roll the bank cannot pay.
    propose(0, '(deal "Short" (signers 0 1) (rounds 1) (exit-notice 0) (deposits) (no-trade 0 1))')
    pid = view()["proposals"][-1]["id"]
    for i in (0, 1):
        check(srv.post(f"/api/games/{code}/sign", {"token": tokens[i], "id": pid})["ok"], "a signer signs")
    goods = " ".join(f"(transfer bank treasury {r} 1000)" for r in view()["resources"])
    propose(2, f'(law "Empty bank" (now {goods}))')
    pid = view()["proposals"][-1]["id"]
    for i in range(2):
        check(srv.post(f"/api/games/{code}/vote", {"token": tokens[i], "id": pid, "yes": True})["ok"], "a yes vote counts")
    text = lambda v: [l["text"] for l in v["chronicle"]]
    check(any(t.startswith('By law "Empty bank", the moment it passed,') for t in text(view())), "a decree's line names the law")
    end_turn_until(srv, code, tokens, lambda v: any("the bank had no" in t for t in text(v)) and any(t == "The deal between Mara and Ada ended." for t in text(v)))
    print("ok: the chronicle tells of a deal's end and of a roll the bank could not pay")


@on_fresh_tables
def a_roll_law_fires(srv):
    """Two people pass a law that pays the bank's grain on every roll, and it pays on the next one, to
    the seat whose turn that roll starts. The chronicle says so."""
    code = srv.post("/api/games", {"seats": 2})["code"]
    tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 7})["token"] for n in ("Mara", "Ada")]
    v = end_turn_until(srv, code, tokens, lambda v: v["phase"] == "actions" and all(v["seats"][v["turn"]]["hand"][k] >= 1 for k in ("grain", "wool")))
    a = v["turn"]
    b = 1 - a
    law = '(law "Roller gift" (on-roll (transfer bank actor grain 1)))'
    r = srv.post(f"/api/games/{code}/propose", {"token": tokens[a], "text": law})
    check(r["ok"], "a law that reacts to the roll can be proposed")
    vs = srv.get(f"/api/games/{code}/view?token={tokens[b]}")
    p = vs["proposals"][-1]
    check(p["text"] == law and p["description"] == {"status": "none"}, "a roll law typed by hand shows its source, and it has no description")
    check(srv.post(f"/api/games/{code}/vote", {"token": tokens[a], "id": p["id"], "yes": True})["ok"], "the proposer votes for it")
    check(srv.post(f"/api/games/{code}/vote", {"token": tokens[b], "id": p["id"], "yes": True})["ok"], "the other seat votes for it")
    before = srv.get(f"/api/games/{code}/view?token={tokens[a]}")
    check(len(before["laws"]) == 1, "the roll law is in force")
    grain = before["seats"][b]["hand"]["grain"]
    lines = len(before["chronicle"])
    check(srv.post(f"/api/games/{code}/move", {"token": tokens[a], "move": {"t": "endTurn"}})["ok"], "the turn ends")
    after = srv.get(f"/api/games/{code}/view?token={tokens[a]}")
    check(after["turn"] == b and after["seats"][b]["hand"]["grain"] > grain, "the next roll pays the seat whose turn it starts")
    text = " ".join(l["text"] for l in after["chronicle"][lines:])
    roll = after["lastRoll"]
    name = ["Mara", "Ada"][b]
    article = "an" if roll in (8, 11) else "a"
    check(f", on {article} {roll}, the bank paid {name} 1 grain." in text and "By law \"" in text, "the chronicle shows the law's payment, as one line, and names the law")
    check(any(l["major"] and l["text"].startswith("By law \"") for l in after["chronicle"][lines:]), "that line is one the screen tells")


@on_fresh_tables
def refusals_and_embargo(srv):
    """Three people at a table. The propose route refuses bad laws. Then one seat signs a promise not to
    trade with a seat that does not sign. Those two cannot trade, whichever offers. The seat that did
    not sign can trade with the third."""
    code = srv.post("/api/games", {"seats": 3})["code"]
    tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 7})["token"] for n in ("Mara", "Ada", "Grace")]
    v = end_turn_until(srv, code, tokens, lambda v: v["phase"] == "actions" and held(v, v["turn"]))
    a = v["turn"]
    b, c = (a + 1) % 3, (a + 2) % 3
    for text, why in REFUSED_LAWS:
        r = srv.post(f"/api/games/{code}/propose", {"token": tokens[a], "text": text})
        check(not r["ok"] and why in r["error"], f"the propose route refuses a law for: {why}")
    deal = f'(deal "Embargo" (signers {a} {b}) (rounds 30) (exit-notice 0) (deposits) (no-trade {a} {c}))'
    check(srv.post(f"/api/games/{code}/propose", {"token": tokens[a], "text": deal})["ok"], "a deal can name a seat that does not sign")
    v = srv.get(f"/api/games/{code}/view?token={tokens[b]}")
    pid = v["proposals"][-1]["id"]
    for signer in (a, b):
        check(srv.post(f"/api/games/{code}/sign", {"token": tokens[signer], "id": pid})["ok"], "a signer signs it")
    v = srv.get(f"/api/games/{code}/view?token={tokens[a]}")
    text = " ".join(l["text"] for l in v["chronicle"])
    check("The deal started." in text, "the deal started with two signatures, and the third seat did not sign")
    names = ["Mara", "Ada", "Grace"]
    check(f"{names[a]} will not trade with {names[c]}, in either direction." in text, "the chronicle says who will not trade with whom")
    give = [{"res": held(v, a)[0], "n": 1}]
    get = [{"res": "grain" if held(v, a)[0] != "grain" else "ore", "n": 1}]
    r = srv.post(f"/api/games/{code}/move", {"token": tokens[a], "move": {"t": "offer", "to": c, "give": give, "get": get}})
    check(not r["ok"], "the signer cannot make an offer to the seat it promised to avoid")
    r = srv.post(f"/api/games/{code}/move", {"token": tokens[a], "move": {"t": "offer", "to": None, "give": give, "get": get}})
    check(r["ok"], "the signer can make an open offer")
    v = srv.get(f"/api/games/{code}/view?token={tokens[c]}")
    r = srv.post(f"/api/games/{code}/move", {"token": tokens[c], "move": {"t": "accept", "id": v["offers"][-1]["id"]}})
    check(not r["ok"] and "forbids" in r["error"], "the seat that did not sign cannot accept the signer's offer")
    v = end_turn_until(srv, code, tokens, lambda v: v["turn"] == c and held(v, c) and [k for k in held(v, b) if k != held(v, c)[0]])
    give = held(v, c)[0]
    get = [k for k in held(v, b) if k != give][0]
    r = srv.post(f"/api/games/{code}/move", {"token": tokens[c], "move": {"t": "offer", "to": b, "give": [{"res": give, "n": 1}], "get": [{"res": get, "n": 1}]}})
    check(r["ok"], "the seat that did not sign can make an offer to another seat")
    v = srv.get(f"/api/games/{code}/view?token={tokens[b]}")
    r = srv.post(f"/api/games/{code}/move", {"token": tokens[b], "move": {"t": "accept", "id": v["offers"][-1]["id"]}})
    check(r["ok"], "the seat that did not sign can still trade with anyone else")
    return code


def five_kinds_in_hand(srv):
    """Two people at a table, one on their turn with all 5 resources in hand, and the other holding at
    least 2 each of 2 resources. Returns the table, the tokens, the seat on its turn and the other."""
    code = srv.post("/api/games", {"seats": 2})["code"]
    tokens = [srv.post(f"/api/games/{code}/join", {"name": n, "nonce": 7})["token"] for n in ("Mara", "Ada")]

    def ready(v):
        if v["phase"] != "actions":
            return False
        hand, rate = v["seats"][v["turn"]]["hand"], v["bankRate"]
        missing = sum(1 for n in hand.values() if n == 0)
        spare = sum((n - 1) // rate for n in hand.values() if n > 1)
        other = v["seats"][1 - v["turn"]]["hand"]
        return spare >= missing and sum(1 for n in other.values() if n >= 2) >= 2

    v = end_turn_until(srv, code, tokens, ready)
    a = v["turn"]
    for _ in range(5):
        hand = v["seats"][a]["hand"]
        gone = [k for k, n in hand.items() if n == 0]
        if not gone:
            break
        rich = max(hand, key=hand.get)
        r = srv.post(f"/api/games/{code}/move", {"token": tokens[a], "move": {"t": "bankTrade", "give": rich, "get": gone[0]}})
        check(r["ok"], "the bank trades for a resource the seat lacks")
        v = srv.get(f"/api/games/{code}/view?token={tokens[a]}")
    check(all(n > 0 for n in v["seats"][a]["hand"].values()), "a seat can come to hold all 5 resources")
    return code, tokens, a, 1 - a


def ones(kinds):
    return [{"res": k, "n": 1} for k in kinds]


@on_fresh_tables
def trades_of_several_resources(srv):
    """An offer and a deal can each carry several resources, up to 4 on each side, and a trade pays in full."""
    code, tokens, a, b = five_kinds_in_hand(srv)
    move = lambda seat, m: srv.post(f"/api/games/{code}/move", {"token": tokens[seat], "move": m})
    view = lambda: srv.get(f"/api/games/{code}/view?token={tokens[a]}")
    v = view()
    kinds = sorted(v["seats"][a]["hand"])
    check(v["maxGoodsPerSide"] == 4, "the view tells the page how many resources a side can carry")

    # The limit on offers: 4 different resources pass, on either side, and 5 are refused.
    r = move(a, {"t": "offer", "to": None, "give": ones(kinds[:4]), "get": ones(kinds[:4])})
    check(r["ok"], "an offer with 4 different resources on each side is accepted")
    offer = view()["offers"][-1]
    check(len(offer["give"]) == 4 and len(offer["get"]) == 4, "the offer keeps all 4 on each side")
    check(move(a, {"t": "cancel", "id": offer["id"]})["ok"], "the offer can be taken back")
    for give, get in ((kinds, kinds[:1]), (kinds[:1], kinds)):
        r = move(a, {"t": "offer", "to": None, "give": ones(give), "get": ones(get)})
        check(not r["ok"] and "at most 4 different resources" in r["error"], f"an offer with 5 different resources on one side is refused: {r.get('error')}")

    # A trade of two for two moves exactly those cards, and both sides read it in the chronicle.
    v = view()
    other = v["seats"][b]["hand"]
    want = sorted((k for k, n in other.items() if n >= 2), key=lambda k: -other[k])[:2]
    pay = [k for k in kinds if k not in want][:2]
    mine = dict(v["seats"][a]["hand"])
    theirs = dict(other)
    check(move(a, {"t": "offer", "to": b, "give": [{"res": pay[0], "n": 1}, {"res": pay[1], "n": 1}], "get": [{"res": want[0], "n": 2}, {"res": want[1], "n": 1}]})["ok"], "a two for two offer is made")
    oid = view()["offers"][-1]["id"]
    check(move(b, {"t": "accept", "id": oid})["ok"], "the other seat accepts the two for two offer")
    v = view()
    for k, d in ((pay[0], -1), (pay[1], -1), (want[0], 2), (want[1], 1)):
        mine[k] += d
        theirs[k] -= d
    check(v["seats"][a]["hand"] == mine and v["seats"][b]["hand"] == theirs, "both hands change by exactly the offer")
    check(not v["offers"], "the accepted offer is gone")
    line = v["chronicle"][-1]["text"]
    check(f"1 {pay[0]} and 1 {pay[1]} for 2 {want[0]} and 1 {want[1]}" in line, f"the chronicle names every resource: {line}")

    # Accepting pays in full or not at all.
    v = view()
    too_much = v["seats"][b]["hand"][want[1]] + 1
    check(move(a, {"t": "offer", "to": b, "give": ones(want[:1]), "get": [{"res": want[0], "n": 1}, {"res": want[1], "n": too_much}]})["ok"], "an offer can ask for more than a seat holds")
    oid = view()["offers"][-1]["id"]
    r = move(b, {"t": "accept", "id": oid})
    check(not r["ok"], "a seat cannot accept an offer it can pay only in part")
    now = view()["seats"]
    check(now[a]["hand"] == v["seats"][a]["hand"] and now[b]["hand"] == v["seats"][b]["hand"], "a refused acceptance moves nothing")
    check(move(a, {"t": "cancel", "id": oid})["ok"], "the offer is taken back")

    # A deal from the form takes the same lists, under the same limit.
    propose = lambda body: srv.post(f"/api/games/{code}/propose", {"token": tokens[a], **body})
    form = lambda give, get: {"dealForm": {"with": b, "give": ones(give), "get": ones(get), "rounds": 2, "exitNotice": 1}}
    for give, get in ((kinds, kinds[:1]), (kinds[:1], kinds)):
        r = propose(form(give, get))
        check(not r["ok"] and "at most 4 different resources" in r["error"], f"a deal form with 5 different resources on one side is refused: {r.get('error')}")
    pays = " ".join(f"(pay {a} {b} {k} 1)" for k in kinds)
    deposits = " ".join(f"({a} {k} 2)" for k in kinds)
    r = propose({"text": f'(deal "All five" (signers {a} {b}) (rounds 2) (exit-notice 0) (deposits {deposits}) (every-round {pays}))'})
    check(not r["ok"] and "at most 4 different resources" in r["error"], "the same deal sent as text is refused too")
    check(propose(form(kinds[:4], kinds[1:]))["ok"], "a deal form with 4 different resources on each side is accepted")
    deal = view()["proposals"][-1]
    check(deal["kind"] == "deal" and all(k in deal["english"] for k in kinds), "the deal names every resource")

    # A two for two deal starts, and sets aside what it says.
    v = view()
    rich = [k for k, n in v["seats"][a]["hand"].items() if n >= 2][:1]
    if rich:
        want = sorted((k for k, n in v["seats"][b]["hand"].items() if n >= 2 and k not in rich))[:1]
        if want:
            check(propose(form(rich, want))["ok"], "a deal that both seats can fund is proposed")
            pid = view()["proposals"][-1]["id"]
            before_a, before_b = dict(view()["seats"][a]["hand"]), dict(view()["seats"][b]["hand"])
            for s in (a, b):
                check(srv.post(f"/api/games/{code}/sign", {"token": tokens[s], "id": pid})["ok"], "a signer signs the deal from the form")
            v = view()
            check("The deal started." in " ".join(l["text"] for l in v["chronicle"]), "the deal from the form started")
            check(v["seats"][a]["hand"][rich[0]] == before_a[rich[0]] - 2 and v["seats"][b]["hand"][want[0]] == before_b[want[0]] - 2, "each signer sets aside its deposit")


@on_fresh_tables
def a_bot_takes_a_good_offer(srv):
    """A bot takes an offer of several resources that gives it at least what it gives."""
    code = srv.post("/api/games", {"seats": 2})["code"]
    r = srv.post(f"/api/games/{code}/join", {"name": "Human", "nonce": 7})
    token, you = r["token"], r["seat"]
    check(srv.post(f"/api/games/{code}/bot", {})["ok"], "a bot joins")
    move = lambda m: srv.post(f"/api/games/{code}/move", {"token": token, "move": m})
    view = lambda: srv.get(f"/api/games/{code}/view?token={token}")
    for _ in range(4000):
        v = view()
        if v["phase"] == "ended":
            raise TableRanOut()
        if v["turn"] != you:
            time.sleep(0.002)
            continue
        hand, bot = v["seats"][you]["hand"], v["seats"][1 - you]["hand"]
        wanted = [k for k, n in bot.items() if n > 0]
        offered = [k for k, n in hand.items() if n > 0 and k not in wanted[:1]]
        if v["phase"] == "actions" and wanted and len(offered) >= 2:
            give = ones(offered[:2])
            check(move({"t": "offer", "to": 1 - you, "give": give, "get": ones(wanted[:1])})["ok"], "a two for one offer goes to a bot")
            for _ in range(500):
                now = view()
                if now["seats"][you]["hand"][wanted[0]] == hand[wanted[0]] + 1:
                    check(all(now["seats"][you]["hand"][k] == hand[k] - 1 for k in offered[:2]), "the bot took the offer, and paid for it")
                    return
                time.sleep(0.005)
            raise SystemExit("FAILED: the bot did not take an offer that gives it more than it gives")
        place = [m for m in v["legalMoves"] if m["move"]["t"] == "place"]
        r = move(place[0]["move"] if v["phase"] == "setup" and place else {"t": "endTurn"})
        if not r["ok"]:
            raise SystemExit(f"FAILED: a turn was refused: {r}")
    raise TableRanOut()


@on_fresh_tables
def a_table_over_the_limit(srv):
    """A table where a seat holds all 5 resources. Returns what `add_offer_over_the_limit` writes to its log."""
    code, tokens, a, _ = five_kinds_in_hand(srv)
    kinds = sorted(srv.get(f"/api/games/{code}/view?token={tokens[a]}")["seats"][a]["hand"])
    event = {"t": "move", "seat": a, "move": {"t": "offer", "to": None, "give": ones(kinds), "get": ones(kinds[:1])}}
    return code, tokens[a], event


def add_offer_over_the_limit(data, code, event):
    """Add an event to a saved log, as an older version could have written it before the limit."""
    db = sqlite3.connect(os.path.join(data, f"{code}.db"))
    with db:
        seq = db.execute("SELECT MAX(seq) FROM events").fetchone()[0] + 1
        db.execute("INSERT INTO events (seq, body) VALUES (?, ?)", (seq, log_body(event)))
    db.close()


def log_body(event):
    """An event as the log stores it: a byte count in LEB128, then the JSON in UTF-8."""
    body = json.dumps(event).encode()
    n, head = len(body), bytearray()
    while n >= 128:
        head.append(n % 128 + 128)
        n //= 128
    head.append(n)
    return bytes(head) + body


def write_old_logs(data):
    """Two saved games as an older version could have left them: one holds a law the rules now refuse,
    and one holds a join with no nonce. Returns their codes."""
    create = {"t": "create", "seats": 2, "_serverSeed": 1}
    join = lambda n, nonce: {"t": "join", "name": n, "kind": "human", "_token": n, "nonce": nonce}
    bad_law = {"t": "propose", "seat": 0, "text": '(law "x" (on-round-end (transfer actor treasury grain 1)))'}
    logs = {
        "OLDLAW": [dict(create, code="OLDLAW"), join("A", 1), join("B", 2), {"t": "start"}, bad_law],
        "OLDNON": [dict(create, code="OLDNON"), {"t": "join", "name": "A", "kind": "human", "_token": "A"}],
    }
    for name, events in logs.items():
        db = sqlite3.connect(os.path.join(data, f"{name}.db"))
        with db:
            db.execute("CREATE TABLE events (seq INTEGER PRIMARY KEY, body BLOB NOT NULL)")
            db.execute("CREATE TABLE snapshots (seq INTEGER PRIMARY KEY, body BLOB NOT NULL)")
            for i, e in enumerate(events):
                db.execute("INSERT INTO events (seq, body) VALUES (?, ?)", (i, log_body(e)))
        db.close()
    return list(logs)


def check_scenes(data):
    node = shutil.which("node")
    if not node:
        print("skipped: scene decoding, because Node is not installed")
        return
    with tempfile.TemporaryDirectory() as d:
        files = []
        for i, (buf, picks, labels) in enumerate(SCENES):
            name = os.path.join(d, f"{i}.bin")
            with open(name, "wb") as f:
                f.write(buf)
            files.append({"file": name, "picks": picks, "labels": labels})
        with open(os.path.join(d, "list.json"), "w") as f:
            json.dump(files, f)
        r = subprocess.run([node, os.path.join(ROOT, "scripts", "check_scene.mjs"), os.path.join(d, "list.json")], capture_output=True, text=True)
        sys.stdout.write(r.stdout)
        sys.stderr.write(r.stderr)
        check(r.returncode == 0, f"{len(SCENES)} scene streams decode, and each legal pick has a marker")


def run_previews():
    r = subprocess.run([os.path.join(ROOT, ".lake", "build", "bin", "charter-sim"), "--check-previews"], capture_output=True, text=True)
    sys.stdout.write(r.stdout)
    check(r.returncode == 0, "law previews match what the engine then does, in real games")


class Tee:
    """Writes to the terminal and to a file, so that a failure's whole output is kept."""
    def __init__(self, stream, file):
        self.stream, self.file = stream, file

    def write(self, text):
        self.stream.write(text)
        self.file.write(text)
        self.file.flush()

    def flush(self):
        self.stream.flush()


def main_with_log():
    """A failure's full output goes to a temp file, and its path is the last thing printed."""
    fd, path = tempfile.mkstemp(prefix="charter-smoke-", suffix=".log")
    real_out, real_err = sys.stdout, sys.stderr
    with os.fdopen(fd, "w") as log:
        sys.stdout, sys.stderr = Tee(real_out, log), Tee(real_err, log)
        try:
            main()
        except BaseException:
            import traceback
            traceback.print_exc(file=log)
            log.flush()
            sys.stdout, sys.stderr = real_out, real_err
            print(f"smoke failed. Its full output is in {path}", file=sys.stderr)
            raise
        finally:
            sys.stdout, sys.stderr = real_out, real_err
    os.unlink(path)


def main():
    if not os.path.exists(BIN):
        raise SystemExit("run make install first")
    data = tempfile.mkdtemp(prefix="charter-smoke-")
    port = free_port()
    srv = Server(port, data)
    try:
        check(b"charter" in srv.raw("/").lower(), "the server serves the web page")
        check(len(srv.raw("/vendor/player.js")) > 1000, "the 3D player is served")
        check(len(srv.raw("/vendor/vendor/three.module.min.js")) > 100000, "three.js is served")
        r = srv.post("/api/games", {"seats": 4})
        check(r["ok"], "a table can be created")
        code = r["code"]
        try:
            srv.post(f"/api/games/{code}/join", {"name": "No nonce"})
            refused = False
        except urllib.error.HTTPError as e:
            refused = e.code == 400
        check(refused, "a player must send a nonce of their own")
        r = srv.post(f"/api/games/{code}/join", {"name": "Human", "nonce": 12345})
        check(r["ok"], "a player can join")
        token = r["token"]
        version_route(srv, code, token)
        for _ in range(3):
            check(srv.post(f"/api/games/{code}/bot", {})["ok"], "a bot can join")
        v, did = play(srv, code, token)
        check(v["phase"] == "ended", "the game ended")
        check(v["winner"] is not None, f"the game has a winner: {v['seats'][v['winner']]['name']} with {v['seats'][v['winner']]['points']} points, round {v['round']}")
        check(did["law"] and did["piece"] and did["deal"] and did["form"], "laws and deals were proposed")
        text = " ".join(l["text"] for l in v["chronicle"])
        check("rolled" in text and "The game ended" in text, "the chronicle tells the game")
        check("The law passed." in text, "a law passed")
        check("The deal started." in text, "a deal started")
        check("Under a deal" in text, "a deal paid")
        check("from a closed deal" in text, "a deal refunded the rest")
        check("A gift" not in text, "the chronicle reads a deal from its terms, not its title")
        check(len(v["laws"]) >= 1, f"{len(v['laws'])} laws are in force")
        labels = [f"Law {l['id']}" for l in v["laws"]]
        built = [p for p in v["pieces"] if p["kind"] == "lighthouse"]
        if built:
            labels.append("lighthouse")
        check(any(p["name"] == "lighthouse" for p in v["pieceDefs"]) or not did["piece"], "the law-made piece is in the rules")
        print(f"note: {len(built)} lighthouses were built in this game")
        SCENES.append((srv.raw(f"/api/games/{code}/scene?token={token}"), [], labels))
        for n in (2, 3):
            bots_only(srv, n)
        second = second_game(srv)
        pack = extension_pack(srv)
        slime_pack(srv)
        bubble_pack(srv)
        strike_pack(srv)
        pirate_pack(srv)
        omerta_pack(srv)
        claude_table = claude_with_no_key(srv)
        talk_and_replay(srv, code, token, v)
        a_roll_law_fires(srv)
        griefer_findings_stay_fixed(srv)
        table3 = refusals_and_embargo(srv)
        trades_of_several_resources(srv)
        a_bot_takes_a_good_offer(srv)
        over_limit, over_token, over_event = a_table_over_the_limit(srv)
        check(v["serverSeed"] is not None, "the seed is revealed at the end")
        check(srv.post(f"/api/games/{code}/move", {"token": token, "move": {"t": "endTurn"}})["ok"] is False, "nothing happens after the end")
        events = srv.get(f"/api/games/{code}/events")
        check(all("_token" not in e and "_serverSeed" not in e for e in events), "the public log hides tokens and the seed field")
        check_scenes(data)
        srv.stop()
        old = write_old_logs(data)
        add_offer_over_the_limit(data, over_limit, over_event)
        err_path = os.path.join(data, "stderr.txt")
        with open(err_path, "w") as err:
            srv = Server(port, data, err)
        codes = [g["code"] for g in srv.get("/api/games")]
        with open(err_path) as f:
            err_text = f.read()
        check(not any(o in codes for o in old) and code in codes and table3 in codes, "a saved game that no longer replays is left out, and the others load")
        check(second in codes and claude_table in codes, "tables of other games and with other seats load")
        check(over_limit in codes and len(srv.get(f"/api/games/{over_limit}/view?token={over_token}")["offers"][-1]["give"]) == 5, "a saved table with an offer over the limit still replays")
        check(pack in codes and srv.get(f"/api/games/{pack}/view")["game"]["id"] == "not-catan", "a pack's table replays from its log after a restart")
        check(srv.get(f"/api/games/{second}/view")["game"]["id"] == "slime-parliament", "a replay from the log runs the game named in the log")
        check(srv.get(f"/api/games/{code}/talk")["lines"][-1]["text"] == "Good game.", "talk survives a restart")
        check(all(f"[{o}] this saved game was not loaded" in err_text for o in old), "the server says which saved games it left out, and why")
        v2 = srv.get(f"/api/games/{code}/view?token={token}")
        check(v2["version"] == v["version"] and v2["winner"] == v["winner"] and v2["pieces"] == v["pieces"] and v2["chronicle"] == v["chronicle"], f"the game replays the same from its log after a restart ({v['version']} events)")
        run_previews()
        r = subprocess.run([os.path.join(ROOT, ".lake", "build", "bin", "charter-sim"), "--check-bot-log", os.path.join(ROOT, "scripts", "fixtures", "bot-game.jsonl")], capture_output=True, text=True)
        check(r.returncode == 0, f"a bot chooses as it always did: {r.stdout.strip()}")
    finally:
        srv.stop()
    try:
        turn_timer(data)
        vote_pacing(data)
    finally:
        shutil.rmtree(data, ignore_errors=True)
    print("smoke passed")


if __name__ == "__main__":
    main_with_log()
