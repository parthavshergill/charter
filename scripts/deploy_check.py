#!/usr/bin/env python3
"""Checks what a public server needs: the budgets, the pause when nobody is there, waking without
spending, and the copy of every log in storage. It uses stand-ins for the Anthropic API and for R2, and
it makes no real calls.

The stand-in for R2 answers as `cloudflare/src/index.ts` does. It starts its own servers on free ports
and stops them at the end.
"""
import glob, http.server, json, os, re, shutil, signal, sqlite3, subprocess, sys, tempfile, threading, time, urllib.error, urllib.parse, urllib.request

from checklib import check, free_port, send_text, wait_for

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, ".lake", "build", "bin", "charter-server")
FAKE_KEY = "fake-key-for-the-deploy-check-0123456789"
BANK = '(law "A fairer bank" (set-bank-rate 3))'
END = json.dumps({"actions": [{"action": "end_turn"}], "confess": None, "remember": "a note to keep", "say": "Next.", "whispers": []})


class Api(http.server.BaseHTTPRequestHandler):
    """A stand-in for the Anthropic API. It counts requests, and each reports the token use set here."""
    calls = []
    # Calls that describe a law are counted apart, so that the budgets below see only the rest.
    describes = []
    input_tokens = 10
    describe_input = 1000
    describe_output = 100
    lock = threading.Lock()

    def log_message(self, *a):
        pass

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers["content-length"])))
        is_seat = "format" in body.get("output_config", {})
        describing = "You describe one law" in body["system"][0]["text"]
        with Api.lock:
            if describing:
                Api.describes.append(body)
            else:
                Api.calls.append("seat" if is_seat else "clerk")
        text = "A description." if describing else END if is_seat else BANK
        usage = {"input_tokens": Api.describe_input if describing else Api.input_tokens, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0}
        send_text(self, text, usage, output_tokens=Api.describe_output if describing else 3)


class Store(http.server.BaseHTTPRequestHandler):
    """A stand-in for the Worker's R2 handler."""
    objects = {}
    failing = False
    put_delay = 0.0
    puts = 0
    lock = threading.Lock()

    def log_message(self, *a):
        pass

    def reply(self, status, body=b""):
        self.send_response(status)
        self.send_header("content-length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def handle_any(self):
        n = int(self.headers.get("content-length") or 0)
        body = self.rfile.read(n) if n else b""
        if Store.failing:
            return self.reply(500)
        url = urllib.parse.urlparse(self.path)
        if url.path == "/list":
            cursor = int(urllib.parse.parse_qs(url.query).get("cursor", ["0"])[0])
            with Store.lock:
                keys = sorted(Store.objects)
            page = keys[cursor:cursor + 50]
            more = cursor + 50 < len(keys)
            return self.reply(200, json.dumps({"keys": page, "cursor": str(cursor + 50) if more else None}).encode())
        key = url.path[3:]
        if self.command == "PUT":
            if Store.put_delay:
                time.sleep(Store.put_delay)
            with Store.lock:
                Store.objects[key] = body
                Store.puts += 1
            return self.reply(200, b"ok")
        if self.command == "DELETE":
            with Store.lock:
                Store.objects.pop(key, None)
            return self.reply(200, b"ok")
        with Store.lock:
            found = Store.objects.get(key)
        return self.reply(200, found) if found is not None else self.reply(404)

    do_GET = do_PUT = do_DELETE = handle_any


def serve(handler):
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv


class Server:
    def __init__(self, data, api, **extra):
        self.port = free_port()
        self.data = data
        self.log = tempfile.NamedTemporaryFile(prefix="charter-log-", delete=False)
        env = dict(os.environ, PORT=str(self.port), CHARTER_ROOT=ROOT, CHARTER_DATA=data, CHARTER_BOT_DELAY_MS="0", CHARTER_VOTE_HOLD_MS="0",
                   ANTHROPIC_API_KEY=FAKE_KEY, ANTHROPIC_BASE_URL=f"http://127.0.0.1:{api.server_address[1]}", CHARTER_SEAT_TIMEOUT_S="2", CHARTER_SEAT_BUDGET_S="4")
        env.update({k: str(v) for k, v in extra.items()})
        self.proc = subprocess.Popen([BIN], env=env, stdout=self.log, stderr=self.log)
        for _ in range(400):
            try:
                self.req("/api/defs")
                return
            except OSError:
                if self.proc.poll() is not None:
                    raise SystemExit(f"FAILED: the server stopped at start: {self.logs()}")
                time.sleep(0.05)
        raise SystemExit("FAILED: the server did not start")

    def logs(self):
        with open(self.log.name) as f:
            return f.read()

    def req(self, path, body=None, headers=None):
        data = None if body is None else json.dumps(body).encode()
        r = urllib.request.Request(f"http://127.0.0.1:{self.port}{path}", data=data, headers={"Content-Type": "application/json", **(headers or {})})
        with urllib.request.urlopen(r, timeout=30) as resp:
            return json.loads(resp.read())

    def status(self, path, body=None, headers=None):
        """The status and the JSON, even for an error."""
        try:
            return 200, self.req(path, body, headers)
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def stop(self, sig=signal.SIGTERM):
        if self.proc.poll() is None:
            self.proc.send_signal(sig)
            try:
                self.proc.wait(timeout=30)
            except subprocess.TimeoutExpired:
                # A later stop in a `finally` must not hide this, so the process goes now.
                self.proc.kill()
                self.proc.wait()
                raise SystemExit(f"FAILED: the server did not stop within 30 seconds of {signal.Signals(sig).name}. The end of its log:\n{self.logs()[-4000:]}")
        return self.proc.returncode


def table(srv, seats=2, people=2, headers=None):
    """A table with this many people. Returns its code and their tokens."""
    code = srv.req("/api/games", {"seats": seats}, headers)["code"]
    tokens = [srv.req(f"/api/games/{code}/join", {"name": f"P{i}", "nonce": 3 + i}, headers)["token"] for i in range(people)]
    return code, tokens


def through_setup(srv, code, tokens):
    """Play the founding, so that a table can use the clerk's suggestions."""
    for _ in range(100):
        v = srv.req(f"/api/games/{code}/view?token={tokens[0]}")
        if v["phase"] != "setup":
            return
        token = tokens[v["turn"]]
        for _ in range(4):
            v = srv.req(f"/api/games/{code}/view?token={token}")
            place = [m for m in v["legalMoves"] if m["move"]["t"] == "place"]
            if not place:
                break
            srv.req(f"/api/games/{code}/move", {"token": token, "move": place[0]["move"]})
        srv.req(f"/api/games/{code}/move", {"token": token, "move": {"t": "endTurn"}})
    raise SystemExit("FAILED: the founding did not end")


def events(srv, code):
    return srv.req(f"/api/games/{code}/events")


def rows_on_disk(path):
    """Read a log the way any reader must: through SQLite, which sees the WAL."""
    db = sqlite3.connect(path)
    try:
        return db.execute("SELECT COUNT(*) FROM events").fetchone()[0]
    finally:
        db.close()


def public_surface(api, root):
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api)
    try:
        code, tokens = table(srv)
        status, _ = srv.status("/api/games")
        check(status == 404, "no public route lists the tables")
        s = srv.req(f"/api/games/{code}")
        check(s["code"] == code and "token" not in json.dumps(s), "a person with the code can read that table's summary, with no token in it")
        v = srv.req(f"/api/games/{code}/view", headers={"X-Charter-Token": tokens[0]})
        check(v["you"] == 0, "the seat token works in a header")
        r = urllib.request.urlopen(f"http://127.0.0.1:{srv.port}/index.html")
        check(r.headers.get("Access-Control-Allow-Origin") is None, "no route allows every origin")
        api_text = json.dumps(events(srv, code))
        check(not any(t in api_text for t in tokens) and "_serverSeed" not in api_text, "the public log holds no token and no seed")
    finally:
        srv.stop()
    # The address and the files it needs.
    check(subprocess.run([BIN], env=dict(os.environ, PORT=str(free_port()), CHARTER_ROOT=ROOT, CHARTER_DATA=data, CHARTER_BIND="nowhere"), capture_output=True, timeout=30).returncode == 1,
          "a bad bind address stops the server at start")
    empty = tempfile.mkdtemp(dir=root)
    os.makedirs(os.path.join(empty, "Server"))
    open(os.path.join(empty, "Server", "formalizer.md"), "w").close()
    r = subprocess.run([BIN], env=dict(os.environ, PORT=str(free_port()), CHARTER_ROOT=empty, CHARTER_DATA=os.path.join(empty, "d")), capture_output=True, text=True, timeout=30)
    check(r.returncode == 1 and "Server/formalizer.md" in r.stderr and "Server/player_rules.md" in r.stderr and "web/index.html" in r.stderr,
          "a missing or empty file stops the server at start, and it names the file")
    srv = Server(tempfile.mkdtemp(dir=root), api, CHARTER_BIND="0.0.0.0")
    try:
        check("http://0.0.0.0:" in srv.logs(), "the bind address can be set")
    finally:
        srv.stop()


def http_get(port, path, headers=None):
    """The status, the headers and the body, for any answer."""
    r = urllib.request.Request(f"http://127.0.0.1:{port}{path}", headers=headers or {})
    try:
        with urllib.request.urlopen(r, timeout=30) as resp:
            return resp.status, resp.headers, resp.read()
    except urllib.error.HTTPError as e:
        return e.code, e.headers, e.read()


def build_of(page):
    m = re.search(rb'<base href="/v/([0-9a-f]+)/">', page)
    return m.group(1).decode() if m else None


def files_a_build_loads(port, build):
    """Every file the page loads, followed from its first two files through imports and stylesheets. All of
    them must be relative, so that all of them stay in the build's folder."""
    todo, seen = ["app.js", "app.css"], {}
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        status, headers, body = http_get(port, f"/v/{build}/{name}")
        seen[name] = (status, headers.get("Cache-Control"), body)
        here = os.path.dirname(name)
        text = body.decode("utf-8", "replace")
        if name.endswith(".js") and "three.module" not in name:
            refs = re.findall(r"""(?:from\s*|import\s*\(\s*|import\s+)["'](\./[^"']+)["']""", text)
            todo += [os.path.normpath(os.path.join(here, r)) for r in refs]
        if name.endswith(".css"):
            refs = re.findall(r"""url\((fonts/[^)]+)\)""", text)
            todo += [os.path.normpath(os.path.join(here, r)) for r in refs]
    return seen


def static_files(api, root):
    """Files a browser may keep, what it must never keep, and what happens when a deploy changes the files."""
    site = tempfile.mkdtemp(dir=root)
    shutil.copytree(os.path.join(ROOT, "web"), os.path.join(site, "web"))
    shutil.copytree(os.path.join(ROOT, "packs"), os.path.join(site, "packs"))
    os.makedirs(os.path.join(site, "Server"))
    for f in ("formalizer.md", "describer.md", "player_rules.md"):
        shutil.copy(os.path.join(ROOT, "Server", f), os.path.join(site, "Server", f))
    with open(os.path.join(site, "web", ".hidden"), "w") as f:
        f.write("not for anyone")
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, CHARTER_ROOT=site)
    try:
        status, h, page = http_get(srv.port, "/")
        build = build_of(page)
        check(status == 200 and build is not None, "the page names one build's folder for all its files")
        check(h["Cache-Control"] == "no-cache" and h["ETag"] == f'"{build}"', "a browser asks again for the page on each visit")
        status, h, body = http_get(srv.port, "/", {"If-None-Match": f'"{build}"'})
        check(status == 304 and not body, "a browser with this page gets a short answer")
        # Cloudflare marks an ETag as weak when it compresses a response, and the browser sends that back.
        status, _, _ = http_get(srv.port, "/?game=ABCDE", {"If-None-Match": f'W/"{build}"'})
        check(status == 304, "the mark that compression adds to an ETag still matches")
        status, _, _ = http_get(srv.port, "/", {"If-None-Match": '"something-else"'})
        check(status == 200, "a browser with another page gets this one")

        loaded = files_a_build_loads(srv.port, build)
        check({"app.js", "app.css", "vendor/player.js", "vendor/vendor/three.module.min.js", "fonts/im-fell-english.woff2"} <= set(loaded), "imports and stylesheets lead to the 3D player and the fonts")
        check(all(st == 200 and "immutable" in (cc or "") and "max-age=31536000" in cc for st, cc, _ in loaded.values()), f"all {len(loaded)} files of a build can be kept for good")
        with open(os.path.join(site, "web", "app.js"), "rb") as f:
            check(loaded["app.js"][2] == f.read(), "a build's file is the file on disk")

        status, h, body = http_get(srv.port, "/app.js")
        check(status == 200 and h["Cache-Control"] == "no-cache" and h["ETag"], "a file at its plain address is checked each time")
        status, _, _ = http_get(srv.port, "/app.js", {"If-None-Match": h["ETag"]})
        check(status == 304, "and unchanged, it is not sent again")
        for bad in (f"/v/{build}/.hidden", f"/v/{build}/../Server/formalizer.md", f"/v/{build}/", "/.hidden", "/../Server/formalizer.md"):
            status, h, _ = http_get(srv.port, bad)
            check(status == 404 and h["Cache-Control"] == "no-store", f"{bad.replace(build, '<build>')} is not served")

        # What changes must never be kept.
        code, tokens = table(srv)
        through_setup(srv, code, tokens)
        for path in ("/api/defs", f"/api/games/{code}", f"/api/games/{code}/view", f"/api/games/{code}/talk", f"/api/games/{code}/events", f"/api/games/{code}/scene", "/api/defs/island/scene"):
            _, h, _ = http_get(srv.port, path, {"X-Charter-Token": tokens[0]})
            check(h["Cache-Control"] == "no-store", f"{path.replace(code, '<code>')} is never kept")
        status, h, scene = http_get(srv.port, f"/api/games/{code}/scene", {"X-Charter-Token": tokens[0]})
        tag = h["X-Scene-Tag"]
        check(status == 200 and scene[:4] == b"GPC1" and tag, "a scene has a tag for its bytes")
        check(h["Content-Type"] == "application/x-protobuf", "a scene has a type that the edge compresses")
        status, h, body = http_get(srv.port, f"/api/games/{code}/scene?have={tag}", {"X-Charter-Token": tokens[0]})
        check(status == 204 and not body and h["Cache-Control"] == "no-store", "a page that has this scene is not sent it again")
        status, _, body = http_get(srv.port, f"/api/games/{code}/scene?have=0000000000000000", {"X-Charter-Token": tokens[0]})
        check(status == 200 and body == scene, "a page with another picture is sent this one")
    finally:
        srv.stop()

    # A restart with the same files: every browser's copy stays good.
    srv = Server(data, api, CHARTER_ROOT=site)
    try:
        status, _, _ = http_get(srv.port, "/", {"If-None-Match": f'"{build}"'})
        check(status == 304, "a restart with the same files keeps the page's name")
        status, _, _ = http_get(srv.port, f"/v/{build}/app.js")
        check(status == 200, "and its files")
    finally:
        srv.stop()

    # A deploy that changes one file: the old page must not get a mix of old and new files.
    with open(os.path.join(site, "web", "feel.js"), "a") as f:
        f.write("\n// a change\n")
    srv = Server(data, api, CHARTER_ROOT=site)
    try:
        _, _, page2 = http_get(srv.port, "/", {"If-None-Match": f'"{build}"'})
        build2 = build_of(page2)
        check(build2 is not None and build2 != build, "changing one file gives the whole page a new name")
        for name in ("feel.js", "app.js", "vendor/player.js"):
            status, h, _ = http_get(srv.port, f"/v/{build}/{name}")
            check(status == 404 and h["Cache-Control"] == "no-store", f"an old page asking for {name} gets nothing, not a newer file under the old name")
        check(all(st == 200 and "immutable" in (cc or "") for st, cc, _ in files_a_build_loads(srv.port, build2).values()), "the new page finds all its files under its own name")
        with open(os.path.join(ROOT, "web", "index.html")) as f:
            html = f.read()
        check('src="app.js" onerror="reloadOnce()"' in html and 'href="app.css" onerror="reloadOnce()"' in html, "a page whose files have gone reloads itself, once")
    finally:
        srv.stop()


def budgets(api, root):
    # At these tokens each request costs $4 of input, and very little output.
    Api.input_tokens = 1000000
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, CHARTER_BUDGET_PER_IP_USD=3, CHARTER_TRUST_CLIENT_IP=1)
    a = {"x-charter-client-ip": "198.51.100.1"}
    b = {"x-charter-client-ip": "198.51.100.2"}
    try:
        code, tokens = table(srv, headers=a)
        def draft(code, token, headers):
            srv.req(f"/api/games/{code}/draft", {"token": token, "words": "Make the bank fairer"}, headers)
            return wait_for(lambda: (lambda d: d if d.get("outcome") else None)(srv.req(f"/api/games/{code}/draft?token={token}")), "the draft to end")
        Api.calls.clear()
        d = draft(code, tokens[0], a)
        check(d["outcome"] == "ready" and Api.calls == ["clerk"], "the first draft is within the budget")
        d = draft(code, tokens[0], a)
        check(d["outcome"] == "failed" and "on strike until tomorrow" in d["reason"] and Api.calls == ["clerk"], f"the next one is not sent, and the clerk says so: {d['reason'][:60]}")
        check(d.get("strike") is True and "budget" not in d["reason"], "the budget is not the player's to read about")
        code2, tokens2 = table(srv, headers=b)
        d = draft(code2, tokens2[0], b)
        check(d["outcome"] == "ready" and len(Api.calls) == 2, "another address has its own budget")
        status, r = srv.status(f"/api/games/{code}/claude", {}, a)
        check(status == 429 and "on strike until tomorrow" in r["error"], "a Claude seat is refused while the budget is used up")
        through_setup(srv, code, tokens)
        srv.req(f"/api/games/{code}/suggest", {"token": tokens[0]}, a)
        d = wait_for(lambda: (lambda d: d if d.get("outcome") else None)(srv.req(f"/api/games/{code}/draft?token={tokens[0]}")), "the suggestion to end")
        check(d["outcome"] == "failed" and "on strike until tomorrow" in d["reason"] and len(Api.calls) == 2, "a suggestion from the clerk is under the same budget")
        v = srv.req(f"/api/games/{code}/view?token={tokens[0]}")
        check("on strike until tomorrow" in (v.get("resting") or ""), "the table's view says the clerk is on strike until tomorrow")
        before = v["version"]
        seat = tokens[v["turn"]]
        r = srv.req(f"/api/games/{code}/move", {"token": seat, "move": {"t": "endTurn"}})
        check(r["ok"] and r["version"] > before, "the game still plays")
        r = srv.req(f"/api/games/{code}/draft", {"token": seat, "words": BANK}, a)
        check(len(Api.calls) == 2, "formal text needs no budget")
        d = wait_for(lambda: (lambda d: d if d.get("outcome") else None)(srv.req(f"/api/games/{code}/draft?token={seat}")), "the formal text to be read")
        check(d["outcome"] == "ready" and d["viaClaude"] is False, "formal text still reaches the review")
        check("one address's budget" in srv.logs(), "the log says which budget is used up, and not which address")
        srv.stop()
        srv = Server(data, api, CHARTER_BUDGET_PER_IP_USD=3, CHARTER_TRUST_CLIENT_IP=1)
        srv.req(f"/api/games/{code}/view?token={tokens[0]}", headers=a)
        d = draft(code, tokens[0], a)
        check(d["outcome"] == "ready", "the per-address figures are in memory, and a restart loses them")
    finally:
        srv.stop()

    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, CHARTER_BUDGET_DAILY_USD=3)
    try:
        code, tokens = table(srv)
        Api.calls.clear()
        srv.req(f"/api/games/{code}/draft", {"token": tokens[0], "words": "Make the bank fairer"})
        wait_for(lambda: srv.req(f"/api/games/{code}/draft?token={tokens[0]}").get("outcome"), "the draft to end")
        code2, tokens2 = table(srv, people=1)
        status, r = srv.status(f"/api/games/{code2}/claude", {})
        check(status == 429 and "on strike until tomorrow" in r["error"], "the budget for the whole server stops everyone")
        srv.req(f"/api/games/{code}/draft", {"token": tokens[0], "words": "Make the bank fairer again"})
        wait_for(lambda: srv.req(f"/api/games/{code}/draft?token={tokens[0]}").get("outcome"), "the second draft to end")
        check("the server's budget" in srv.logs(), "the log says it was the server's budget")
        srv.stop()
        srv = Server(data, api, CHARTER_BUDGET_DAILY_USD=3)
        v = srv.req(f"/api/games/{code}/view?token={tokens[0]}")
        check("on strike until tomorrow" in (v.get("resting") or ""), "the server's total survives a restart")
    finally:
        srv.stop()
    # Claude seats at a table with no budget pass their turns, so the table goes on with no API calls.
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, CHARTER_BUDGET_DAILY_USD=3)
    try:
        code = srv.req("/api/games", {"seats": 3})["code"]
        token = srv.req(f"/api/games/{code}/join", {"name": "Mara", "nonce": 7})["token"]
        srv.req(f"/api/games/{code}/claude", {})
        srv.req(f"/api/games/{code}/bot", {})
        Api.calls.clear()
        def poll_and_play():
            v = srv.req(f"/api/games/{code}/view?token={token}")
            if v.get("turn") == 0:
                for m in [m for m in v["legalMoves"] if m["move"]["t"] == "place"][:1]:
                    srv.req(f"/api/games/{code}/move", {"token": token, "move": m["move"]})
                srv.req(f"/api/games/{code}/move", {"token": token, "move": {"t": "endTurn"}})
            return "on strike until tomorrow" in (v.get("resting") or "")
        wait_for(poll_and_play, "the budget to run out", 30)
        count = len(Api.calls)
        start = len(events(srv, code))
        wait_for(lambda: poll_and_play() and len(events(srv, code)) >= start + 6, "the table to go on while the clerk rests", 30)
        check(len(Api.calls) == count, "Claude seats pass their turns, with no API calls, once the budget is used up")
    finally:
        srv.stop()
    Api.input_tokens = 10
    # New tables are limited, so the data folder cannot grow without limit.
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, CHARTER_GAMES_PER_IP_DAY=2, CHARTER_GAMES_PER_DAY=3, CHARTER_TRUST_CLIENT_IP=1)
    try:
        def found(ip):
            return srv.status("/api/games", {"seats": 2}, {"x-charter-client-ip": ip})
        check(found("a")[0] == 200 and found("a")[0] == 200, "an address can found its tables")
        check(found("a")[0] == 429, "and no more than its limit")
        check(found("b")[0] == 200, "another address can still found one")
        check(found("c")[0] == 429, "and the server has its own limit")
    finally:
        srv.stop()


def ledger_rows(path):
    """The budget log, as its rows."""
    db = sqlite3.connect(path)
    try:
        bodies = [bytes(b).decode() if not isinstance(b, str) else b for (b,) in db.execute("SELECT body FROM events ORDER BY seq")]
        return [json.loads(b[b.index("{"):]) for b in bodies]
    finally:
        db.close()


def description_prices(api, root):
    """A description call is charged at the prices of its own model, and those prices can be set."""
    def description_cost(**env):
        data = tempfile.mkdtemp(dir=root)
        srv = Server(data, api, **env)
        code, tokens = table(srv)
        through_setup(srv, code, tokens)
        count = len(Api.describes)
        srv.req(f"/api/games/{code}/draft", {"token": tokens[0], "words": "Make the bank fairer"})
        wait_for(lambda: srv.req(f"/api/games/{code}/draft?token={tokens[0]}").get("review", {}).get("description", {}).get("status") == "ready", "a description")
        check(len(Api.describes) == count + 1, "one description call")
        model = Api.describes[-1]["model"]
        srv.stop()
        rows = [r["usd"] for r in ledger_rows(os.path.join(data, "_spend.ledger")) if "usd" in r]
        check(len(rows) == 2, "the budget log has one row for the draft and one for the description")
        return model, rows[-1], rows[0]

    model, cost, clerk = description_cost()
    check(model == "claude-sonnet-5-5", "the default description model is Sonnet")
    check(cost == 3000, f"1000 input and 100 output tokens cost $0.003000 at Sonnet's prices ({cost} millionths)")
    check(clerk == 100, f"the clerk's call is still at Opus prices: 10 input and 3 output tokens are $0.000100 ({clerk} millionths)")
    _, cost, _ = description_cost(CHARTER_DESCRIBE_MODEL="claude-haiku-5-5", CHARTER_PRICE_HAIKU_INPUT_USD="1", CHARTER_PRICE_HAIKU_OUTPUT_USD="5")
    check(cost == 1500, f"CHARTER_PRICE_HAIKU_* change those prices ({cost} millionths)")
    model, cost, _ = description_cost(CHARTER_DESCRIBE_MODEL="claude-haiku-5-5")
    check(model == "claude-haiku-5-5" and cost == 150, f"another description model is priced as that model ({cost} millionths)")
    model, cost, _ = description_cost(CHARTER_DESCRIBE_MODEL="a-model-with-no-prices")
    check(cost == 6000, f"a model with no prices of its own is charged at the highest ({cost} millionths)")


def advancing(srv, code, seconds):
    n = len(events(srv, code))
    time.sleep(seconds)
    return len(events(srv, code)) - n


def forced(srv, code):
    return sum(1 for e in events(srv, code) if e["t"] == "forceEndTurn")


def pausing(api, root):
    away = 1000
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, CHARTER_TABLE_AWAY_MS=away, CHARTER_TURN_MS=300, CHARTER_CLAUDE_TURN_MS=300)
    try:
        # One person and one bot, with the person gone.
        code, tokens = table(srv, people=1)
        srv.req(f"/api/games/{code}/bot", {})
        wait_for(lambda: forced(srv, code) >= 1, "the timer to end the person's turn while they are here")
        time.sleep(away / 1000 + 0.5)
        n, f = len(events(srv, code)), forced(srv, code)
        time.sleep(1.5)
        check(len(events(srv, code)) == n and forced(srv, code) == f, "a table with nobody there stops: no event, and no forced turn")
        spec = srv.req(f"/api/games/{code}/view")
        check(spec["paused"] is True, "someone watching can see that it is paused, and watching does not wake it")
        time.sleep(0.4)
        check(len(events(srv, code)) == n, "a spectator does not count as a person at the table")
        v = srv.req(f"/api/games/{code}/view?token={tokens[0]}")
        check(v["paused"] is False and v["turnLeftMs"] >= 250, f"a person's return ends the pause, with a whole new deadline ({v['turnLeftMs']} ms)")
        def keep_polling():
            srv.req(f"/api/games/{code}/view?token={tokens[0]}")
            return forced(srv, code) > f
        wait_for(keep_polling, "the table to play on after the return", 10)
        check(True, "the table plays on after the return")
        check(not any(e["t"] not in ("create", "join", "start", "move", "forceEndTurn", "vote", "sign", "propose", "exit") for e in events(srv, code)), "pausing puts nothing in the log")

        # Two people, and only one here: the other cannot stall the table.
        code, tokens = table(srv, people=2)
        start = forced(srv, code)
        end = time.time() + 2.5 * away / 1000
        while time.time() < end:
            v = srv.req(f"/api/games/{code}/view?token={tokens[0]}")
            time.sleep(0.05)
        check(forced(srv, code) - start >= 3 and v["paused"] is False, "with one person here the timer still ends the turn of an idle seat")

        # A person and a Claude seat, with the person gone: no more API calls.
        code = srv.req("/api/games", {"seats": 2})["code"]
        token = srv.req(f"/api/games/{code}/join", {"name": "Mara", "nonce": 7})["token"]
        Api.calls.clear()
        srv.req(f"/api/games/{code}/claude", {})
        wait_for(lambda: len(Api.calls) >= 1, "the seat to be asked")
        time.sleep(away / 1000 + 2.5)
        count = len(Api.calls)
        time.sleep(1.5)
        check(len(Api.calls) == count, "a Claude seat makes no API calls at a paused table")
        srv.req(f"/api/games/{code}/view?token={token}")
        def poll_claude():
            srv.req(f"/api/games/{code}/view?token={token}")
            return len(Api.calls) > count
        wait_for(poll_claude, "the seat to be asked again", 15)
        check(True, "and it is asked again when the person returns")

        # A table with no people is not paused by this rule.
        code = srv.req("/api/games", {"seats": 2})["code"]
        srv.req(f"/api/games/{code}/bot", {})
        srv.req(f"/api/games/{code}/bot", {})
        time.sleep(away / 1000 + 0.3)
        wait_for(lambda: srv.req(f"/api/games/{code}/view").get("phase") == "ended", "the bot table to end", 120)
        check(True, "a table of bots plays to the end with nobody there")
    finally:
        srv.stop()
    # After a restart: every table with people waits for one, and a table of Claude seats for a watcher.
    data = tempfile.mkdtemp(dir=root)
    fast = dict(CHARTER_TURN_MS=300, CHARTER_CLAUDE_TURN_MS=300)
    srv = Server(data, api, CHARTER_TABLE_AWAY_MS=60000, **fast)
    try:
        people, tokens = table(srv, people=1)
        srv.req(f"/api/games/{people}/bot", {})
        ai = srv.req("/api/games", {"seats": 2})["code"]
        srv.req(f"/api/games/{ai}/claude", {})
        srv.req(f"/api/games/{ai}/claude", {})
        bots = srv.req("/api/games", {"seats": 2})["code"]
        srv.stop()
        time.sleep(0.5)  # A request sent just before the stop may still be arriving.
        Api.calls.clear()
        srv = Server(data, api, CHARTER_TABLE_AWAY_MS=60000, **fast)
        check(advancing(srv, people, 1.0) == 0 and advancing(srv, ai, 0.2) == 0, "after a restart no saved table moves until someone is back")
        check(Api.calls == [], "waking up starts no spending")
        srv.req(f"/api/games/{bots}/bot", {})
        srv.req(f"/api/games/{bots}/bot", {})
        wait_for(lambda: srv.req(f"/api/games/{bots}/view").get("phase") == "ended", "bots to play", 120)
        srv.req(f"/api/games/{people}/view?token={tokens[0]}")
        wait_for(lambda: advancing(srv, people, 0.5) > 0, "the table to wake for its person", 10)
        check(True, "a saved table wakes for its person")
        srv.req(f"/api/games/{ai}/view")
        wait_for(lambda: len(Api.calls) > 0, "the all-Claude table to wake", 10)
        check(True, "a saved table of Claude seats wakes for someone watching")
        wait_for(lambda: srv.req(f"/api/games/{ai}/view").get("phase") == "ended", "the Claude table to end", 180)
        interviewed = Api.calls.count("seat")
        srv.stop()
        time.sleep(0.5)
        Api.calls.clear()
        srv = Server(data, api, CHARTER_TABLE_AWAY_MS=60000, **fast)
        srv.req(f"/api/games/{ai}/view")
        time.sleep(1.0)
        check(Api.calls == [], f"a finished game asks nothing after a restart ({interviewed} requests before it)")
    finally:
        srv.stop()


def mirror_env(store):
    return dict(CHARTER_MIRROR_URL=f"http://127.0.0.1:{store.server_address[1]}", CHARTER_MIRROR_INTERVAL_MS=100)


def mirrored(api, store, root):
    Store.objects.clear()
    data = tempfile.mkdtemp(dir=root)
    env = dict(mirror_env(store), CHARTER_BOT_DELAY_MS=10, CHARTER_TABLE_AWAY_MS=60000)
    srv = Server(data, api, **env)
    try:
        people, tokens = table(srv, seats=2, people=2)
        srv.req(f"/api/games/{people}/talk", {"token": tokens[0], "text": "Good luck."})
        srv.req(f"/api/games/{people}/draft", {"token": tokens[0], "words": "Make the bank fairer"})
        wait_for(lambda: srv.req(f"/api/games/{people}/draft?token={tokens[0]}").get("outcome"), "the draft")
        claude = srv.req("/api/games", {"seats": 2})["code"]
        srv.req(f"/api/games/{claude}/claude", {})
        srv.req(f"/api/games/{claude}/claude", {})
        wait_for(lambda: glob.glob(os.path.join(data, f"{claude}.seats")) and rows_on_disk(os.path.join(data, f"{claude}.seats")) > 0, "a seat record")
        running = srv.req("/api/games", {"seats": 2})["code"]
        srv.req(f"/api/games/{running}/bot", {})
        srv.req(f"/api/games/{running}/bot", {})
        wait_for(lambda: len(events(srv, running)) > 40, "the bot game to get going")

        # A slow store does not slow a move.
        Store.put_delay = 1.5
        time.sleep(0.2)
        v = srv.req(f"/api/games/{people}/view?token={tokens[0]}")
        place = [m for m in v["legalMoves"] if m["move"]["t"] == "place"]
        start = time.time()
        r = srv.req(f"/api/games/{people}/move", {"token": tokens[v['turn']], "move": place[0]["move"]})
        took = time.time() - start
        check(r["ok"] and took < 0.5, f"a slow store does not hold up a move ({took * 1000:.0f} ms with uploads taking 1500 ms)")
        Store.put_delay = 0.0

        # A stopped store does not stop the game, and the copy catches up.
        Store.failing = True
        n = len(events(srv, running))
        wait_for(lambda: len(events(srv, running)) > n + 10, "the game to go on with the store down")
        wait_for(lambda: "storage cannot be reached" in srv.logs(), "the log to say the store is down")
        check(True, "with the store down the game goes on, and the log says why")
        Store.failing = False
        before_folds = max(len([k for k in Store.objects if f"/{running}.db/" in k]), 0)
        check(before_folds <= 17, f"a busy log is folded into few objects ({before_folds})")

        # SIGTERM: the platform's way to stop a container. Nothing is lost.
        check(srv.stop() == 0, "SIGTERM ends the server cleanly")
        check("everything is in storage" in srv.logs(), "and it says the last copy finished")
        on_disk = {os.path.basename(p): rows_on_disk(p) for p in glob.glob(os.path.join(data, "*")) if p.rsplit(".", 1)[-1] in ("db", "talk", "clerk", "seats", "ledger")}
        check(len(on_disk) >= 6 and any(k.endswith(".clerk") for k in on_disk) and any(k.endswith(".seats") for k in on_disk) and "_spend.ledger" in on_disk, "game, talk, clerk, seat and budget logs are all in the data folder")
        text = b"".join(Store.objects.values()) + open(srv.log.name, "rb").read()
        check(FAKE_KEY.encode() not in text, "the API key is in no log and no stored object")

        # A new container with an empty disk.
        fresh = tempfile.mkdtemp(dir=root)
        srv2 = Server(fresh, api, **env)
        restored = {os.path.basename(p): rows_on_disk(p) for p in glob.glob(os.path.join(fresh, "*")) if p.rsplit(".", 1)[-1] in ("db", "talk", "clerk", "seats", "ledger")}
        # The bot table is already playing again, so its log can only be longer.
        different = {k: (on_disk.get(k), restored.get(k)) for k in set(on_disk) | set(restored)
                     if (on_disk.get(k) or 0) != (restored.get(k) or 0) and not (k.startswith(running) and (restored.get(k) or 0) > (on_disk.get(k) or 0))}
        check(not different, f"a fresh disk gets every row of every log back: {sum(on_disk.values())} rows in {len(on_disk)} logs")
        check(not glob.glob(os.path.join(fresh, ".restore")), "restoring cleans up after itself")
        v = srv2.req(f"/api/games/{people}/view?token={tokens[0]}")
        check(v["you"] == 0 and v["started"], "a seat token still works after a restore")
        check(srv2.req(f"/api/games/{people}/talk?token={tokens[0]}")["lines"][-1]["text"] == "Good luck.", "talk is back")
        srv2.req(f"/api/games/{people}/draft", {"token": tokens[0], "words": "Make the bank fairer"})
        wait_for(lambda: srv2.req(f"/api/games/{people}/draft?token={tokens[0]}").get("outcome"), "a new draft")
        check(rows_on_disk(os.path.join(fresh, f"{people}.clerk")) == on_disk[f"{people}.clerk"] + 1, "the clerk's memory is back, and grows")
        describes_before = len(Api.describes)
        d = srv2.req(f"/api/games/{people}/draft?token={tokens[0]}")
        check(d["review"]["description"] == {"status": "ready", "text": "A description."} and len(Api.describes) == describes_before,
              "a law's description is back from storage, and it needs no new call")
        place = [m for m in v["legalMoves"] if m["move"]["t"] == "place"]
        if place:
            r = srv2.req(f"/api/games/{people}/move", {"token": tokens[v['turn']], "move": place[0]["move"]})
            check(r["ok"], "the game goes on from its log")
        wait_for(lambda: srv2.req(f"/api/games/{running}/view").get("phase") == "ended" or len(events(srv2, running)) > on_disk[f"{running}.db"] + 20, "the bot game to go on", 60)
        check(True, "a bot game goes on by itself from where it stopped")
        wait_for(lambda: len([k for k in Store.objects if f"/{claude}.db/" in k]) == 1, "the quiet logs to fold", 20)
        check(True, "a log with several objects is folded into one once it is quiet")

        # SIGKILL: no warning. What is in storage is a prefix of each log.
        count_before = len(events(srv2, running))
        check(srv2.stop(signal.SIGKILL) == -9, "a hard kill")
        local = rows_on_disk(os.path.join(fresh, f"{running}.db"))
        fresh2 = tempfile.mkdtemp(dir=root)
        srv3 = Server(fresh2, api, **env)
        back = rows_on_disk(os.path.join(fresh2, f"{running}.db"))
        print(f"note: a hard kill during a bot game playing at about 50 events a second, with a copy every 100 ms: {local} events on the lost disk, {back} restored, {local - back} lost")
        check(back <= local and local - back < 100 and back >= count_before - 100, "it loses at most the rows since the last copy")
        a = srv3.req(f"/api/games/{running}/events")
        check(len(a) >= back, "and the game replays from what survives")
        srv3.stop()

        # Gaps must stop the server. Overlaps must not.
        keys = sorted(k for k in Store.objects if f"/{people}.db/" in k)
        whole = keys[0]
        first, count = whole.rsplit("/", 1)[1][:-6].split("-")
        rows = Store.objects[whole].decode().splitlines(True)
        n = len(rows)
        Store.objects[whole.replace(f"{first}-{count}", f"{1:012}-{n - 1:012}")] = "".join(rows[1:]).encode()
        Store.objects[whole.replace(f"{first}-{count}", f"{0:012}-{2:012}")] = "".join(rows[:2]).encode()
        fresh3 = tempfile.mkdtemp(dir=root)
        srv4 = Server(fresh3, api, **env)
        check(rows_on_disk(os.path.join(fresh3, f"{people}.db")) == n, "objects that overlap restore correctly")
        srv4.stop()
        for k in sorted(k for k in Store.objects if f"/{people}.db/" in k):
            del Store.objects[k]
        Store.objects[f"v1/{people}.db/{5:012}-{2:012}.jsonl"] = b'"x"\n"y"\n'
        fresh4 = tempfile.mkdtemp(dir=root)
        env_fast = dict(os.environ, PORT=str(free_port()), CHARTER_ROOT=ROOT, CHARTER_DATA=fresh4, CHARTER_MIRROR_URL=env["CHARTER_MIRROR_URL"])
        start = time.time()
        r = subprocess.run([BIN], env=env_fast, capture_output=True, text=True, timeout=60)
        check(r.returncode == 1 and "will not start" in r.stderr and f"{people}.db" in r.stderr and "missing" in r.stderr, f"a gap in a log stops the server, and it names the log ({time.time() - start:.0f} s of retries)")
    finally:
        srv.stop()
        for s in list(locals().values()):
            if isinstance(s, Server):
                s.stop()


def sleep_and_wake(api, store, root):
    """The whole story: friends stop, the table pauses, the container sleeps, and they come back."""
    Store.objects.clear()
    env = dict(mirror_env(store), CHARTER_TABLE_AWAY_MS=500, CHARTER_TURN_MS=100000, CHARTER_CLAUDE_TURN_MS=100000)
    data = tempfile.mkdtemp(dir=root)
    srv = Server(data, api, **env)
    try:
        code = srv.req("/api/games", {"seats": 2})["code"]
        token = srv.req(f"/api/games/{code}/join", {"name": "Mara", "nonce": 7})["token"]
        srv.req(f"/api/games/{code}/claude", {})
        wait_for(lambda: srv.req(f"/api/games/{code}/view?token={token}")["turn"] is not None, "the game to start")
        time.sleep(1.0)
        n = len(events(srv, code))
        check(srv.stop() == 0, "the container sleeps while its table is paused")
        Api.calls.clear()
        srv = Server(tempfile.mkdtemp(dir=root), api, **env)
        time.sleep(1.0)
        check(Api.calls == [] and len(events(srv, code)) == n, "it wakes with a fresh disk, the game back, the table still paused, and no spending")
        v = srv.req(f"/api/games/{code}/view?token={token}")
        check(v["paused"] is False and v["you"] == 0, "the person returns, and the table plays")
    finally:
        srv.stop()


def main():
    root = tempfile.mkdtemp(prefix="charter-deploy-")
    api = serve(Api)
    store = serve(Store)
    try:
        public_surface(api, root)
        static_files(api, root)
        budgets(api, root)
        description_prices(api, root)
        pausing(api, root)
        mirrored(api, store, root)
        sleep_and_wake(api, store, root)
    finally:
        api.shutdown()
        store.shutdown()
        shutil.rmtree(root, ignore_errors=True)
    print("deploy check passed")


if __name__ == "__main__":
    main()
