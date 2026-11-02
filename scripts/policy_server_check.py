"""Play a table of policy bots on every world in the Library through the real server, over HTTP.

python3 scripts/policy_server_check.py WEIGHTS

Starts charter-server with CHARTER_BOT=policy and CHARTER_POLICY_WEIGHTS=WEIGHTS, adds four bots ("Add a bot")
to a table of each world, and waits for each game to end. Fails if a game does not end in time.
"""
import os
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import smoke  # noqa: E402


def main():
    weights = os.path.abspath(sys.argv[1])
    os.environ["CHARTER_BOT"] = "policy"
    os.environ["CHARTER_POLICY_WEIGHTS"] = weights
    with tempfile.TemporaryDirectory() as data:
        srv = smoke.Server(smoke.free_port(), data)
        try:
            for d in srv.get("/api/defs"):
                game = d["id"]
                seats = max(d.get("minSeats", 2), min(4, d.get("maxSeats", 4)))
                t0 = time.time()
                code = srv.post("/api/games", {"seats": seats, "game": game})["code"]
                for _ in range(seats):
                    r = srv.post(f"/api/games/{code}/bot", {})
                    if not r["ok"]:
                        raise SystemExit(f"FAILED: a policy bot could not join {game}: {r}")
                while True:
                    v = srv.get(f"/api/games/{code}/view")
                    if v["phase"] == "ended":
                        w = v["seats"][v["winner"]] if v.get("winner") is not None else None
                        pts = [s["points"] for s in v["seats"]]
                        print(f"ok: {game}, {seats} policy bots, ended in round {v['round']}, points {pts}, "
                              f"winner {w['name'] if w else None}, {time.time() - t0:.1f} s")
                        break
                    if time.time() - t0 > 600:
                        raise SystemExit(f"FAILED: {game} did not end: round {v['round']}")
                    time.sleep(0.1)
        finally:
            srv.stop()
    print("policy server check passed")


if __name__ == "__main__":
    main()
