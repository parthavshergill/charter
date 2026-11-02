"""A short reading of saved Sonnet games: moves by type for each seat, and what each seat built, in order.

    python3 rl/hero/summarize.py CODE...
"""
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    for code in sys.argv[1:]:
        d = json.load(open(os.path.join(HERE, "games", f"{code}.json")))
        res = d["result"]
        p = res["policy_seat"]
        print(f"## {code} ({d['settings']['weights_label']}, {res['mode']}): policy seat {p}; winner {res['winner']} "
              f"({res['how']}), round {res['round']}, points {res['points']}")
        kinds = collections.defaultdict(collections.Counter)
        built = collections.defaultdict(list)
        turns = 0
        for e in d["events"]:
            if e.get("t") != "move":
                continue
            m, s = e["move"], e["seat"]
            kinds[s][m["t"]] += 1
            if m["t"] == "endTurn":
                turns += 1
            if m["t"] in ("place", "placeLink"):
                rnd = max(0, (turns - 8) // 4 + 1)
                built[s].append(f"r{rnd} {m.get('kind')}@{m.get('spot', m.get('a', ''))}")
            if m["t"] == "bankTrade":
                rnd = max(0, (turns - 8) // 4 + 1)
                built[s].append(f"r{rnd} trade {m.get('give')}>{m.get('get')}")
        for s in sorted(kinds):
            who = "POLICY" if s == p else "sonnet"
            print(f"  seat {s} {who}: {dict(kinds[s])}")
            print(f"    {'; '.join(built[s])}")


if __name__ == "__main__":
    main()
