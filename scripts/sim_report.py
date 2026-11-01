#!/usr/bin/env python3
"""Prints what happened in a game from `make sim`: the story from its files, for a person to read.

Usage: scripts/sim_report.py results/<run> [section ...]
Sections: summary laws drafts talk confessions whispers interviews refused calls chronicle
With no section it prints all but talk and chronicle.
"""
import glob, json, os, sys


def read(path):
    with open(path) as f:
        return [json.loads(l) for l in f if l.strip()]


def main():
    run = sys.argv[1]
    want = sys.argv[2:] or ["summary", "laws", "drafts", "confessions", "whispers", "interviews", "refused", "calls"]
    for path in sorted(glob.glob(os.path.join(run, "*.summary.json"))):
        code = os.path.basename(path).split(".")[0]
        with open(path) as f:
            s = json.load(f)
        talk = read(os.path.join(run, f"{code}.talk.jsonl"))
        seats = read(os.path.join(run, f"{code}.seats.jsonl"))
        events = read(os.path.join(run, f"{code}.events.jsonl"))
        name = {x["seat"]: x["name"] for x in s["seats"]}
        print(f"==== {code}")
        if "summary" in want:
            print(f"status {s['status']}, {s['game']}, round {s['round']}, {s['events']} events, winner {s['winner']}, {s['wallMs']/60000:.1f} minutes")
            print(f"model {s['model']}, effort {s['effort']}; {s['calls']} decisions, {s['clerkCalls']} clerk calls; "
                  f"tokens: {s['input']} in, {s['cacheRead']} cache read, {s['cacheWrite']} cache write, {s['output']} out; "
                  f"{s['refused']} refused, {s['fallbacks']} fallbacks; {s['laws']} laws in force, {s['dealsStarted']} deals started")
            for x in s["seats"]:
                p = x.get("persona") or {}
                print(f"  seat {x['seat']} {x['name']} ({p.get('style')}): {x['points']} points, {x['used']}")
        if "laws" in want:
            print("-- proposals and votes")
            for i, e in enumerate(events):
                if e.get("t") == "propose":
                    print(f"  [{i}] {name.get(e['seat'])}: {e['text']}")
                elif e.get("t") == "vote":
                    print(f"  [{i}]   {name.get(e['seat'])} votes {'yes' if e['yes'] else 'no'} on {e['id']}")
                elif e.get("t") == "sign":
                    print(f"  [{i}]   {name.get(e['seat'])} signs {e['id']}")
                elif e.get("t") == "exit":
                    print(f"  [{i}]   {name.get(e['seat'])} gives notice on deal {e['dealId']}")
                elif e.get("t") == "move" and e["move"].get("t") == "accept":
                    print(f"  [{i}]   {name.get(e['seat'])} accepts offer {e['move']['id']}")
        if "drafts" in want:
            print("-- drafts")
            for r in seats:
                if r.get("k") == "draft":
                    print(f"  [{r['event']}] {name.get(r['seat'])}: {r['words']!r} -> {r['outcome']}: {r.get('formal') or r.get('why')} {('DIFF: ' + r['difference']) if r.get('difference') else ''}")
        for kind, title in (("public", "talk"), ("confession", "confessions"), ("private", "whispers"), ("interview", "interviews")):
            if title in want:
                print(f"-- {title}")
                for l in talk:
                    if l["kind"] == kind:
                        to = f" to {name.get(l['to'])}" if l.get("to") is not None else ""
                        print(f"  [{l['event']}] {name.get(l['by'])}{to}: {l['text']}")
        if "refused" in want:
            print("-- refused and fallbacks")
            for r in seats:
                if r.get("k") in ("refused", "fallback"):
                    what = json.dumps(r.get("action")) if r.get("action") else ""
                    print(f"  [{r.get('event')}] {name.get(r['seat'])} {r['k']}: {r.get('why')} {what}")
        if "calls" in want:
            calls = [r for r in seats if r.get("k") == "call"]
            if calls:
                ms = sorted(r["ms"] for r in calls)
                print(f"-- calls: {len(calls)}, median {ms[len(ms)//2]/1000:.1f}s, longest {ms[-1]/1000:.1f}s, failures {sum(1 for r in calls if r.get('failure'))}")
                for r in calls:
                    if r.get("failure"):
                        print(f"  [{r['event']}] {name.get(r['seat'])} http {r.get('http')}: {r['failure']}")
        if "chronicle" in want:
            print("-- events")
            for i, e in enumerate(events):
                print(f"  [{i}] {json.dumps(e)}")


if __name__ == "__main__":
    main()
