#!/usr/bin/env python3
"""Check the server's policy against the training team's own code (`rl/entity/entity_numpy.py` on the training
branch). Extract that file, `rl/entity/__init__.py`, `rl/reference/policy.py`, `rl/reference/__init__.py` and
`rl/layout.json` from the branch into REFDIR (keeping their paths), then run this with `python3 -I`:

  policy_ref_check.py forward REFDIR WEIGHTS.chpw META.json OBS.txt OUT.txt
      the reference forward on recorded observations (charter-policy-check --record), carrying the recurrent state
      across a seat's decisions; compare with charter-policy-diff WEIGHTS OBS.txt OUT.txt.
  policy_ref_check.py mix REFDIR WEIGHTS.chpw META.json DECISIONS.rec K C
      the reference `choose_mix` (the decision-time blend) on decisions the server recorded
      (charter-policy-check --record-mix), with a stand-in game that replays the server's after-states.
"""
import json
import sys

import numpy as np


def header_bytes(b):
    nt = int.from_bytes(b[44:48], "little")
    return 4 + 4 * (11 + 3 * nt + {2: 5, 3: 7, 4: 8, 5: 10}[int.from_bytes(b[4:8], "little")])


def load(refdir, chpw, meta_path):
    sys.path.insert(0, refdir + "/rl")
    from entity.entity_numpy import load_entity
    b = open(chpw, "rb").read()
    raw = chpw + ".bin"
    open(raw, "wb").write(b[header_bytes(b):])
    return load_entity(raw, json.load(open(meta_path)), refdir + "/rl/layout.json")


def forward(refdir, chpw, meta_path, obs_path, out):
    net = load(refdir, chpw, meta_path)
    state = net.initial_state()
    rows = []
    for line in open(obs_path):
        line = line.strip()
        if not line or line == "reset":
            state = net.initial_state()
            continue
        if line == "turn":
            continue  # carry: a new turn changes nothing
        logits, _, state = net.forward(np.array([float(v) for v in line.split()], np.float32), state)
        rows.append(" ".join(repr(float(v)) for v in logits))
    open(out, "w").write("\n".join(rows) + "\n")
    print("wrote %d rows of %d logits" % (len(rows), len(logits)))


def mix(refdir, chpw, meta_path, rec, k, c):
    net = load(refdir, chpw, meta_path)
    net.set_diag("mix%dc%g" % (k, c))
    assert net.mix == (k, c), net.mix
    decisions, cur = [], None
    for line in open(rec):
        tag, _, rest = line.rstrip("\n").partition(" ")
        if tag == "decision": cur = {"name": rest, "cands": []}; decisions.append(cur)
        elif tag == "state": cur["state"] = np.array(rest.split(), np.float32)
        elif tag == "obs": cur["obs"] = np.array(rest.split(), np.float32)
        elif tag == "legal": cur["legal"] = [int(x) for x in rest.split()]
        elif tag == "cand":
            a, kind, v, sc = rest.split(); cur["cands"].append({"a": int(a), "kind": kind, "v": float(v), "score": float(sc)})
        elif tag == "after": cur["cands"][-1]["after"] = np.array(rest.split(), np.float32)
        elif tag == "lean": a, v = rest.split(); cur["lean"] = int(a); cur["vnow"] = float(v)

    class Child:
        def __init__(self, d, seat): self.d, self.seat_ = d, seat; self.cand = None
        def step(self, a):
            self.cand = next((x for x in self.d["cands"] if x["a"] == a), None)
            if self.cand is None: raise KeyError("the reference tried action %d, which the server did not record" % a)
        @property
        def over(self): return self.cand["kind"] == "over"
        @property
        def seat(self): return self.seat_ if self.cand["kind"] == "same" else -1
        def obs(self): return self.cand["after"]
        def rewards(self):
            out = np.zeros(6, np.float32); out[self.seat_] = self.cand["v"]; return out

    class Game:
        voting = False
        def __init__(self, d, seat): self.d, self.seat = d, seat
        def copy(self): return Child(self.d, self.seat)

    class Player: pass

    same = 0; worst_v = worst_s = 0.0; flips = 0; rows = []
    for d in decisions:
        seat = int(d["name"].split()[2])
        hidden = len(d["state"])
        logits, v, st = net.forward(d["obs"], [d["state"]])
        lg = logits.astype(np.float64)[:516]; masked = np.full_like(lg, -np.inf); masked[d["legal"]] = lg[d["legal"]]
        p = Player(); p.state = st
        a = net.choose_mix(p, Game(d, seat), d["obs"], None, masked)
        same += (a == d["lean"])
        worst_v = max(worst_v, abs(float(v) - d["vnow"]))
        # reference scores for the recorded candidates
        for x in d["cands"]:
            if x["kind"] == "same":
                _, v2, _ = net.forward(x["after"], st); vr = float(v2)
            elif x["kind"] == "over": vr = x["v"]
            else: vr = float(v)
            worst_s = max(worst_s, abs(masked[x["a"]] + c * (vr - float(v)) - x["score"]))
        flips += (a != int(np.argmax(masked)))
    print("decisions: %d | chosen action agrees: %d of %d | blend changed the greedy choice in %d | max |V(now) error| %.2e | max candidate-score error %.2e"
          % (len(decisions), same, len(decisions), flips, worst_v, worst_s))


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) == 6 and a[0] == "forward":
        forward(*a[1:])
    elif len(a) == 7 and a[0] == "mix":
        mix(a[1], a[2], a[3], a[4], int(a[5]), float(a[6]))
    else:
        print(__doc__)
        sys.exit(2)
