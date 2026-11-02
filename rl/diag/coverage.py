"""Which observation columns never vary on the training worlds but do on others (their weights never get a signal)."""
import json, sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from pit import parse, S
L = json.load(open("/home/user/charter/rl/layout.json"))
worlds = sys.argv[1].split(",")
train = ["island", "not-catan"]
def cols(world):
    p = f"{S}/srv/rec-{world}.txt" if world != "the-pit" else f"{S}/srv/pit.txt"
    obs = np.stack([r["obs"] for k, r in parse(p) if k == "dec"])
    out = {}
    for t in L["tables"]:
        if t["name"] == "moves": continue
        x = obs[:, t["offset"]:t["offset"] + t["rows"] * t["width"]].reshape(len(obs), t["rows"], t["width"])
        real = x[:, :, 0] > 0.5
        for c in t["cols"]:
            v = x[:, :, c["at"]:c["at"] + c["width"]][real]
            out[(t["name"], c["name"])] = (float(v.min()) if v.size else 0.0, float(v.max()) if v.size else 0.0)
    return out
C = {w: cols(w) for w in worlds}
keys = list(C[worlds[0]].keys())
print("| table.column | " + " | ".join(worlds) + " |")
print("|---" * (len(worlds) + 1) + "|")
n = 0
for k in keys:
    tr = [C[w][k] for w in train if w in C]
    const_train = all(lo == hi for lo, hi in tr) and len(set(tr)) <= 1
    varies_else = any(C[w][k][0] != C[w][k][1] or (tr and C[w][k] != tr[0]) for w in worlds if w not in train)
    if const_train and varies_else:
        n += 1
        print(f"| {k[0]}.{k[1]} | " + " | ".join(f"{C[w][k][0]:.2g}..{C[w][k][1]:.2g}" for w in worlds) + " |")
print(f"\n{n} columns are constant on both training worlds and vary (or differ) on another world")
