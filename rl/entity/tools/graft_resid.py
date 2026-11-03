"""Add the encoder's residual block (CE_RESID) to an entity checkpoint, so the new network plays exactly as the old.

    python3 rl/entity/tools/graft_resid.py OLD.bin OUT.bin [--seed 0]

OLD.bin's meta (OLD.bin.json) must say layout 2 and pointer 1, with no residual block. After `W_out` the new file
has the LayerNorm's gain (all 1) and bias (all 0), `W_r1` (small random, as PufferLib would start it) and `W_r2`
(all 0). Everything else is copied.

With W_r2 = 0 the block adds nothing: every logit and the value are the same as OLD's (checked here on random
observations). Training can still move it: W_r2's gradient is not zero, and once W_r2 moves, the others' are not.
"""
import argparse
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RL = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path[:0] = [RL, os.path.join(RL, "entity"), HERE]
from entity.entity_numpy import base_tables, read_entity_bin, load_entity  # noqa: E402
from graft_moves import write  # noqa: E402

LAYOUT = json.load(open(os.path.join(RL, "layout.json")))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old")
    ap.add_argument("out")
    ap.add_argument("--seed", type=int, default=0)
    a = ap.parse_args()
    meta = json.load(open(a.old + ".json"))
    assert int(meta.get("layout", 2)) == 2 and int(meta.get("pointer", 0)) == 1 and not meta.get("resid")
    E, H, layers, act = meta["entity_dim"], meta["hidden"], meta["layers"], meta["act_size"]
    moves = bool(meta.get("moves", 0))
    w_in, w_out, dec, ptr, grus = read_entity_bin(a.old, base_tables(LAYOUT, moves), E, H, layers, act, 1)
    rng = np.random.default_rng(a.seed)
    g, b = np.ones(H, np.float32), np.zeros(H, np.float32)
    w1 = (rng.normal(size=(H, H)) * (2 / H) ** 0.5).astype(np.float32)
    w2 = np.zeros((H, H), np.float32)
    write(list(w_in) + [w_out, g, b, w1, w2, dec, ptr] + list(grus), a.out)
    meta2 = dict(meta, resid=1, name=os.path.basename(a.out), grafted_from=meta.get("name", a.old))
    json.dump(meta2, open(a.out + ".json", "w"))
    old, new = load_entity(a.old, meta), load_entity(a.out, meta2)
    size = LAYOUT["full_size"] if moves else LAYOUT["base_size"]
    worst = 0.0
    for k in range(20):
        obs = rng.normal(size=size).astype(np.float32)
        for t in LAYOUT["tables"]:
            if t["offset"] >= size:
                continue
            blk = obs[t["offset"]:t["offset"] + t["rows"] * t["width"]].reshape(t["rows"], t["width"])
            blk[:, 0] = rng.random(t["rows"]) < 0.6
            if t["name"] == "moves":
                blk[:, 1] = rng.permutation(act - 1)[:t["rows"]]
        s = [np.zeros(H, np.float32) for _ in range(layers)]
        lo, vo, _ = old.forward(obs, s)
        ln, vn, _ = new.forward(obs, s)
        worst = max(worst, float(np.abs(lo - ln).max()), abs(float(vo - vn)))
    print(f"wrote {a.out}: the grafted net matches the old one to {worst:.2e} on 20 random observations")
    assert worst < 1e-4


if __name__ == "__main__":
    main()
