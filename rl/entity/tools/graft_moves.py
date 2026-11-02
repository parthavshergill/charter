"""Graft per-move rows onto a layout-2 entity checkpoint without them, so the new network plays exactly as the old.

    python3 rl/entity/tools/graft_moves.py OLD.bin OUT.bin [--seed 0]

OLD.bin's meta (OLD.bin.json) must say layout 2, pointer 1, no moves. The new file has:
- `W_moves` (E x 58), small random, as PufferLib would start it;
- `W_out` with E more input columns for the moves table's mean, set to 0;
- `A` with E more rows (the move query), set to 0;
- everything else copied.

With those zeros, every logit and the value are the same as OLD's (checked here on random observations), and
training can still move all of them: the move query's gradient is not zero, and through it `W_moves`'s.
"""
import argparse
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RL = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path[:0] = [RL, os.path.join(RL, "entity")]
from entity.entity_numpy import base_tables, read_entity_bin, load_entity  # noqa: E402

LAYOUT = json.load(open(os.path.join(RL, "layout.json")))


def write(blocks, path):
    out = []
    for b in blocks:
        a = np.ascontiguousarray(b, np.float32).ravel()
        out.append(np.concatenate([a, np.zeros((-len(a)) % 8, np.float32)]))
    np.concatenate(out).astype("<f4").tofile(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old")
    ap.add_argument("out")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--no-end-linear", action="store_true",
                    help="zero the decoder's linear row for end turn (action 0), so end turn is scored from its moves "
                         "row only; train with no_end_linear (CE_NO_LINEAR_END) to keep it 0")
    a = ap.parse_args()
    meta = json.load(open(a.old + ".json"))
    assert int(meta.get("layout", 2)) == 2 and int(meta.get("pointer", 0)) == 1 and not meta.get("moves")
    E, H, layers, act = meta["entity_dim"], meta["hidden"], meta["layers"], meta["act_size"]
    base = base_tables(LAYOUT)
    w_in, w_out, dec, ptr, grus = read_entity_bin(a.old, base, E, H, layers, act, 1)
    width = next(t["width"] for t in LAYOUT["tables"] if t["name"] == "moves")
    rng = np.random.default_rng(a.seed)
    w_moves = (rng.normal(size=(E, width)) * (2 / width) ** 0.5).astype(np.float32)
    w_out2 = np.concatenate([w_out, np.zeros((H, E), np.float32)], 1)
    ptr2 = np.concatenate([ptr, np.zeros((E, H), np.float32)], 0)
    if a.no_end_linear:
        dec = dec.copy()
        dec[0] = 0
    write(list(w_in) + [w_moves, w_out2, dec, ptr2] + list(grus), a.out)
    meta2 = dict(meta, moves=1, no_end_linear=int(a.no_end_linear), obs_size=LAYOUT["full_size"], name=os.path.basename(a.out),
                 grafted_from=meta.get("name", a.old))
    meta2["settings"] = dict(meta.get("settings", {}), move_rows=True)
    json.dump(meta2, open(a.out + ".json", "w"))
    # The same play: OLD on the base observation, NEW on the full one (base, then moves rows).
    old, new = load_entity(a.old, meta), load_entity(a.out, meta2)
    worst = 0.0
    for k in range(20):
        obs = rng.normal(size=LAYOUT["full_size"]).astype(np.float32)
        for t in LAYOUT["tables"]:
            blk = obs[t["offset"]:t["offset"] + t["rows"] * t["width"]].reshape(t["rows"], t["width"])
            blk[:, 0] = rng.random(t["rows"]) < 0.6
            if t["name"] == "moves":
                blk[:, 1] = rng.permutation(act - 1)[:t["rows"]]
        s = [np.zeros(H, np.float32) for _ in range(layers)]
        lo, vo, _ = old.forward(obs[:LAYOUT["base_size"]], s)
        ln, vn, _ = new.forward(obs, s)
        worst = max(worst, float(np.abs(lo - ln).max()), abs(float(vo - vn)))
    if a.no_end_linear:
        print(f"wrote {a.out}: the old net, with end turn's linear row set to 0")
        return
    print(f"wrote {a.out}: the grafted net matches the old one to {worst:.2e} on 20 random observations")
    assert worst < 1e-4


if __name__ == "__main__":
    main()
