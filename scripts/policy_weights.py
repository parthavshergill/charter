#!/usr/bin/env python3
"""Convert a PufferLib checkpoint to a Lean policy weights file (.chpw).

Usage:
  policy_weights.py CKPT.bin --out OUT.chpw [--gru-state carry|turn|zero]

CKPT.bin.json must sit next to CKPT.bin (keys: entity_dim, hidden, layers,
act_size, pointer, layout). The layout (1 or 2) comes from the meta's
`layout`, 1 if it has none; its tables are in policy_diff.py.

The output is a header followed by the .bin bytes unchanged. The format is
described in Server/Policy/Net.lean.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from policy_diff import LAYOUTS, STATE_RULES, block_shapes, header_bytes, pad8  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ckpt")
    ap.add_argument("--out", required=True)
    ap.add_argument("--gru-state", choices=sorted(STATE_RULES),
                    help="how the recurrent state moves between a seat's decisions, if the meta has no gru_state: "
                         "carry (eval, games against bots), turn (0.5 at each turn start, as self-play waiting ticks "
                         "make it), zero (behaviour cloning)")
    a = ap.parse_args()

    meta = json.load(open(a.ckpt + ".json"))
    version = int(meta.get("layout", 1))
    if version not in LAYOUTS:
        sys.exit("layout version %d: this server path knows versions %s" % (version, sorted(LAYOUTS)))
    layout = LAYOUTS[version]
    E = int(meta.get("entity_dim", 32))
    hidden, layers = int(meta["hidden"]), int(meta["layers"])
    act, pointer = int(meta["act_size"]), int(meta.get("pointer", 0))
    if act not in (layout["act_size"], layout["act_size"] + 1):
        sys.exit("act_size %d in checkpoint, %d (or one more, for the no-op) in layout %d" % (act, layout["act_size"], version))
    if version == 2 and pointer not in (0, 3):
        # entity2's layout-2 meta writes pointer 1 for the layout-2 pointer (places and bank).
        pointer = 3

    data = open(a.ckpt, "rb").read()
    shapes = block_shapes([t[3] for t in layout["tables"]], E, hidden, layers, act, pointer)
    want = 4 * sum(pad8(r * c) for r, c in shapes)
    if len(data) != want:
        sys.exit("%s: expected %d bytes for this layout and meta, got %d"
                 % (a.ckpt, want, len(data)))
    rule = meta.get("gru_state") or a.gru_state
    if rule not in STATE_RULES:
        sys.exit("the meta has no gru_state: say how the checkpoint was trained with --gru-state carry|turn|zero")
    if meta.get("gru_state") and a.gru_state and a.gru_state != meta["gru_state"]:
        sys.exit("--gru-state %s, but the meta says %s" % (a.gru_state, meta["gru_state"]))
    out = header_bytes(layout, E, hidden, layers, pointer, rule, act) + data
    open(a.out, "wb").write(out)
    print("wrote %s (%d bytes, %d params, state rule %s)" % (a.out, len(out), sum(r * c for r, c in shapes), rule))


if __name__ == "__main__":
    main()
