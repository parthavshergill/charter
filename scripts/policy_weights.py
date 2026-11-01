#!/usr/bin/env python3
"""Convert a PufferLib checkpoint to a Lean policy weights file (.chpw).

Usage:
  policy_weights.py CKPT.bin [LAYOUT.json] --out OUT.chpw

CKPT.bin.json must sit next to CKPT.bin (keys: entity_dim, hidden, layers,
act_size, pointer). LAYOUT.json is optional; without it the layout version 1
numbers below are used. Its keys: layout_version, act_size, act_spot,
act_link, act_bank, tables (a list of [name, offset, rows, width]).

The output is a header followed by the .bin bytes unchanged. The format is
described in Server/Policy/Net.lean.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from policy_diff import STATE_RULES, V1, block_shapes, header_bytes, pad8  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ckpt")
    ap.add_argument("layout", nargs="?")
    ap.add_argument("--out", required=True)
    ap.add_argument("--gru-state", choices=sorted(STATE_RULES),
                    help="how the recurrent state moves between a seat's decisions, if the meta has no gru_state: "
                         "carry (eval, games against bots), turn (0.5 at each turn start, as self-play waiting ticks "
                         "make it), zero (behaviour cloning)")
    a = ap.parse_args()

    meta = json.load(open(a.ckpt + ".json"))
    layout = json.load(open(a.layout)) if a.layout else V1
    E = int(meta.get("entity_dim", 32))
    hidden, layers = int(meta["hidden"]), int(meta["layers"])
    act, pointer = int(meta["act_size"]), int(meta.get("pointer", 0))
    if act != layout["act_size"]:
        sys.exit("act_size %d in checkpoint, %d in layout" % (act, layout["act_size"]))
    names = [t[0] for t in layout["tables"]]
    for n in ("kinds", "spots", "links", "resources"):
        if n not in names:
            sys.exit("layout has no table named %r" % n)

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
    out = header_bytes(layout, E, hidden, layers, pointer, rule) + data
    open(a.out, "wb").write(out)
    print("wrote %s (%d bytes, %d params, state rule %s)" % (a.out, len(out), sum(r * c for r, c in shapes), rule))


if __name__ == "__main__":
    main()
