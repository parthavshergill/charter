#!/usr/bin/env python3
"""Convert a PufferLib checkpoint to a Lean policy weights file (.chpw).

Usage:
  policy_weights.py CKPT.bin --out OUT.chpw [--gru-state carry|turn|zero]

CKPT.bin.json must sit next to CKPT.bin (keys: entity_dim, hidden, layers,
act_size, pointer, layout, moves). The layout (1 or 2) comes from the meta's
`layout`, 1 if it has none; `moves` (per-move rows) adds the ninth table. The
tables are in policy_diff.py.

The output is a header followed by the .bin bytes unchanged. The format is
described in Server/Policy/Net.lean.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from policy_diff import LAYOUTS, STATE_RULES, V2M, block_shapes, header_bytes, pad8  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ckpt")
    ap.add_argument("--out", required=True)
    ap.add_argument("--moves-order", choices=["legal", "ranked"],
                    help="for a checkpoint with per-move rows, if the meta has no moves_order: the order of the table "
                         "of moves it trained with. legal: before harness 5fde545 (end turn, trades, declarations, "
                         "placements); ranked: 5fde545 and later (end turn and votes, placements, trades, declarations)")
    ap.add_argument("--mix-k", type=int, help="the decision-time blend: how many of the policy's best legal actions "
                    "to try (rl/entity/entity_numpy.py choose_mix); with --mix-c. Off when not given.")
    ap.add_argument("--mix-c", type=float, help="the blend's weight c: each candidate scores logit + c * (V(after) - V(now))")
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
    moves = bool(meta.get("moves")) or bool((meta.get("settings") or {}).get("move_rows"))
    if moves:
        if version != 2:
            sys.exit("per-move rows are known for layout 2 only")
        layout = V2M   # a ninth encoder table, `moves`, and pointer 4
    E = int(meta.get("entity_dim", 32))
    hidden, layers = int(meta["hidden"]), int(meta["layers"])
    act, pointer = int(meta["act_size"]), int(meta.get("pointer", 0))
    if act not in (layout["act_size"], layout["act_size"] + 1):
        sys.exit("act_size %d in checkpoint, %d (or one more, for the no-op) in layout %d" % (act, layout["act_size"], version))
    if version == 2 and pointer not in (0, 3, 4):
        # entity2's layout-2 meta writes pointer 1 for the layout-2 pointer (places and bank, and moves rows too).
        pointer = 4 if moves else 3
    want_obs = sum(t[2] * t[3] for t in layout["tables"])
    if int(meta.get("obs_size", want_obs)) != want_obs:
        sys.exit("obs_size %s in the meta, %d for this layout" % (meta.get("obs_size"), want_obs))

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
    flags = None
    if moves:
        settings = meta.get("settings") or {}
        order = meta.get("moves_order") or a.moves_order
        if order not in ("legal", "ranked"):
            sys.exit("the meta has no moves_order: say which table of moves the checkpoint trained with, "
                     "--moves-order legal (harness before 5fde545) or ranked (5fde545 and later)")
        if meta.get("moves_order") and a.moves_order and a.moves_order != meta["moves_order"]:
            sys.exit("--moves-order %s, but the meta says %s" % (a.moves_order, meta["moves_order"]))
        prune = bool(settings.get("prune_declares", meta.get("prune_declares", False)))
        once = bool(settings.get("declare_once_per_turn", meta.get("declare_once_per_turn", False)))
        if once and not prune:
            sys.exit("declare_once_per_turn works only with prune_declares, and the meta has one without the other")
        flags = (1 if prune else 0) + (2 if once else 0) + (4 if order == "ranked" else 0)
    settings = meta.get("settings") or {}
    mix_k = a.mix_k if a.mix_k is not None else settings.get("mix_k")
    mix_c = a.mix_c if a.mix_c is not None else settings.get("mix_c")
    mix = None
    if mix_k is not None or mix_c is not None:
        if mix_k is None or mix_c is None:
            sys.exit("the blend needs both a candidate count and a weight: --mix-k K --mix-c C")
        if flags is None:
            sys.exit("the blend is written in format 5, which needs a checkpoint with per-move rows")
        mix = (int(mix_k), float(mix_c))
    out = header_bytes(layout, E, hidden, layers, pointer, rule, act, flags, mix) + data
    open(a.out, "wb").write(out)
    extra = "" if flags is None else ", moves order %s, prune_declares %s, declare_once_per_turn %s" % (
        "ranked" if flags & 4 else "legal", bool(flags & 1), bool(flags & 2))
    if mix:
        extra += ", blend over %d candidates at c = %g" % mix
    print("wrote %s (%d bytes, %d params, state rule %s%s)" % (a.out, len(out), sum(r * c for r, c in shapes), rule, extra))


if __name__ == "__main__":
    main()
