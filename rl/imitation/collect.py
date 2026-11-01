"""Imitation data from the `hand` bot: every seat is a caller, and each decision's label is what `hand` would do.

    python3 rl/imitation/collect.py --games 400 --out results/imitation/hand.npz

Stores float16 observations, the packed mask, the action, the game and seat, and the step within that seat's
decisions. Settings follow round 1: `vote_mode=bot`, no per-move rows. Decisions where `hand` wants something with no
action (an offer) are labelled end turn, which is what the arena does when no event is accepted."""
import argparse
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "env"))
from charter import Game  # noqa: E402

TRAIN = ["island", "not-catan"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--games", type=int, default=400)
    ap.add_argument("--out", default="results/imitation/hand.npz")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--seats", default="4", help="seat count, or a range such as 2-6: game k cycles through it, "
                    "within what the game allows")
    ap.add_argument("--declare-always", action="store_true", help="offer declarations in every game (env declare_always)")
    args = ap.parse_args()
    lo, hi = (int(x) for x in (args.seats.split("-") + [args.seats])[:2])
    obs, masks, acts, game_ids, seats, fallback = [], [], [], [], [], 0
    for k in range(args.games):
        gid = TRAIN[k % len(TRAIN)]
        cfg = {"game": gid, "lineup": ["caller"] * 4, "seed": args.seed * 100000 + k, "vote_mode": "bot"}
        if args.declare_always:
            cfg["declare_always"] = True
        g = Game(cfg)
        if (lo, hi) != (4, 4):
            glo, ghi = g.seat_range
            choices = [n for n in range(lo, hi + 1) if glo <= n <= ghi] or [4]
            g.restart(["caller"] * choices[(k // len(TRAIN)) % len(choices)], args.seed * 100000 + k)
        while not g.over:
            m = g.mask()
            a = g.suggest("hand")
            if a < 0 or not m[a]:
                fallback += 1
                a = 0 if m[0] else int(np.flatnonzero(m)[0])
            obs.append(g.obs().astype(np.float16))
            masks.append(np.packbits(m))
            acts.append(a)
            game_ids.append(k)
            seats.append(g.seat)
            g.step(a)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    np.savez_compressed(args.out, obs=np.stack(obs), mask=np.stack(masks), action=np.array(acts, np.int16),
                        game=np.array(game_ids, np.int32), seat=np.array(seats, np.int8))
    print(f"{len(acts)} decisions from {args.games} games, {fallback} labelled by fallback, wrote {args.out}")


if __name__ == "__main__":
    main()
