"""Behaviour cloning of `hand` into the flat policy, saved as a PufferLib checkpoint for a warm start.

    python3 rl/imitation/bc.py results/imitation/hand.npz --out results/imitation/bc.bin [--hidden 128 --layers 1]

The GRU state is zero at every decision here (no sequences), so this trains the encoder, the GRU's input path and
the decoder. Training then carries the state. The checkpoint has PufferLib's layout (rl/reference/policy.py), and
`--base.warm_start_path=<file>` loads it with rl/puffer/patches/0002-warm-start.patch. A meta JSON is written next
to it, so rl/eval can play it."""
import argparse
import json
import os
import sys

import numpy as np
import torch
import torch.nn.functional as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "reference"))
from encoders import LAYOUT, Policy  # noqa: E402

ACTS = LAYOUT["act_size"] + 1


def save_puffer(pol, path):
    """encoder, decoder, then each GRU block, each padded to a multiple of 8 floats."""
    blocks = [pol.encoder.w, pol.decoder] + [g.w for g in pol.grus]
    out = []
    for b in blocks:
        a = b.detach().float().numpy().ravel()
        pad = (-len(a)) % 8
        out.append(np.concatenate([a, np.zeros(pad, np.float32)]))
    np.concatenate(out).astype("<f4").tofile(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("data")
    ap.add_argument("--out", default="results/imitation/bc.bin")
    ap.add_argument("--hidden", type=int, default=128)
    ap.add_argument("--layers", type=int, default=1)
    ap.add_argument("--epochs", type=int, default=4)
    ap.add_argument("--batch", type=int, default=512)
    ap.add_argument("--lr", type=float, default=1e-3)
    args = ap.parse_args()
    z = np.load(args.data)
    obs = torch.tensor(z["obs"].astype(np.float32))
    mask = torch.tensor(np.unpackbits(z["mask"], axis=1)[:, :ACTS - 1].astype(bool))
    act = torch.tensor(z["action"].astype(np.int64))
    held = torch.tensor(z["game"] % 10 == 0)
    tr, te = (~held).nonzero().squeeze(1), held.nonzero().squeeze(1)
    torch.manual_seed(0)
    pol = Policy("flat", hidden=args.hidden, layers=args.layers)
    opt = torch.optim.Adam(pol.parameters(), lr=args.lr)

    def loss_acc(idx):
        logits, _, _ = pol(obs[idx], pol.initial_state(len(idx)))
        logits = logits[:, :ACTS - 1].masked_fill(~mask[idx], -1e9)
        return F.cross_entropy(logits, act[idx]), (logits.argmax(1) == act[idx]).float().mean()

    for ep in range(args.epochs):
        perm = tr[torch.randperm(len(tr))]
        for i in range(0, len(perm), args.batch):
            loss, _ = loss_acc(perm[i:i + args.batch])
            opt.zero_grad()
            loss.backward()
            opt.step()
        with torch.no_grad():
            l, a = loss_acc(te)
        print(f"epoch {ep}: held-out loss {l:.3f}, agreement with hand {100 * a:.1f}%", flush=True)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    save_puffer(pol, args.out)
    json.dump({"name": "bc-hand", "format": "puffer-flat", "obs_size": LAYOUT["base_size"], "act_size": ACTS,
               "hidden": args.hidden, "layers": args.layers, "settings": {"vote_mode": "bot"},
               "agreement_with_hand": round(float(a), 4)}, open(args.out + ".json", "w"))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
