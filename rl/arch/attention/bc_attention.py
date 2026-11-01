"""Behaviour cloning of `hand` into the attention policy, saved as a PufferLib checkpoint for a warm start.

    python3 rl/arch/attention/bc_attention.py HAND_NPZ --out bc.bin [--hidden 128 --epochs 4]

HAND_NPZ comes from rl/imitation/collect.py. This is rl/imitation/bc.py with the attention encoder
(attention_ref.forward) in place of the flat one: the same data, loss, held-out split (game id mod 10 == 0) and
GRU state at zero. The checkpoint has the layout attention_np.read_bin reads, which is the order the CUDA encoder
registers its weights: the encoder's weights, the decoder (act + 1 rows, the last is the value), then the MinGRU.
"""
import argparse
import json
import os
import sys

import numpy as np
import torch
import torch.nn.functional as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", "reference"))
import attention_ref as R  # noqa: E402
from encoders import LAYOUT, MinGRU  # noqa: E402

ACTS = LAYOUT["act_size"] + 1
LAYOUT_PATH = os.path.join(HERE, "..", "..", "layout.json")


class AttentionPolicy(torch.nn.Module):
    def __init__(self, hidden, seed=0):
        super().__init__()
        self.plan = R.load_plan(LAYOUT_PATH)
        p = R.init_params(self.plan, hidden, seed)
        self.names = [n for n, _ in R.param_shapes(self.plan, hidden)]
        self.enc = torch.nn.ParameterDict({n: torch.nn.Parameter(p[n].float()) for n in self.names})
        self.gru = MinGRU(hidden)
        self.decoder = torch.nn.Parameter(torch.randn(ACTS + 1, hidden) * hidden ** -0.5)
        self.hidden = hidden

    def forward(self, obs):
        x = R.forward(self.plan, dict(self.enc), obs)
        x, _ = self.gru(x, torch.zeros(obs.shape[0], self.hidden))
        y = x @ self.decoder.T
        return y[:, :-1]

    def blocks(self):
        return [self.enc[n] for n in self.names] + [self.decoder, self.gru.w]


def save_puffer(pol, path):
    out = []
    for b in pol.blocks():
        a = b.detach().float().numpy().ravel()
        out.append(np.concatenate([a, np.zeros((-len(a)) % 8, np.float32)]))
    np.concatenate(out).astype("<f4").tofile(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("data")
    ap.add_argument("--out", required=True)
    ap.add_argument("--hidden", type=int, default=128)
    ap.add_argument("--epochs", type=int, default=4)
    ap.add_argument("--batch", type=int, default=512)
    ap.add_argument("--lr", type=float, default=1e-3)
    args = ap.parse_args()
    torch.set_num_threads(os.cpu_count())
    z = np.load(args.data)
    obs = torch.tensor(z["obs"].astype(np.float32))
    mask = torch.tensor(np.unpackbits(z["mask"], axis=1)[:, :ACTS - 1].astype(bool))
    act = torch.tensor(z["action"].astype(np.int64))
    held = torch.tensor(z["game"] % 10 == 0)
    tr, te = (~held).nonzero().squeeze(1), held.nonzero().squeeze(1)
    print(f"{len(tr)} training decisions, {len(te)} held out", flush=True)
    torch.manual_seed(0)
    pol = AttentionPolicy(args.hidden)
    opt = torch.optim.Adam(pol.parameters(), lr=args.lr)

    def loss_acc(idx):
        logits = pol(obs[idx])[:, :ACTS - 1].masked_fill(~mask[idx], -1e9)
        return F.cross_entropy(logits, act[idx]), (logits.argmax(1) == act[idx]).float().mean()

    for ep in range(args.epochs):
        perm = tr[torch.randperm(len(tr))]
        for i in range(0, len(perm), args.batch):
            loss, _ = loss_acc(perm[i:i + args.batch])
            opt.zero_grad()
            loss.backward()
            opt.step()
        with torch.no_grad():
            ls, accs = zip(*(loss_acc(te[i:i + 4096]) for i in range(0, len(te), 4096)))
            l, a = float(sum(ls) / len(ls)), float(sum(accs) / len(accs))
        print(f"epoch {ep}: held-out loss {l:.3f}, agreement with hand {100 * a:.1f}%", flush=True)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    save_puffer(pol, args.out)
    json.dump({"name": "bc-hand-attention", "format": "puffer-attention", "encoder": "attention",
               "obs_size": LAYOUT["base_size"], "act_size": ACTS, "hidden": args.hidden, "layers": 1,
               "settings": {"vote_mode": "bot"}, "agreement_with_hand": round(a, 4)}, open(args.out + ".json", "w"))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
