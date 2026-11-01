"""Behaviour cloning of `hand` into the entity policy (optionally with the pointer decoder), saved as a PufferLib
checkpoint for a warm start (`--base.warm_start_path=FILE`, patch 0002).

    python3 rl/entity/bc_entity.py DATA.npz --out bc.bin [--pointer] [--entity-dim 32 --hidden 128]

DATA.npz is from rl/imitation/collect.py (or `--collect N` plays N games first). The model is entity_torch.encode,
PufferLib's MinGRU with zero state (rl/reference/encoders.py), the linear decoder, and with `--pointer` the pointer
scores (entity_torch.pointer_logits). The file's layout is entity_numpy.read_entity_bin's.
"""
import argparse
import json
import os
import sys

import numpy as np
import torch
import torch.nn.functional as F

HERE = os.path.dirname(os.path.abspath(__file__))
RL = os.path.dirname(HERE)
sys.path[:0] = [HERE, RL, os.path.join(RL, "reference"), os.path.join(RL, "env")]
from entity_torch import encode, pointer_logits  # noqa: E402
from encoders import MinGRU  # noqa: E402

LAYOUT = json.load(open(os.path.join(RL, "layout.json")))
TABLES = [(t["name"], t["offset"], t["rows"], t["width"]) for t in LAYOUT["tables"] if t["name"] != "moves"]
NAMES = [t[0] for t in TABLES]
ACTS = LAYOUT["act_size"] + 1


def collect(games, out, seed=7):
    """Like rl/imitation/collect.py, with the training settings: random maps and shuffled rows."""
    from charter import Game
    obs, masks, acts, game_ids = [], [], [], []
    for k in range(games):
        gid = ["island", "not-catan"][k % 2]
        n = 2 + k % 5   # 2 to 6 seats, as the env trains
        g = Game({"game": gid, "lineup": ["caller"] * n, "seed": seed * 100000 + k, "vote_mode": "bot",
                  "random_map": True, "slot_order": "shuffled", "declare_always": True})
        while not g.over:
            m = g.mask()
            a = g.suggest("hand")
            if a < 0 or not m[a]:
                a = 0 if m[0] else int(np.flatnonzero(m)[0])
            obs.append(g.obs().astype(np.float16))
            masks.append(np.packbits(m))
            acts.append(a)
            game_ids.append(k)
            g.step(a)
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    np.savez_compressed(out, obs=np.stack(obs), mask=np.stack(masks), action=np.array(acts, np.int16),
                        game=np.array(game_ids, np.int32))
    print(f"{len(acts)} decisions from {games} games, wrote {out}", flush=True)


class EntityPolicy(torch.nn.Module):
    def __init__(self, E, hidden, pointer):
        """pointer: 0 none, 1 spots and links, 2 also bank trades."""
        super().__init__()
        self.w_in = torch.nn.ParameterList([torch.nn.Parameter(torch.randn(E, w) * (2 / w) ** 0.5)
                                            for _, _, _, w in TABLES])
        self.w_out = torch.nn.Parameter(torch.randn(hidden, len(TABLES) * E) * (len(TABLES) * E) ** -0.5)
        self.gru = MinGRU(hidden)
        self.decoder = torch.nn.Parameter(torch.randn(ACTS + 1, hidden) * hidden ** -0.5)
        self.ptr = torch.nn.Parameter(torch.randn(3 * E, hidden) * 0.1 * hidden ** -0.5) if pointer else None
        self.E = E

    def forward(self, obs):
        ts = [(o, r, w) for _, o, r, w in TABLES]
        h = encode(obs, ts, list(self.w_in), self.w_out)
        x, _ = self.gru(h, torch.zeros_like(h))
        y = x @ self.decoder.T
        logits = y[:, :ACTS]
        if self.ptr is not None:
            logits = logits + pointer_logits(obs, ts, list(self.w_in), x, self.ptr, NAMES.index("places"),
                                              NAMES.index("resources"), LAYOUT["actions"]["place"],
                                              LAYOUT["actions"]["bank"], ACTS)
        return logits, y[:, ACTS]

    def blocks(self):
        return list(self.w_in) + [self.w_out, self.decoder] + ([self.ptr] if self.ptr is not None else []) + [self.gru.w]


def save_puffer(pol, path):
    out = []
    for b in pol.blocks():
        a = b.detach().float().numpy().ravel()
        out.append(np.concatenate([a, np.zeros((-len(a)) % 8, np.float32)]))
    np.concatenate(out).astype("<f4").tofile(path)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("data")
    ap.add_argument("--collect", type=int, default=0, help="play this many games first and write DATA")
    ap.add_argument("--out", required=True)
    ap.add_argument("--pointer", action="store_true", help="spots and links")
    ap.add_argument("--pointer-bank", action="store_true", help="spots, links and bank trades")
    ap.add_argument("--entity-dim", type=int, default=32)
    ap.add_argument("--hidden", type=int, default=128)
    ap.add_argument("--epochs", type=int, default=6)
    ap.add_argument("--batch", type=int, default=512)
    ap.add_argument("--lr", type=float, default=2e-3)
    args = ap.parse_args()
    if args.collect:
        collect(args.collect, args.data)
    torch.set_num_threads(os.cpu_count())
    z = np.load(args.data)
    obs = torch.tensor(z["obs"].astype(np.float32))
    mask = torch.tensor(np.unpackbits(z["mask"], axis=1)[:, :ACTS].astype(bool))
    act = torch.tensor(z["action"].astype(np.int64))
    held = torch.tensor(z["game"] % 10 == 0)
    tr, te = (~held).nonzero().squeeze(1), held.nonzero().squeeze(1)
    torch.manual_seed(0)
    pointer = int(args.pointer or args.pointer_bank)
    pol = EntityPolicy(args.entity_dim, args.hidden, pointer)
    opt = torch.optim.Adam(pol.parameters(), lr=args.lr)

    def loss_acc(idx):
        logits, _ = pol(obs[idx])
        logits = logits.masked_fill(~mask[idx], -1e9)
        choice = mask[idx].sum(1) > 1   # agreement counted where there was a choice
        acc = ((logits.argmax(1) == act[idx]) & choice).float().sum() / choice.float().sum().clamp(min=1)
        return F.cross_entropy(logits, act[idx]), acc

    for ep in range(args.epochs):
        perm = tr[torch.randperm(len(tr))]
        for i in range(0, len(perm), args.batch):
            loss, _ = loss_acc(perm[i:i + args.batch])
            opt.zero_grad()
            loss.backward()
            opt.step()
        with torch.no_grad():
            ls, accs = zip(*[loss_acc(te[i:i + 4096]) for i in range(0, len(te), 4096)])
        a = float(np.mean([float(x) for x in accs]))
        print(f"epoch {ep}: held-out loss {np.mean([float(x) for x in ls]):.3f}, agreement with hand where there "
              f"was a choice {100 * a:.1f}%", flush=True)
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    save_puffer(pol, args.out)
    meta = {"name": "bc-hand-entity" + ["", "-pointer"][pointer], "layout": LAYOUT["version"], "format": "puffer-entity",
            "encoder": "entity", "obs_size": LAYOUT["base_size"], "act_size": ACTS, "hidden": args.hidden,
            "layers": 1, "entity_dim": args.entity_dim, "pointer": pointer,
            "settings": {"vote_mode": "bot", "move_rows": False, "declare_always": 1},
            "agreement_with_hand": round(a, 4)}
    json.dump(meta, open(args.out + ".json", "w"))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
