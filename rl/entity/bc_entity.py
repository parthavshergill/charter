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
from entity_torch import encode, pointer_logits, strip_moves, moves_logits  # noqa: E402
from encoders import MinGRU  # noqa: E402

LAYOUT = json.load(open(os.path.join(RL, "layout.json")))
TABLES = [(t["name"], t["offset"], t["rows"], t["width"]) for t in LAYOUT["tables"] if t["name"] != "moves"]
NAMES = [t[0] for t in TABLES]
TABLES_M = [(t["name"], t["offset"], t["rows"], t["width"]) for t in LAYOUT["tables"]]   # with the moves table
NAMES_M = [t[0] for t in TABLES_M]
ACTS = LAYOUT["act_size"] + 1


def collect(games, out, seed=7, bot="hand", worlds="island,not-catan", moves=False):
    """Like rl/imitation/collect.py, with the training settings: random maps and shuffled rows. `bot` labels every
    decision; `worlds` are dealt in turn; `moves` adds the per-move rows to the observation."""
    from charter import Game
    obs, masks, acts, game_ids, seats, returns = [], [], [], [], [], []
    ws = worlds.split(",")
    for k in range(games):
        gid = ws[k % len(ws)]
        cfg = {"game": gid, "seed": seed * 100000 + k, "vote_mode": "bot", "random_map": True,
               "slot_order": "shuffled", "declare_always": True, "move_rows": moves}
        g = None
        for n in (3 + (k // len(ws)) % 2, 4, 3, 5, 2, 6):   # 3 or 4 seats where the world allows them
            try:
                g = Game(dict(cfg, lineup=["caller"] * n))
                break
            except ValueError:
                continue
        while not g.over:
            m = g.mask()
            a = g.suggest(bot)
            if a < 0 or not m[a]:
                a = 0 if m[0] else int(np.flatnonzero(m)[0])
            obs.append(g.obs().astype(np.float16))
            masks.append(np.packbits(m))
            acts.append(a)
            game_ids.append(k)
            seats.append(g.seat)
            g.step(a)
        r = g.rewards()   # each seat's final reward: the value target for this game's decisions
        returns.extend(float(r[s]) for s in seats[len(returns):])
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    np.savez_compressed(out, obs=np.stack(obs), mask=np.stack(masks), action=np.array(acts, np.int16),
                        game=np.array(game_ids, np.int32), seat=np.array(seats, np.int8),
                        ret=np.array(returns, np.float32))
    print(f"{len(acts)} decisions from {games} games, wrote {out}", flush=True)


class EntityPolicy(torch.nn.Module):
    def __init__(self, E, hidden, pointer, moves=False, resid=False):
        """pointer: 0 none, 1 places and bank trades (layout 2). moves: per-move rows, and a pointer over them.
        resid: the encoder's residual block (charter_entity.cu, CE_RESID)."""
        super().__init__()
        self.tables, self.names, self.moves = (TABLES_M, NAMES_M, True) if moves else (TABLES, NAMES, False)
        self.w_in = torch.nn.ParameterList([torch.nn.Parameter(torch.randn(E, w) * (2 / w) ** 0.5)
                                            for _, _, _, w in self.tables])
        nt = len(self.tables)
        self.w_out = torch.nn.Parameter(torch.randn(hidden, nt * E) * (nt * E) ** -0.5)
        self.gru = MinGRU(hidden)
        self.decoder = torch.nn.Parameter(torch.randn(ACTS + 1, hidden) * hidden ** -0.5)
        self.ptr = (torch.nn.Parameter(torch.randn((4 if moves else 3) * E, hidden) * 0.1 * hidden ** -0.5)
                    if pointer or moves else None)
        self.E = E
        self.resid = torch.nn.ParameterList([torch.nn.Parameter(torch.ones(1, hidden)),
                                             torch.nn.Parameter(torch.zeros(1, hidden)),
                                             torch.nn.Parameter(torch.randn(hidden, hidden) * (2 / hidden) ** 0.5),
                                             torch.nn.Parameter(torch.zeros(hidden, hidden))]) if resid else None

    def forward(self, obs, state=None):
        """state: the MinGRU state before this step, (B, hidden); zeros if None."""
        ts = [(o, r, w) for _, o, r, w in self.tables]
        if self.moves:
            obs, macts, mreal = strip_moves(obs, ts, self.names.index("moves"), 1)
        h = encode(obs, ts, list(self.w_in), self.w_out, list(self.resid) if self.resid is not None else None)
        x, _ = self.gru(h, torch.zeros_like(h) if state is None else state)
        y = x @ self.decoder.T
        logits = y[:, :ACTS]
        if self.ptr is not None:
            logits = logits + pointer_logits(obs, ts, list(self.w_in), x, self.ptr, self.names.index("places"),
                                              self.names.index("resources"), LAYOUT["actions"]["place"],
                                              LAYOUT["actions"]["bank"], ACTS, E=self.E)
        if self.moves:
            logits = logits + moves_logits(obs, ts, list(self.w_in), x, self.ptr, self.names.index("moves"), macts,
                                           mreal, ACTS, self.E)
        return logits, y[:, ACTS]

    def blocks(self):
        return (list(self.w_in) + [self.w_out] + (list(self.resid) if self.resid is not None else [])
                + [self.decoder] + ([self.ptr] if self.ptr is not None else []) + [self.gru.w])

    def load_numpy(self, w_in, w_out, dec, ptr, grus, res=None):
        """Weights as entity_numpy.read_entity_bin returns them (one GRU layer)."""
        arrays = list(w_in) + [w_out] + ([np.reshape(a, p.shape) for a, p in zip(res, self.resid)] if res else []) \
            + [dec] + ([ptr] if ptr is not None else []) + [grus[0]]
        with torch.no_grad():
            for p, a in zip(self.blocks(), arrays):
                assert tuple(p.shape) == tuple(np.shape(a)), (p.shape, np.shape(a))
                p.copy_(torch.tensor(np.asarray(a, np.float32)))

    def save_puffer(self, path):
        save_puffer(self, path)


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
    ap.add_argument("--moves", action="store_true", help="per-move rows and a pointer over them (CE_MOVES)")
    ap.add_argument("--bot", default="hand", help="the bot whose choices are the labels: hand or table")
    ap.add_argument("--worlds", default="island,not-catan")
    ap.add_argument("--entity-dim", type=int, default=32)
    ap.add_argument("--hidden", type=int, default=128)
    ap.add_argument("--epochs", type=int, default=6)
    ap.add_argument("--batch", type=int, default=512)
    ap.add_argument("--lr", type=float, default=2e-3)
    ap.add_argument("--vf-coef", type=float, default=0.0, help="also fit the value to each seat's final reward")
    args = ap.parse_args()
    if args.collect:
        collect(args.collect, args.data, bot=args.bot, worlds=args.worlds, moves=args.moves)
    torch.set_num_threads(os.cpu_count())
    z = np.load(args.data)
    obs = torch.tensor(z["obs"].astype(np.float32))
    mask = torch.tensor(np.unpackbits(z["mask"], axis=1)[:, :ACTS].astype(bool))
    act = torch.tensor(z["action"].astype(np.int64))
    ret = torch.tensor(z["ret"]) if "ret" in z else None
    held = torch.tensor(z["game"] % 10 == 0)
    tr, te = (~held).nonzero().squeeze(1), held.nonzero().squeeze(1)
    torch.manual_seed(0)
    pointer = int(args.pointer or args.pointer_bank)
    pol = EntityPolicy(args.entity_dim, args.hidden, pointer, args.moves)
    opt = torch.optim.Adam(pol.parameters(), lr=args.lr)

    def loss_acc(idx):
        logits, value = pol(obs[idx])
        logits = logits.masked_fill(~mask[idx], -1e9)
        vloss = F.mse_loss(value, ret[idx]) if args.vf_coef and ret is not None else 0.0
        choice = mask[idx].sum(1) > 1   # agreement counted where there was a choice
        acc = ((logits.argmax(1) == act[idx]) & choice).float().sum() / choice.float().sum().clamp(min=1)
        return F.cross_entropy(logits, act[idx]) + args.vf_coef * vloss, acc

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
    meta = {"name": f"bc-{args.bot}-entity" + ["", "-pointer"][pointer] + ("-moves" if args.moves else ""),
            "layout": LAYOUT["version"], "moves": int(args.moves), "format": "puffer-entity",
            "encoder": "entity", "obs_size": LAYOUT["full_size"] if args.moves else LAYOUT["base_size"], "act_size": ACTS, "hidden": args.hidden,
            "layers": 1, "entity_dim": args.entity_dim, "pointer": pointer,
            "settings": {"vote_mode": "bot", "move_rows": bool(args.moves), "declare_always": True},
            "agreement_with_hand": round(a, 4)}
    json.dump(meta, open(args.out + ".json", "w"))
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
