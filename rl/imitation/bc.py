"""Behaviour cloning of `hand` into the flat policy, saved as a PufferLib checkpoint for a warm start.

    python3 rl/imitation/bc.py results/imitation/hand.npz --out results/imitation/bc.bin [--hidden 128 --layers 1]

By default the GRU state is zero at every decision (no sequences), which RL training never has. `--sequences`
replays each seat's whole game in tick order, as PufferLib does: on other seats' ticks the seat sees zeros (or, with
`--stale-wait`, its own last observation, matching `env.stale_wait = 1`), and its state moves. Then memory means the
same in BC, training and eval (`Player.wait`).

`--vf-coef C` (for example 1; default 0, as before) also trains the value output, the decoder's last row, which PufferLib's critic reads: its
target is `gamma ** (ticks to the end) * ret`, the seat's final return from `collect.py`. Without it a warm start's
critic is random. With `--sequences` the value is fitted on waiting ticks too, as training does. The checkpoint has PufferLib's layout (rl/reference/policy.py), and
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
    ap.add_argument("--sequences", action="store_true", help="replay whole games per seat, waiting ticks included")
    ap.add_argument("--stale-wait", action="store_true", help="waiting ticks see the seat's last observation")
    ap.add_argument("--vf-coef", type=float, default=0.0, help="weight of the value loss, for example 1; 0 (the default) trains no value")
    ap.add_argument("--gamma", type=float, default=0.995)
    args = ap.parse_args()
    if args.sequences:
        return main_sequences(args)
    z = np.load(args.data)
    obs = torch.tensor(z["obs"].astype(np.float32))
    mask = torch.tensor(np.unpackbits(z["mask"], axis=1)[:, :ACTS - 1].astype(bool))
    act = torch.tensor(z["action"].astype(np.int64))
    held = torch.tensor(z["game"] % 10 == 0)
    tr, te = (~held).nonzero().squeeze(1), held.nonzero().squeeze(1)
    torch.manual_seed(0)
    pol = Policy("flat", hidden=args.hidden, layers=args.layers)
    opt = torch.optim.Adam(pol.parameters(), lr=args.lr)

    vtarget = value_targets(z, args.gamma)

    def loss_acc(idx):
        logits, value, _ = pol(obs[idx], pol.initial_state(len(idx)))
        logits = logits[:, :ACTS - 1].masked_fill(~mask[idx], -1e9)
        loss = F.cross_entropy(logits, act[idx])
        if vtarget is not None and args.vf_coef > 0:
            loss = loss + args.vf_coef * F.mse_loss(value, vtarget[idx])
        return loss, (logits.argmax(1) == act[idx]).float().mean()

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
    write(pol, args, a)


def write(pol, args, agreement):
    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    save_puffer(pol, args.out)
    settings = {"vote_mode": "bot"}
    if args.stale_wait:
        settings["stale_wait"] = True
    json.dump({"name": "bc-hand", "format": "puffer-flat", "obs_size": LAYOUT["base_size"], "act_size": ACTS,
               "layout": LAYOUT["version"], "hidden": args.hidden, "layers": args.layers, "settings": settings,
               "bc": {"sequences": args.sequences, "vf_coef": args.vf_coef, "gamma": args.gamma},
               "agreement_with_hand": round(float(agreement), 4)}, open(args.out + ".json", "w"))
    print(f"wrote {args.out}")


def value_targets(z, gamma):
    """`gamma ** (ticks to the end) * ret` for each decision, or None if the data has no returns."""
    if "ret" not in z.files or "tick" not in z.files:
        print("no returns in the data (an old collect.py): the value is not trained")
        return None
    game, tick = z["game"], z["tick"].astype(np.int64)
    last = np.zeros(game.max() + 1, np.int64)
    np.maximum.at(last, game, tick)
    return torch.tensor((gamma ** (last[game] - tick)) * z["ret"], dtype=torch.float32)


def main_sequences(args):
    """BC over whole games: each (game, seat) is one sequence over every tick of the game."""
    z = np.load(args.data)
    if "tick" not in z.files:
        raise SystemExit("--sequences needs data from the current collect.py (with tick and ret)")
    obs16, game, seat, tick = z["obs"], z["game"], z["seat"].astype(np.int64), z["tick"].astype(np.int64)
    mask_all = np.unpackbits(z["mask"], axis=1)[:, :ACTS - 1].astype(bool)
    act_all, ret = z["action"].astype(np.int64), z["ret"].astype(np.float32)
    starts = np.flatnonzero(np.r_[True, game[1:] != game[:-1]])
    ends = np.r_[starts[1:], len(game)]
    seqs = [(a, b, s) for a, b in zip(starts, ends) for s in np.unique(seat[a:b])]
    held = [x for x in seqs if game[x[0]] % 10 == 0]
    train = [x for x in seqs if game[x[0]] % 10 != 0]
    torch.manual_seed(0)
    rng = np.random.default_rng(0)
    pol = Policy("flat", hidden=args.hidden, layers=args.layers)
    opt = torch.optim.Adam(pol.parameters(), lr=args.lr)
    obs_size = obs16.shape[1]

    def batch_loss(batch):
        T = max(b - a for a, b, _ in batch)
        B = len(batch)
        x = torch.zeros(B, T, obs_size)
        own = torch.zeros(B, T, dtype=torch.bool)
        acts = torch.zeros(B, T, dtype=torch.long)
        masks = torch.ones(B, T, ACTS - 1, dtype=torch.bool)
        vt = torch.zeros(B, T)
        live = torch.zeros(B, T, dtype=torch.bool)
        for i, (a, b, s) in enumerate(batch):
            n = b - a
            mine = seat[a:b] == s
            o = torch.tensor(obs16[a:b].astype(np.float32))
            if args.stale_wait:
                # Each tick sees the seat's own latest observation; ticks before its first decision see zeros.
                idx = np.where(mine, np.arange(n), -1)
                idx = np.maximum.accumulate(idx)
                o = torch.where(torch.tensor(idx >= 0)[:, None], o[np.maximum(idx, 0)], torch.zeros_like(o))
            else:
                o = o * torch.tensor(mine, dtype=torch.float32)[:, None]
            x[i, :n] = o
            own[i, :n] = torch.tensor(mine)
            acts[i, :n] = torch.tensor(act_all[a:b])
            masks[i, :n] = torch.tensor(mask_all[a:b])
            r = ret[a:b][mine][0]
            vt[i, :n] = torch.tensor((args.gamma ** (tick[b - 1] - tick[a:b])) * r, dtype=torch.float32)
            live[i, :n] = True
        state = pol.initial_state(B)
        logits_t, values_t = [], []
        for t in range(T):
            lg, v, state = pol(x[:, t], state)
            logits_t.append(lg)
            values_t.append(v)
        logits = torch.stack(logits_t, 1)[:, :, :ACTS - 1].masked_fill(~masks, -1e9)
        values = torch.stack(values_t, 1)
        loss = F.cross_entropy(logits[own], acts[own])
        if args.vf_coef > 0:
            loss = loss + args.vf_coef * F.mse_loss(values[live], vt[live])
        acc = (logits[own].argmax(1) == acts[own]).float().mean()
        return loss, acc

    a = torch.tensor(0.0)
    for ep in range(args.epochs):
        order = rng.permutation(len(train))
        for i in range(0, len(order), 8):
            loss, _ = batch_loss([train[j] for j in order[i:i + 8]])
            opt.zero_grad()
            loss.backward()
            opt.step()
        with torch.no_grad():
            accs = [batch_loss(held[i:i + 8]) for i in range(0, len(held), 8)]
        l = sum(x[0] for x in accs) / len(accs)
        a = sum(x[1] for x in accs) / len(accs)
        print(f"epoch {ep}: held-out loss {l:.3f}, agreement with hand {100 * a:.1f}%", flush=True)
    write(pol, args, a)


if __name__ == "__main__":
    main()
