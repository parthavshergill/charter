"""Learn from the improved move (rl/ROUND4.md, `entity4` item 1): train the policy toward the decision-time blend's
choice, so the policy itself learns what the lookahead finds.

The blend (`#mixKcC`, entity_numpy.EntityNet.choose_mix) scores the policy's K best legal moves by
`logit + C * (V(after) - V(now))`, each move tried on a copy of the game through `Engine.step`. The improved policy
is

    target(a) = softmax over legal moves of  logit(a) + C * dV(a),   dV = 0 for moves not tried

(Gumbel-style policy improvement, with the value change standing in for Q). Its best move is the blend's move.

    collect:  play games with the blend at one seat, `table` bots at the others, and record each decision
              (observation, recurrent state before it, mask, the K moves tried and their dV, the move played)
    distill:  start from the same weights and fit the policy to the targets (cross-entropy), keeping the value
              head close to the recording network's value

    python3 rl/entity/expert_iter.py collect CKPT OUT.npz --games 200 --seed 1 [--worlds island,not-catan,pack-train]
    python3 rl/entity/expert_iter.py distill CKPT OUT.bin DATA1.npz [DATA2.npz ...] [--epochs 2 --lr 3e-4]

CKPT is a `puffer-entity` checkpoint with its meta beside it (CKPT.json), with per-move rows (`moves: 1`). The
recurrent state is taken as recorded, so a decision is fitted with the state the playing network had there.
"""
import argparse
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RL = os.path.dirname(HERE)
sys.path[:0] = [HERE, RL, os.path.join(RL, "reference"), os.path.join(RL, "env")]

TRAIN_WORLDS = "island,not-catan,pack-train"


def game_config(gid, n, seed, random_map, settings):
    """A training game as charter.h starts one (rl/puffer/charter.h), with the meta's switches."""
    cfg = {"game": gid, "lineup": ["caller"] * n, "seed": int(seed), "vote_mode": "bot", "slot_order": "shuffled",
           "move_rows": True, "law_every": 8, "random_map": bool(random_map), "preview": True,
           "declare_always": True}
    for key in ("prune_declares", "declare_once_per_turn"):
        if settings.get(key):
            cfg[key] = True
    return cfg


def make_game(gid, rng, seed, settings):
    from charter import Game
    rmap = rng.random() < 0.5
    for n in ((4, 3) if rng.random() < 0.5 else (3, 4)) + (5, 2, 6):
        try:
            return Game(game_config(gid, n, seed, rmap, settings)), n
        except ValueError:
            continue
    raise ValueError(f"no seat count works for {gid}")


def collect(ckpt, out, games, seed, worlds, k, c, explore):
    from charter import Game  # noqa: F401  (loads the engine)
    from entity_numpy import load_entity
    meta = json.load(open(ckpt + ".json"))
    assert meta.get("moves"), "needs per-move rows"
    settings = dict(meta.get("settings", {}))
    net = load_entity(ckpt, meta)
    H = meta["hidden"]
    rng = np.random.default_rng(seed)
    ws = worlds.split(",")
    rec = {key: [] for key in ("obs", "state", "mask", "cand", "dv", "action", "value", "game", "seat", "world",
                               "table")}
    rets, nwin, ndec = [], 0, 0
    for i in range(games):
        gid = ws[i % len(ws)]
        g, n = make_game(gid, rng, seed * 1000003 + i, settings)
        at = int(rng.integers(n))
        player = net.player(seed + i)
        player.stale_wait = True
        start = len(rec["action"])
        while not g.over:
            if g.seat == at:
                state_in = player.state[0].copy()
                obs = g.obs()
                mask = g.mask()
                player.last_obs = np.array(obs, np.float32)
                logits, v, player.state = net.forward(obs, player.state)
                logits = logits[:len(mask)].astype(np.float64)
                logits[mask == 0] = -np.inf
                legal = np.flatnonzero(mask)
                a = int(np.argmax(logits))
                if len(legal) > 1 and not g.voting:
                    cand = legal[np.argsort(-logits[legal])][:k]
                    v_now = float(v)
                    dv = np.zeros(len(cand))
                    for j, b in enumerate(cand):
                        if b == 0:
                            continue
                        g2 = g.copy()
                        g2.step(int(b))
                        if g2.over:
                            dv[j] = float(g2.rewards()[at]) - v_now
                        elif g2.seat == at:
                            _, v2, _ = net.forward(g2.obs(), player.state)
                            dv[j] = float(v2) - v_now
                    score = logits[cand] + c * dv
                    a = int(cand[np.argmax(score)])
                    if explore > 0 and rng.random() < explore:   # sometimes play another of the improved moves
                        p = np.exp(score - score.max())
                        a = int(rng.choice(cand, p=p / p.sum()))
                    pad = k - len(cand)
                    rec["obs"].append(np.asarray(obs, np.float16))
                    rec["state"].append(state_in.astype(np.float32))
                    rec["mask"].append(np.packbits(mask.astype(np.uint8)))
                    rec["cand"].append(np.concatenate([cand, -np.ones(pad, int)]).astype(np.int16))
                    rec["dv"].append(np.concatenate([dv, np.zeros(pad)]).astype(np.float32))
                    rec["action"].append(a)
                    rec["value"].append(v_now)
                    rec["game"].append(i)
                    rec["seat"].append(at)
                    rec["world"].append(gid)
                    tb = g.suggest("table")   # the table bot's move here, for item 2's imitation loss
                    rec["table"].append(tb if tb >= 0 and mask[tb] else -1)
                ndec += 1
            else:
                m = g.mask()
                a = g.suggest("table")
                if a < 0 or not m[a]:
                    a = 0 if m[0] else int(np.flatnonzero(m)[0])
                player.wait(g.obs_size)
            if not g.step(a):
                g.step(int(g.legal()[0]))
        r = float(g.rewards()[at])
        nwin += int(int(g.info()["winner"]) == at)
        rets.extend([r] * (len(rec["action"]) - start))
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    np.savez_compressed(out, obs=np.stack(rec["obs"]), state=np.stack(rec["state"]), mask=np.stack(rec["mask"]),
                        cand=np.stack(rec["cand"]), dv=np.stack(rec["dv"]),
                        action=np.array(rec["action"], np.int16), value=np.array(rec["value"], np.float32),
                        ret=np.array(rets, np.float32), game=np.array(rec["game"], np.int32),
                        seat=np.array(rec["seat"], np.int8), world=np.array(rec["world"]),
                        table=np.array(rec["table"], np.int16))
    print(f"{games} games, {nwin} won by the blend seat, {ndec} decisions, {len(rec['action'])} with a choice; "
          f"wrote {out}", flush=True)


def distill(ckpt, out, data, epochs, lr, c, vf_coef, batch, max_rows, imitate=0.0):
    import torch
    import torch.nn.functional as F
    from bc_entity import EntityPolicy, ACTS
    from entity_numpy import read_entity_bin, base_tables, LAYOUT as LAYOUT_PATH
    meta = json.load(open(ckpt + ".json"))
    layout = json.load(open(LAYOUT_PATH))
    E, H = meta["entity_dim"], meta["hidden"]
    resid = bool(meta.get("resid", 0))
    pol = EntityPolicy(E, H, 1, moves=True, resid=resid)
    got = read_entity_bin(ckpt, base_tables(layout, True), E, H, meta["layers"], meta["act_size"], 1, resid)
    pol.load_numpy(*got)
    teacher = EntityPolicy(E, H, 1, moves=True, resid=resid)
    teacher.load_numpy(*got)
    teacher.requires_grad_(False)
    torch.set_num_threads(os.cpu_count())

    zs = [np.load(p) for p in data]
    cat = lambda key: np.concatenate([z[key] for z in zs])
    obs, state, maskb = cat("obs"), cat("state"), cat("mask")
    cand, dv, value = cat("cand").astype(np.int64), cat("dv"), cat("value")
    # Item 2: the table bot's move where it builds or trades (not end turn, not a declaration), else -1.
    table = cat("table").astype(np.int64) if imitate and all("table" in z for z in zs) else -np.ones(len(cand), np.int64)
    act_decl, act_place = layout["actions"]["declare"], layout["actions"]["place"]
    table[(table <= 0) | ((table >= act_decl) & (table < act_place))] = -1
    game = np.concatenate([z["game"] + 1000000 * j for j, z in enumerate(zs)])
    if max_rows and len(obs) > max_rows:
        keep = np.random.default_rng(0).choice(len(obs), max_rows, replace=False)
        obs, state, maskb, cand, dv, value, game, table = (x[keep] for x in (obs, state, maskb, cand, dv, value,
                                                                              game, table))
    held = game % 10 == 0
    tr, te = np.flatnonzero(~held), np.flatnonzero(held)
    print(f"{len(obs)} decisions ({len(tr)} train, {len(te)} held out), from {len(data)} files", flush=True)

    def batch_of(idx):
        o = torch.tensor(obs[idx].astype(np.float32))
        s = torch.tensor(state[idx])
        m = torch.tensor(np.unpackbits(maskb[idx], axis=1)[:, :ACTS].astype(bool))
        cd = torch.tensor(cand[idx])
        d = torch.tensor(dv[idx])
        return o, s, m, cd, d, torch.tensor(value[idx]), torch.tensor(table[idx])

    def losses(idx):
        o, s, m, cd, d, v0, tb = batch_of(idx)
        with torch.no_grad():
            tl, _ = teacher(o, s)
            tl = tl.masked_fill(~m, -1e9)
            bonus = torch.zeros_like(tl)
            ok = cd >= 0
            bonus.scatter_add_(1, cd.clamp(min=0), torch.where(ok, c * d, torch.zeros_like(d)))
            target = F.softmax(tl + bonus, 1)
            best = (tl + bonus).argmax(1)
            t_best = tl.argmax(1)
        logits, val = pol(o, s)
        logp = F.log_softmax(logits.masked_fill(~m, -1e9), 1)
        ce = -(target * logp).sum(1).mean()
        ent = -(target * torch.log(target.clamp(min=1e-12))).sum(1).mean()
        vloss = F.mse_loss(val, v0)
        agree = (logits.masked_fill(~m, -1e9).argmax(1) == best).float().mean()
        base_agree = (t_best == best).float().mean()
        # Item 2: where the improved move ends the turn but the table bot builds or trades, imitate the table bot.
        passes = (best == 0) & (tb >= 0)
        imi = -(logp.gather(1, tb.clamp(min=0)[:, None])[:, 0] * passes.float()).sum() / passes.float().sum().clamp(min=1)
        loss = ce + vf_coef * vloss + (imitate * imi if imitate else 0.0)
        return loss, ce - ent, vloss, agree, base_agree, imi, passes.float().mean()

    opt = torch.optim.Adam(pol.parameters(), lr=lr)

    def evaluate(tag):
        with torch.no_grad():
            r = [losses(te[i:i + 2048]) for i in range(0, len(te), 2048)]
        kl, vl, ag, bag, imi, ps = (float(np.mean([float(x[j]) for x in r])) for j in (1, 2, 3, 4, 5, 6))
        print(f"{tag}: held-out KL(target || policy) {kl:.4f}, value MSE {vl:.5f}, picks the improved move "
              f"{100 * ag:.1f}% (the recording network {100 * bag:.1f}%); table builds or trades where the improved "
              f"move ends the turn: {100 * ps:.1f}% of decisions, -log p(table's move) {imi:.2f}", flush=True)

    evaluate("start")
    rng = np.random.default_rng(1)
    for ep in range(epochs):
        perm = rng.permutation(tr)
        for i in range(0, len(perm), batch):
            loss = losses(perm[i:i + batch])[0]
            opt.zero_grad()
            loss.backward()
            opt.step()
        evaluate(f"epoch {ep}")
    pol.save_puffer(out)
    meta2 = dict(meta, name=os.path.basename(out), distilled_from=meta.get("name", ckpt),
                 expert_iter={"c": c, "epochs": epochs, "lr": lr, "decisions": int(len(obs)), "data": data,
                              "imitate": imitate})
    meta2.pop("diag", None)
    json.dump(meta2, open(out + ".json", "w"))
    print(f"wrote {out}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["collect", "distill"])
    ap.add_argument("ckpt")
    ap.add_argument("out")
    ap.add_argument("data", nargs="*")
    ap.add_argument("--games", type=int, default=100)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--worlds", default=TRAIN_WORLDS)
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--c", type=float, default=100.0)
    ap.add_argument("--explore", type=float, default=0.1)
    ap.add_argument("--epochs", type=int, default=2)
    ap.add_argument("--lr", type=float, default=3e-4)
    ap.add_argument("--vf-coef", type=float, default=1.0)
    ap.add_argument("--batch", type=int, default=256)
    ap.add_argument("--max-rows", type=int, default=0)
    ap.add_argument("--imitate", type=float, default=0.0,
                    help="item 2: weight of the table bot's move where the improved move ends the turn and table "
                         "builds or trades")
    a = ap.parse_args()
    if a.mode == "collect":
        collect(a.ckpt, a.out, a.games, a.seed, a.worlds, a.k, a.c, a.explore)
    else:
        distill(a.ckpt, a.out, a.data, a.epochs, a.lr, a.c, a.vf_coef, a.batch, a.max_rows, a.imitate)


if __name__ == "__main__":
    main()
