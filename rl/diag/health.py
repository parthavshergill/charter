"""Value-head quality (does V predict the win?) and dead encoder units, on recorded server games."""
import json, sys, os, re
import numpy as np
sys.path.insert(0, "/home/user/charter/rl"); sys.path.insert(0, "/home/user/charter/rl/env")
sys.path.insert(0, os.path.dirname(__file__))
from entity.entity_numpy import load_entity, entity_encode
from pit import parse, S

def auc(scores, labels):
    s, l = np.asarray(scores), np.asarray(labels, bool)
    if l.all() or (~l).all(): return float("nan")
    order = np.argsort(s); r = np.empty(len(s)); r[order] = np.arange(1, len(s) + 1)
    return (r[l].sum() - l.sum() * (l.sum() + 1) / 2) / (l.sum() * (~l).sum())

def winners(world):
    p = f"{S}/srv/out-{world}.txt" if world != "the-pit" else None
    lines = open(p).read().splitlines() if p else None
    res = []
    for ln in lines:
        m = re.match(rf"{world}, \d seats, policy \[(\d)\]: .*?seat (\d) \((policy|current bot)\) won", ln)
        if m: res.append(int(m.group(3) == "policy"))
        elif ln.startswith(f"{world}, ") and "won" not in ln: res.append(0)
    return res

def path_of(world):
    return f"{S}/srv/rec-{world}.txt" if world != "the-pit" else f"{S}/srv/pit.txt"

def main(ckpts, worlds):
    print("| checkpoint | world | AUC of V for the win (all / first half / second half of game) | win rate | dead encoder units (of 32 per table, summed over 8 tables) |")
    print("|---|---|---|---|---|")
    for ck in ckpts:
        meta = json.load(open(f"{S}/ck/{ck}.bin.json")); net = load_entity(f"{S}/ck/{ck}.bin", meta)
        for w in worlds:
            recs = parse(path_of(w))
            won = winners(w) if w != "the-pit" else [0] * 40
            st = None; vs = []; act = None
            for kind, r in recs:
                if kind == "reset": st = net.initial_state(); continue
                rows = {}
                _, v, st = net.forward(r["obs"], st)
                vs.append((r["game"], r["round"], float(v)))
                keep = {}
                entity_encode(r["obs"], net.tables, net.w_in, net.w_out, keep)
                a = np.concatenate([(keep[n][r["obs"][o:o + rr * wd].reshape(rr, wd)[:, 0] > 0.5] > 0).any(0)
                                    if (r["obs"][o:o + rr * wd].reshape(rr, wd)[:, 0] > 0.5).any() else np.zeros(net.E, bool)
                                    for n, o, rr, wd in net.tables])
                act = a if act is None else (act | a)
            g = np.array([x[0] for x in vs]); rd = np.array([x[1] for x in vs]); v = np.array([x[2] for x in vs])
            y = np.array([won[i] if i < len(won) else 0 for i in g])
            half = np.median(rd)
            a_all = auc(v, y); a1 = auc(v[rd <= half], y[rd <= half]); a2 = auc(v[rd > half], y[rd > half])
            print(f"| {ck} | {w} | {a_all:.2f} / {a1:.2f} / {a2:.2f} | {np.mean(won):.2f} ({len(won)} games) | {int((~act).sum())} of {act.size} |")

if __name__ == "__main__":
    main(sys.argv[1].split(","), sys.argv[2].split(","))
