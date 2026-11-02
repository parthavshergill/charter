"""Replay recorded server decisions through C5 in NumPy and split the logits into linear and pointer parts."""
import json, sys, os
import numpy as np
sys.path.insert(0, "/home/user/charter/rl"); sys.path.insert(0, "/home/user/charter/rl/env")
from entity.entity_numpy import load_entity
from reference.policy import mingru_step

S = "/tmp/claude-0/-home-user-charter/937608b9-c1c8-56e7-b6d3-2a221283b7ff/scratchpad"
meta = json.load(open(f"{S}/ck/c5.bin.json"))
net = load_entity(f"{S}/ck/c5.bin", meta)
L = json.load(open("/home/user/charter/rl/layout.json"))
A = L["actions"]; P, B, D = A["place"], A["bank"], A["declare"]
off = {t["name"]: t["offset"] for t in L["tables"]}

def cat(a):
    if a == 0: return "end"
    if a < B: return "vote"
    if a < D: return "bank"
    if a < P: return "declare"
    if a < 9999: return "place"
    return "none"

def parse(path):
    recs, cur = [], None
    game = -1
    for line in open(path):
        line = line.strip()
        if line == "reset": game += 1; recs.append(("reset", game)); continue
        if line == "turn": continue
        if line.startswith("legal"):
            cur["legal"] = [int(x) for x in line.split()[1:]]; continue
        if line.startswith("chosen"): cur["chosen"] = int(line.split()[1]); continue
        if line.startswith("table"): cur["table"] = int(line.split()[1]); continue
        if line.startswith("round"): cur["round"] = int(line.split()[1]); recs.append(("dec", cur)); continue
        cur = {"obs": np.array(line.split(), np.float32), "game": game}
    return recs

def run(path):
    st = None; out = []
    for kind, r in parse(path):
        if kind == "reset": st = net.initial_state(); continue
        logits, v, st = net.forward(r["obs"], st)
        lin, ptr = net._lin, net._ptr
        legal = np.array(r["legal"]); 
        sc = logits[legal]
        top = int(legal[np.argmax(sc)])
        setup = r["obs"][2] > 0.5
        rows = r["obs"][off["places"]:off["places"] + 128 * 35].reshape(128, 35)
        lp = legal[(legal >= P) & (legal < P + 128)] - P
        d = {"game": r["game"], "round": r["round"], "setup": bool(setup), "chosen": cat(r["chosen"]), "table": cat(r["table"]),
             "agree_top": top == r["chosen"], "end_legal": 0 in r["legal"], "n_place": len(lp),
             "n_bank": int(((legal >= B) & (legal < D)).sum()), "v": float(v), "end": float(lin[0])}
        if len(lp):
            i = int(lp[np.argmax(logits[P + lp])])
            d.update(place_total=float(logits[P + i]), place_lin=float(lin[P + i]), place_ptr=float(ptr[P + i]),
                     place_lin_mean=float(lin[P + lp].mean()), place_ptr_mean=float(ptr[P + lp].mean()),
                     place_ptr_sd=float(ptr[P + lp].std()), place_lin_sd=float(lin[P + lp].std()),
                     short_min=float(rows[lp, 18].min()), pts_max=float(rows[lp, 15].max()), yld_max=float(rows[lp, 16].max()))
        bl = legal[(legal >= B) & (legal < D)]
        if len(bl):
            d.update(bank_total=float(logits[bl].max()), bank_lin=float(lin[bl[np.argmax(logits[bl])]]))
        if r["table"] < 9999:
            t = r["table"]; d.update(table_total=float(logits[t]), table_lin=float(lin[t]), table_ptr=float(ptr[t]),
                                     table_rank=int((sc > logits[t]).sum()))
        out.append(d)
    return out

def summary(name, out):
    t = [d for d in out if not d["setup"]]
    s = [d for d in out if d["setup"]]
    agree = np.mean([d["agree_top"] for d in out])
    endc = np.mean([d["chosen"] == "end" for d in t])
    tb_end = np.mean([d["table"] == "end" for d in t])
    wp = [d for d in t if d["n_place"] > 0]
    wb = [d for d in t if d["n_bank"] > 0]
    res = {"world": name, "decisions": len(out), "setup": len(s), "turn": len(t), "numpy==server top": round(agree, 3),
           "turn: policy ends": round(endc, 2), "turn: table ends": round(tb_end, 2),
           "turn: a build legal": round(len(wp) / max(len(t), 1), 2), "turn: a bank trade legal": round(len(wb) / max(len(t), 1), 2),
           "same move as table (turn)": round(np.mean([d["chosen"] == d["table"] for d in t]), 2)}
    if wp:
        e = [d for d in wp if d["chosen"] == "end"]
        res["build legal & policy ends"] = len(e)
        res["table builds there"] = int(sum(d["table"] == "place" for d in e))
        if e:
            res["end logit (lin)"] = round(np.mean([d["end"] for d in e]), 1)
            res["best build: total"] = round(np.mean([d["place_total"] for d in e]), 1)
            res["best build: lin"] = round(np.mean([d["place_lin"] for d in e]), 1)
            res["best build: ptr"] = round(np.mean([d["place_ptr"] for d in e]), 1)
            res["gap end - best build"] = round(np.mean([d["end"] - d["place_total"] for d in e]), 1)
            res["ptr sd across legal builds"] = round(np.mean([d["place_ptr_sd"] for d in e]), 2)
            res["lin sd across legal builds"] = round(np.mean([d["place_lin_sd"] for d in e]), 2)
            res["shortfall min (legal builds)"] = round(np.mean([d["short_min"] for d in e]), 2)
            res["points_gain max"] = round(np.mean([d["pts_max"] for d in e]), 2)
            res["table's move rank (0=top)"] = round(np.mean([d["table_rank"] for d in e if "table_rank" in d]), 1)
    if wb:
        e = [d for d in wb if d["chosen"] == "end"]
        res["bank legal & policy ends"] = len(e)
        res["table trades there"] = int(sum(d["table"] == "bank" for d in e))
        if e:
            res["gap end - best bank"] = round(np.mean([d["end"] - d["bank_total"] for d in e]), 1)
    res["value mean (turn)"] = round(np.mean([d["v"] for d in t]), 3)
    return res

if __name__ == "__main__":
    rows = []
    for name in sys.argv[1:]:
        p = f"{S}/srv/rec-{name}.txt" if name != "the-pit" else f"{S}/srv/pit.txt"
        if not os.path.exists(p): continue
        rows.append(summary(name, run(p)))
    keys = []
    for r in rows:
        for k in r:
            if k not in keys: keys.append(k)
    print("| | " + " | ".join(r["world"] for r in rows) + " |")
    print("|---" * (len(rows) + 1) + "|")
    for k in keys[1:]:
        print(f"| {k} | " + " | ".join(str(r.get(k, "")) for r in rows) + " |")
