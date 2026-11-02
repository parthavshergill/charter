"""The entity encoder in NumPy, for rl/eval. Same sums as entity_torch.py and charter_entity.cu.

Formats, chosen by the meta's `format`:
- `puffer-entity`: a PufferLib `.bin` checkpoint built with charter_entity.cu. Raw float32, blocks padded to
  8 floats, in the order the encoder registers them: one `in_<table>` block (E x table width) per base table,
  `out` (hidden x tables*E), then the decoder (act + 1 x hidden) and one MinGRU block (3 hidden x hidden) per layer.
- `npz-entity`: the same arrays in an `.npz`: `in_<table>`, `out`, `decoder`, `gru0`, ...

The meta must give `entity_dim` (E). The table layout comes from rl/layout.json. With `"pointer": 1` in the meta,
the decoder block is followed by the pointer block `ptr` (3E x hidden, layout 2: places and bank trades), and the
pointer scores are added
(charter_entity.cu, CE_POINTER; entity_torch.py `pointer_logits`).
"""
import json
import os

import numpy as np

from reference.policy import FlatNet, mingru_step

LAYOUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "layout.json")


def base_tables(layout):
    """(name, offset, rows, width) for each base table. Same as gen_layout.tables."""
    return [(t["name"], t["offset"], t["rows"], t["width"]) for t in layout["tables"] if t["name"] != "moves"]


def entity_encode(obs, tables, w_in, w_out, keep=None):
    """One observation (obs_size,) to (hidden,): per table, relu(W_t x) on each row, the mean over real rows
    (column 0 above 0.5, zeros if none), then W_out on all the means joined. `keep`, a dict, gets every
    table's rows relu(W_t x), by table name, for the pointer decoder."""
    pooled = []
    for (name, off, rows, width), w in zip(tables, w_in):
        x = obs[off:off + rows * width].reshape(rows, width)
        real = x[:, 0] > 0.5
        r = np.maximum(x @ w.T, 0.0)
        if keep is not None:
            keep[name] = r
        pooled.append(r[real].sum(0) / max(int(real.sum()), 1))
    return w_out @ np.concatenate(pooled)


def pointer_scores(rows, h, ptr, act_size, act_place, act_bank):
    """The pointer decoder's added scores (act_size,), layout 2: see entity_torch.pointer_logits."""
    E = ptr.shape[0] // 3
    q = ptr @ h
    out = np.zeros(act_size, np.float32)
    rp, rr = rows["places"], rows["resources"]
    out[act_place:act_place + rp.shape[0]] = rp @ q[:E]
    bank = (rr @ q[E:2 * E])[:, None] + (rr @ q[2 * E:])[None, :]
    out[act_bank:act_bank + bank.size] = bank.reshape(-1)
    return out


# Diagnostic variants, named after `#` in an eval subject (rl/eval/eval.py), joined by `+`:
# - `perm`: shuffle the linear decoder's place logits at every decision. The encoder and the pointer do not depend on
#   the order of the `places` rows, so this is exactly a random reordering of `places` at eval.
# - `nolin`: drop the linear decoder's place logits (the pointer alone scores placements).
# - `nolinbank`: also drop its bank-trade logits.
# - `look`: one step of lookahead with the engine: each legal action is tried on a copy of the game, and scored by
#   the value of the position after it (the reward if the game ends); end turn is scored by the value now.
#   `lookK` (for example `look4`) only considers the policy's K best actions.
# - `log`: write one JSON line per decision (linear and pointer parts, legal sets, the `table` and `hand` bots'
#   choices) under CHARTER_DIAG_DIR (default /vol/priorart2/diag).
PLACES_COLS = {"points_gain": 15, "yield_gain": 16, "cost_total": 17, "my_short": 18, "on_upgrade": 3, "on_link": 1}


class EntityNet(FlatNet):
    def __init__(self, tables, w_in, w_out, decoder, grus, act_size, ptr=None, acts=None, diag=""):
        super().__init__(None, decoder, grus, act_size)
        self.tables, self.w_in, self.w_out, self.ptr, self.acts = tables, w_in, w_out, ptr, acts
        self.E = w_in[0].shape[0]
        self.diag = set(diag.split("+")) if diag else set()
        self.diag_log = "log" in self.diag
        self.look = next((d for d in self.diag if d.startswith("look")), None)
        self.rng = np.random.default_rng(12345)
        self.places_at = next(off for name, off, _, _ in tables if name == "places")
        self._lin = self._ptr = None
        self._v = 0.0

    def forward(self, obs, state):
        rows = {} if self.ptr is not None else None
        x = entity_encode(np.asarray(obs, np.float32), self.tables, self.w_in, self.w_out, rows)
        out = []
        for W, s in zip(self.grus, state):
            x, s2 = mingru_step(W, x, s)
            out.append(s2)
        y = self.decoder @ x
        lin = y[:-1].copy()
        P, B = self.acts["place"], self.acts["bank"]
        if "perm" in self.diag:
            lin[P:P + 128] = lin[P:P + 128][self.rng.permutation(128)]
        if "nolin" in self.diag or "nolinbank" in self.diag:
            lin[P:P + 128] = 0.0
        if "nolinbank" in self.diag:
            lin[B:B + 256] = 0.0
        logits = lin
        ptr = None
        if self.ptr is not None:
            ptr = pointer_scores(rows, x, self.ptr, len(lin), P, B)
            logits = lin + ptr
        self._lin, self._ptr, self._v = lin, ptr, float(y[-1])
        return logits, y[-1], out

    def category(self, a):
        P, B, D = self.acts["place"], self.acts["bank"], self.acts["declare"]
        if a < 0:
            return "none"
        if a == 0:
            return "end"
        if a < B:
            return "vote"
        if a < D:
            return "bank"
        if a < P:
            return "declare"
        return "place"

    def choose(self, player, game, obs, mask, logits):
        if not self.look:
            return None
        legal = np.flatnonzero(mask[:len(logits)])
        if len(legal) <= 1 or game.voting:
            return None
        k = int(self.look[4:] or 0)
        cand = legal[np.argsort(-logits[legal])][:k] if k else legal
        if len(cand) > 64:
            return None
        seat, v_now = game.seat, self._v
        state = player.state
        best, best_v = None, -np.inf
        for a in cand:
            if a == 0:
                v = v_now
            else:
                g2 = game.copy()
                g2.step(int(a))
                if g2.over:
                    v = float(g2.rewards()[seat])
                elif g2.seat == seat:
                    _, v, _ = self.forward(g2.obs(), state)
                    v = float(v)
                else:
                    v = v_now
            if v > best_v:
                best, best_v = int(a), v
        self.forward(obs, state)  # restore the parts of this decision
        return best

    def record(self, player, game, obs, mask, logits, a):
        import json as _json
        d = os.environ.get("CHARTER_DIAG_DIR", "/vol/priorart2/diag")
        os.makedirs(d, exist_ok=True)
        P, B = self.acts["place"], self.acts["bank"]
        m = np.asarray(mask[:len(logits)], bool)
        lp = np.flatnonzero(m[P:P + 128])
        rec = {"ctx": list(getattr(player, "diag_ctx", ())), "setup": float(obs[2]), "round": float(obs[4]),
               "end_legal": bool(m[0]), "n_place": int(len(lp)), "n_bank": int(m[B:B + 256].sum()),
               "chosen": self.category(a), "v": self._v, "lin_end": float(self._lin[0])}
        if len(lp):
            tot = logits[P + lp]
            i = int(lp[np.argmax(tot)])
            rec["best_place"] = {"total": float(logits[P + i]), "lin": float(self._lin[P + i]),
                                 "ptr": float(self._ptr[P + i]) if self._ptr is not None else 0.0, "row": i}
            rows = np.asarray(obs[self.places_at:self.places_at + 128 * 35], np.float32).reshape(128, 35)
            rec["best_place_row"] = {k: float(rows[i, c]) for k, c in PLACES_COLS.items()}
            rec["legal_points_gain_max"] = float(rows[lp, 15].max())
            rec["legal_short_min"] = float(rows[lp, 18].min())
            rec["lin_place_mean"] = float(self._lin[P + lp].mean())
            rec["ptr_place_mean"] = float(self._ptr[P + lp].mean()) if self._ptr is not None else 0.0
            rec["ptr_place_sd"] = float(self._ptr[P + lp].std()) if self._ptr is not None else 0.0
            rec["lin_place_sd"] = float(self._lin[P + lp].std())
        for bot in ("table", "hand"):
            try:
                s = int(game.suggest(bot))
            except Exception:
                s = -1
            rec[bot] = self.category(s)
            rec[bot + "_same"] = bool(s == a)
            if s >= P and len(lp):
                rec[bot + "_place"] = {"total": float(logits[s]), "lin": float(self._lin[s]),
                                       "ptr": float(self._ptr[s]) if self._ptr is not None else 0.0}
        with open(os.path.join(d, f"{os.getpid()}.jsonl"), "a") as f:
            f.write(_json.dumps(rec) + "\n")


def read_entity_bin(path, tables, E, hidden, layers, act_size, pointer=0):
    w = np.fromfile(path, dtype="<f4")
    pos = 0

    def block(rows, cols):
        nonlocal pos
        a = w[pos:pos + rows * cols].reshape(rows, cols)
        pos = (pos + rows * cols + 7) & ~7
        return a

    w_in = [block(E, width) for _, _, _, width in tables]
    w_out = block(hidden, len(tables) * E)
    dec = block(act_size + 1, hidden)
    ptr = block(3 * E, hidden) if pointer else None
    grus = [block(3 * hidden, hidden) for _ in range(layers)]
    if pos != len(w) and (len(w) + 7) & ~7 != pos:
        raise ValueError(f"{path}: {len(w)} floats, expected {pos} for this shape")
    return w_in, w_out, dec, ptr, grus


def load_entity(path, meta, layout_path=LAYOUT):
    layout = json.load(open(layout_path))
    tables = base_tables(layout)
    assert meta["obs_size"] == layout["base_size"], "the entity encoder reads the base tables only"
    E = meta["entity_dim"]
    pointer = int(meta.get("pointer", 0))
    assert layout["version"] == 2 and meta.get("layout", 2) == 2, "this pointer decoder is for layout 2"
    if meta["format"] == "puffer-entity":
        w_in, w_out, dec, ptr, grus = read_entity_bin(path, tables, E, meta["hidden"], meta["layers"],
                                                      meta["act_size"], pointer)
    else:
        z = np.load(path)
        w_in = [z[f"in_{name}"] for name, _, _, _ in tables]
        w_out, dec = z["out"], z["decoder"]
        ptr = z["ptr"] if pointer else None
        grus = [z[f"gru{i}"] for i in range(meta["layers"])]
    f = lambda a: np.ascontiguousarray(a, np.float32)
    return EntityNet(tables, [f(a) for a in w_in], f(w_out), f(dec), [f(g) for g in grus], meta["act_size"],
                     f(ptr) if pointer else None, layout["actions"], meta.get("diag", ""))
