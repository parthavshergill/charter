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
With `"resid": 1`, four blocks follow `out`: the LayerNorm gain and bias (hidden each), W_r1 and W_r2 (hidden x
hidden), and the encoder ends with out = o0 + W_r2 relu(W_r1 LayerNorm(o0)) (charter_entity.cu, CE_RESID).
"""
import json
import os

import numpy as np

from reference.policy import FlatNet, mingru_step

LAYOUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "layout.json")


def base_tables(layout, moves=False):
    """(name, offset, rows, width) for each table, the moves table only if `moves`. Same as gen_layout.tables."""
    return [(t["name"], t["offset"], t["rows"], t["width"]) for t in layout["tables"] if moves or t["name"] != "moves"]


def layer_norm(x, g, b, eps=1e-5):
    m = x.mean()
    return (x - m) / np.sqrt(((x - m) ** 2).mean() + eps) * g + b


def entity_encode(obs, tables, w_in, w_out, keep=None, resid=None):
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
    o0 = w_out @ np.concatenate(pooled)
    if resid is None:
        return o0
    g, b, w1, w2 = resid
    return o0 + w2 @ np.maximum(w1 @ layer_norm(o0, g, b), 0.0)


def pointer_scores(rows, h, ptr, act_size, act_place, act_bank, E=None, moves=None):
    """The pointer decoder's added scores (act_size,), layout 2: see entity_torch.pointer_logits. With `moves`
    (action numbers and real flags of the moves rows), also entity_torch.moves_logits."""
    E = E or ptr.shape[0] // 3
    q = ptr @ h
    out = np.zeros(act_size, np.float32)
    rp, rr = rows["places"], rows["resources"]
    out[act_place:act_place + rp.shape[0]] = rp @ q[:E]
    bank = (rr @ q[E:2 * E])[:, None] + (rr @ q[2 * E:3 * E])[None, :]
    out[act_bank:act_bank + bank.size] = bank.reshape(-1)
    if moves is not None:
        acts, real = moves
        score = rows["moves"] @ q[3 * E:4 * E]
        for m in np.flatnonzero(real):
            if 0 <= acts[m] < act_size:
                out[acts[m]] += score[m]
    return out


class EntityNet(FlatNet):
    def __init__(self, tables, w_in, w_out, decoder, grus, act_size, ptr=None, acts=None, resid=None):
        super().__init__(None, decoder, grus, act_size)
        self.resid = resid
        self.tables, self.w_in, self.w_out, self.ptr, self.acts = tables, w_in, w_out, ptr, acts
        self.E = w_in[0].shape[0]
        # Eval variants after `#` in a subject (rl/eval): `mixKcC` (for example `mix4c30`) picks, among the policy's K
        # best legal actions, the one with the most logit + C * (V(after) - V(now)), each tried on a copy of the game;
        # `time` keeps the time per decision under CHARTER_DIAG_DIR.
        self.diag_name = ""
        self.mix, self.timing, self._v = None, False, 0.0
        self.t_sum, self.t_n, self.t_steps = 0.0, 0, 0
        names = [t[0] for t in tables]
        self.moves_t = names.index("moves") if "moves" in names else None
        self.act_col = 1   # rl/layout.json: the moves table's `action` column

    def forward(self, obs, state):
        rows = {} if self.ptr is not None else None
        obs = np.array(obs, np.float32)
        moves = None
        if self.moves_t is not None:
            # The moves table's action column routes each row's score, and the encoder sees 0 there.
            _, off, nrows, width = self.tables[self.moves_t]
            cols = off + np.arange(nrows) * width + self.act_col
            moves = (np.rint(obs[cols]).astype(np.int64), obs[off + np.arange(nrows) * width] > 0.5)
            obs[cols] = 0
        x = entity_encode(obs, self.tables, self.w_in, self.w_out, rows, self.resid)
        out = []
        for W, s in zip(self.grus, state):
            x, s2 = mingru_step(W, x, s)
            out.append(s2)
        y = self.decoder @ x
        self._v = float(y[-1])
        self._raw = None
        logits = y[:-1]
        if self.ptr is not None:
            logits = logits + pointer_scores(rows, x, self.ptr, len(logits), self.acts["place"], self.acts["bank"],
                                             self.E, moves)
        self._raw = logits
        return logits, y[-1], out


    def set_diag(self, diag):
        self.diag_name = diag
        parts = set(diag.split("+")) if diag else set()
        mix = next((d for d in parts if d.startswith("mix")), None)
        self.mix = (int(mix[3:].split("c")[0]), float(mix.split("c")[1])) if mix else None
        self.timing = "time" in parts
        # `two` (with mix): also try "bank trade, then a build it makes legal" (rl/ROUND4.md item 3, two-step value)
        self.two = "two" in parts

    def tick(self, dt):
        self.t_sum += dt
        self.t_n += 1
        if self.t_n % 50 == 0:
            d = os.environ.get("CHARTER_DIAG_DIR", "/tmp/charter-diag")
            os.makedirs(d, exist_ok=True)
            with open(os.path.join(d, f"time-{self.diag_name}-{os.getpid()}.json"), "w") as f:
                json.dump({"variant": self.diag_name, "decisions": self.t_n, "seconds": self.t_sum,
                           "engine_steps": self.t_steps}, f)

    def choose_mix(self, player, game, obs, mask, logits):
        k, c = self.mix
        legal = np.flatnonzero(np.isfinite(logits))
        if len(legal) <= 1 or game.voting:
            return None
        cand = legal[np.argsort(-logits[legal])][:k]
        seat, v_now, state = game.seat, self._v, player.state
        raw = None if self._raw is None else np.array(self._raw[:len(logits)], np.float64)
        best, best_s = None, -np.inf
        for a in cand:
            v = v_now
            if a != 0:
                g2 = game.copy()
                g2.step(int(a))
                self.t_steps += 1
                if g2.over:
                    v = float(g2.rewards()[seat])
                elif g2.seat == seat:
                    _, v2, _ = self.forward(g2.obs(), state)
                    v = float(v2)
            sc = float(logits[a]) + c * (v - v_now)
            if sc > best_s:
                best, best_s = int(a), sc
        if self.two:
            a2, s2 = self.two_step(game, seat, state, v_now, raw, c)
            if a2 is not None and s2 > best_s:
                best, best_s = a2, s2
        return best

    def two_step(self, game, seat, state, v_now, raw, c, max_trades=8, max_builds=2):
        """Item 3: a bank trade earns nothing by itself, so one step of lookahead cannot price it. For each legal bank
        trade that makes a build legal that is not legal now, try the trade, then that build (the policy's best one
        or two of them), and score the pair by the build's own logit now plus c * (V after both - V now). Returns the
        trade with the best such score, or None."""
        bank0, decl0, place0 = self.acts["bank"], self.acts["declare"], self.acts["place"]
        mask = game.mask()
        trades = [a for a in np.flatnonzero(mask) if bank0 <= a < decl0]
        best, best_s, tried = None, -np.inf, 0
        for a in trades:
            if tried >= max_trades:
                break
            g2 = game.copy()
            g2.step(int(a))
            self.t_steps += 1
            if g2.over or g2.seat != seat:
                continue
            m2 = g2.mask()
            new = [b for b in np.flatnonzero(m2[:len(mask)]) if b >= place0 and not mask[b]]
            if not new:
                continue
            tried += 1
            new.sort(key=lambda b: -raw[b])
            for b in new[:max_builds]:
                g3 = g2.copy()
                g3.step(int(b))
                self.t_steps += 1
                if g3.over:
                    v = float(g3.rewards()[seat])
                elif g3.seat == seat:
                    _, v3, _ = self.forward(g3.obs(), state)
                    v = float(v3)
                else:
                    continue
                sc = float(raw[b]) + c * (v - v_now)
                if sc > best_s:
                    best, best_s = int(a), sc
        return best, best_s


def read_entity_bin(path, tables, E, hidden, layers, act_size, pointer=0, resid=False):
    """w_in, w_out, decoder, ptr, grus; with `resid`, also the residual block (g, b, W_r1, W_r2) as a sixth."""
    w = np.fromfile(path, dtype="<f4")
    pos = 0

    def block(rows, cols):
        nonlocal pos
        a = w[pos:pos + rows * cols].reshape(rows, cols)
        pos = (pos + rows * cols + 7) & ~7
        return a

    w_in = [block(E, width) for _, _, _, width in tables]
    w_out = block(hidden, len(tables) * E)
    res = (block(1, hidden)[0], block(1, hidden)[0], block(hidden, hidden), block(hidden, hidden)) if resid else None
    dec = block(act_size + 1, hidden)
    ptr = block((4 if any(t[0] == "moves" for t in tables) else 3) * E, hidden) if pointer else None
    grus = [block(3 * hidden, hidden) for _ in range(layers)]
    if pos != len(w) and (len(w) + 7) & ~7 != pos:
        raise ValueError(f"{path}: {len(w)} floats, expected {pos} for this shape")
    if resid:
        return w_in, w_out, dec, ptr, grus, res
    return w_in, w_out, dec, ptr, grus


def load_entity(path, meta, layout_path=LAYOUT):
    layout = json.load(open(layout_path))
    moves = bool(meta.get("moves", 0))   # per-move rows (move_rows=1, built with CE_MOVES)
    tables = base_tables(layout, moves)
    assert meta["obs_size"] == (layout["full_size"] if moves else layout["base_size"]), "obs_size and moves disagree"
    E = meta["entity_dim"]
    pointer = int(meta.get("pointer", 0))
    assert layout["version"] == 2 and meta.get("layout", 2) == 2, "this pointer decoder is for layout 2"
    resid = bool(meta.get("resid", 0))
    res = None
    if meta["format"] == "puffer-entity":
        got = read_entity_bin(path, tables, E, meta["hidden"], meta["layers"], meta["act_size"], pointer, resid)
        w_in, w_out, dec, ptr, grus = got[:5]
        res = got[5] if resid else None
    else:
        z = np.load(path)
        w_in = [z[f"in_{name}"] for name, _, _, _ in tables]
        w_out, dec = z["out"], z["decoder"]
        ptr = z["ptr"] if pointer else None
        grus = [z[f"gru{i}"] for i in range(meta["layers"])]
        assert not resid, "the npz format has no residual block"
    f = lambda a: np.ascontiguousarray(a, np.float32)
    net = EntityNet(tables, [f(a) for a in w_in], f(w_out), f(dec), [f(g) for g in grus], meta["act_size"],
                    f(ptr) if pointer else None, layout["actions"], tuple(f(a) for a in res) if res else None)
    net.set_diag(meta.get("diag", ""))
    return net
