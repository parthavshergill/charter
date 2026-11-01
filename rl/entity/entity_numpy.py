"""The entity encoder in NumPy, for rl/eval. Same sums as entity_torch.py and charter_entity.cu.

Formats, chosen by the meta's `format`:
- `puffer-entity`: a PufferLib `.bin` checkpoint built with charter_entity.cu. Raw float32, blocks padded to
  8 floats, in the order the encoder registers them: one `in_<table>` block (E x table width) per base table,
  `out` (hidden x tables*E), then the decoder (act + 1 x hidden) and one MinGRU block (3 hidden x hidden) per layer.
- `npz-entity`: the same arrays in an `.npz`: `in_<table>`, `out`, `decoder`, `gru0`, ...

The meta must give `entity_dim` (E). The table layout comes from rl/layout.json. With `"pointer": 1` in the meta,
the decoder block is followed by the pointer block `ptr` (2E x hidden, or 4E with `"pointer": 2`, which also
scores bank trades), and the pointer scores are added
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


def pointer_scores(rows, h, ptr, act_size, act_spot, act_link, E=None, act_bank=None):
    """The pointer decoder's added scores (act_size,): see entity_torch.pointer_logits."""
    E = E or ptr.shape[0] // 2
    q = ptr @ h
    rk, rs, rl = rows["kinds"], rows["spots"], rows["links"]
    out = np.zeros(act_size, np.float32)
    spot = np.einsum("e,ve,ke->kv", q[:E], rs, rk[1:])
    out[act_spot:act_spot + spot.size] = spot.reshape(-1)
    out[act_link:act_link + rl.shape[0]] = rl @ (q[E:2 * E] * rk[0])
    if ptr.shape[0] == 4 * E:
        rr = rows["resources"]
        bank = (rr @ q[2 * E:3 * E])[:, None] + (rr @ q[3 * E:])[None, :]
        out[act_bank:act_bank + bank.size] = bank.reshape(-1)
    return out


class EntityNet(FlatNet):
    def __init__(self, tables, w_in, w_out, decoder, grus, act_size, ptr=None, acts=None):
        super().__init__(None, decoder, grus, act_size)
        self.tables, self.w_in, self.w_out, self.ptr, self.acts = tables, w_in, w_out, ptr, acts
        self.E = w_in[0].shape[0]

    def forward(self, obs, state):
        rows = {} if self.ptr is not None else None
        x = entity_encode(np.asarray(obs, np.float32), self.tables, self.w_in, self.w_out, rows)
        out = []
        for W, s in zip(self.grus, state):
            x, s2 = mingru_step(W, x, s)
            out.append(s2)
        y = self.decoder @ x
        logits = y[:-1]
        if self.ptr is not None:
            logits = logits + pointer_scores(rows, x, self.ptr, len(logits), self.acts["spot"], self.acts["link"],
                                             self.E, self.acts["bank"])
        return logits, y[-1], out


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
    ptr = block((4 if pointer == 2 else 2) * E, hidden) if pointer else None
    grus = [block(3 * hidden, hidden) for _ in range(layers)]
    if pos != len(w) and (len(w) + 7) & ~7 != pos:
        raise ValueError(f"{path}: {len(w)} floats, expected {pos} for this shape")
    return w_in, w_out, dec, ptr, grus


def load_entity(path, meta, layout_path=LAYOUT):
    layout = json.load(open(layout_path))
    tables = base_tables(layout)
    assert meta["obs_size"] == layout["base_size"], "the entity encoder reads the base tables only"
    E = meta["entity_dim"]
    pointer = int(meta.get("pointer", 0))   # 1: spots and links, 2: also bank trades
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
                     f(ptr) if pointer else None, layout["actions"])
