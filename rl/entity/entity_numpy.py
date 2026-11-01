"""The entity encoder in NumPy, for rl/eval. Same sums as entity_torch.py and charter_entity.cu.

Formats, chosen by the meta's `format`:
- `puffer-entity`: a PufferLib `.bin` checkpoint built with charter_entity.cu. Raw float32, blocks padded to
  8 floats, in the order the encoder registers them: one `in_<table>` block (E x table width) per base table,
  `out` (hidden x tables*E), then the decoder (act + 1 x hidden) and one MinGRU block (3 hidden x hidden) per layer.
- `npz-entity`: the same arrays in an `.npz`: `in_<table>`, `out`, `decoder`, `gru0`, ...

The meta must give `entity_dim` (E). The table layout comes from rl/layout.json.
"""
import json
import os

import numpy as np

from reference.policy import FlatNet, mingru_step

LAYOUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "layout.json")


def base_tables(layout):
    """(name, offset, rows, width) for each base table. Same as gen_layout.tables."""
    return [(t["name"], t["offset"], t["rows"], t["width"]) for t in layout["tables"] if t["name"] != "moves"]


def entity_encode(obs, tables, w_in, w_out):
    """One observation (obs_size,) to (hidden,): per table, relu(W_t x) on each row, the mean over real rows
    (column 0 above 0.5, zeros if none), then W_out on all the means joined."""
    pooled = []
    for (_, off, rows, width), w in zip(tables, w_in):
        x = obs[off:off + rows * width].reshape(rows, width)
        real = x[:, 0] > 0.5
        h = np.maximum(x[real] @ w.T, 0.0)
        pooled.append(h.sum(0) / max(int(real.sum()), 1))
    return w_out @ np.concatenate(pooled)


class EntityNet(FlatNet):
    def __init__(self, tables, w_in, w_out, decoder, grus, act_size):
        super().__init__(None, decoder, grus, act_size)
        self.tables, self.w_in, self.w_out = tables, w_in, w_out

    def forward(self, obs, state):
        x = entity_encode(np.asarray(obs, np.float32), self.tables, self.w_in, self.w_out)
        out = []
        for W, s in zip(self.grus, state):
            x, s2 = mingru_step(W, x, s)
            out.append(s2)
        y = self.decoder @ x
        return y[:-1], y[-1], out


def read_entity_bin(path, tables, E, hidden, layers, act_size):
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
    grus = [block(3 * hidden, hidden) for _ in range(layers)]
    if pos != len(w) and (len(w) + 7) & ~7 != pos:
        raise ValueError(f"{path}: {len(w)} floats, expected {pos} for this shape")
    return w_in, w_out, dec, grus


def load_entity(path, meta, layout_path=LAYOUT):
    layout = json.load(open(layout_path))
    tables = base_tables(layout)
    assert meta["obs_size"] == layout["base_size"], "the entity encoder reads the base tables only"
    E = meta["entity_dim"]
    if meta["format"] == "puffer-entity":
        w_in, w_out, dec, grus = read_entity_bin(path, tables, E, meta["hidden"], meta["layers"], meta["act_size"])
    else:
        z = np.load(path)
        w_in = [z[f"in_{name}"] for name, _, _, _ in tables]
        w_out, dec = z["out"], z["decoder"]
        grus = [z[f"gru{i}"] for i in range(meta["layers"])]
    f = lambda a: np.ascontiguousarray(a, np.float32)
    return EntityNet(tables, [f(a) for a in w_in], f(w_out), f(dec), [f(g) for g in grus], meta["act_size"])
