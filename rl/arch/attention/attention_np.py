"""The `attention` encoder in NumPy, for rl/eval (format `puffer-attention`). Same numbers as attention.cu.

A `puffer-attention` checkpoint is PufferLib's raw float32 `.bin`, blocks padded to 8 floats, in the order:
the encoder's weights (attention_ref.param_shapes), the decoder (act + 1 x hidden), then one MinGRU block
(3 hidden x hidden) per layer.
"""
import json
import math
import os

import numpy as np

try:
    from . import attention_plan as R
except ImportError:  # run from this folder
    import attention_plan as R

LAYOUT_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "layout.json")


class AttentionEncoder:
    def __init__(self, plan: R.Plan, weights: dict):
        self.plan = plan
        self.w = {k: np.asarray(v, np.float32) for k, v in weights.items()}

    def __call__(self, obs: np.ndarray) -> np.ndarray:
        """One observation [obs_size] -> [hidden]."""
        p, w = self.plan, self.w
        ctx = np.concatenate([obs[b.offset:b.offset + b.width] for b in p.context])
        c = np.maximum(w["w_ctx"] @ ctx, 0)
        xs = []
        for b in p.tokens:
            rows = obs[b.offset:b.offset + b.rows * b.width].reshape(b.rows, b.width)
            keep = rows[:, 0] > 0.5
            xs.append(np.maximum(rows[keep] @ w[f"w_{b.name}"].T, 0))
        x = np.concatenate(xs, 0)                                   # real tokens only, [n, D]
        q = (w["wq"] @ c).reshape(R.HEADS, R.HEAD_DIM)
        if len(x) == 0:
            y = np.zeros(R.ATT, np.float32)
        else:
            k = (x @ w["wk"].T).reshape(-1, R.HEADS, R.HEAD_DIM)
            v = (x @ w["wv"].T).reshape(-1, R.HEADS, R.HEAD_DIM)
            s = np.einsum("ha,nha->hn", q, k) / math.sqrt(R.HEAD_DIM)
            s = np.exp(s - s.max(1, keepdims=True))
            a = s / s.sum(1, keepdims=True)
            y = np.einsum("hn,nha->ha", a, v).reshape(R.ATT)
        return w["wout"] @ np.concatenate([y, c])


def read_bin(path, plan, hidden, layers, act_size):
    """Split a checkpoint into (encoder weights, decoder, MinGRU blocks)."""
    flat = np.fromfile(path, dtype="<f4")
    pos = 0

    def block(rows, cols):
        nonlocal pos
        a = flat[pos:pos + rows * cols].reshape(rows, cols)
        pos = (pos + rows * cols + 7) & ~7
        return a

    enc = {name: block(r, c) for name, (r, c) in R.param_shapes(plan, hidden)}
    dec = block(act_size + 1, hidden)
    grus = [block(3 * hidden, hidden) for _ in range(layers)]
    if pos != len(flat) and (len(flat) + 7) & ~7 != pos:
        raise ValueError(f"{path}: {len(flat)} floats, expected {pos} for this shape")
    return enc, dec, grus


def load(path, meta, layout_path=LAYOUT_PATH):
    """The pieces rl/reference/policy.py needs: an encoder callable, the decoder, the MinGRU blocks."""
    layout = json.load(open(layout_path))
    plan = R.plan_from_layout(layout, meta["obs_size"])
    enc, dec, grus = read_bin(path, plan, meta["hidden"], meta["layers"], meta["act_size"])
    return AttentionEncoder(plan, enc), dec, grus
