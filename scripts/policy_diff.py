#!/usr/bin/env python3
"""Differential test helper for the Lean policy network (Server/Policy/Net.lean).

Commands:
  make-synthetic OUT.chpw         random weights in the real shapes (stand-in
                                  until a real checkpoint is converted)
  make-obs OBS.txt N              N random but plausible observations, with a
                                  `reset` line in the middle
  expect WEIGHTS OBS.txt OUT.txt  run the NumPy reference forward pass and
                                  write one line of logits per observation

OBS.txt: one observation per line, space-separated floats. A blank line or a
line `reset` sets the recurrent state back to zeros (new seat or game).

This file reads the weights header itself, so it does not depend on the Lean
code. The weights format is described in Server/Policy/Net.lean.
"""
import struct
import sys

import numpy as np

# Layout version 1: (name, offset, rows, width).
V1_TABLES = [
    ("global", 0, 1, 17), ("seats", 17, 6, 10), ("resources", 77, 8, 27),
    ("kinds", 293, 9, 28), ("tiles", 545, 24, 18), ("spots", 977, 60, 28),
    ("links", 2657, 84, 15), ("laws", 3917, 16, 27), ("proposal", 4349, 1, 85),
]
V1 = dict(layout_version=1, act_size=695, act_spot=215, act_link=131, act_bank=3,
          tables=V1_TABLES, pointer_tables=("kinds", "spots", "links", "resources"))

# Layout version 2 (harness 89a3a51, rl/layout.json): no tiles or links table; a placement is a row of `places`.
V2_TABLES = [
    ("global", 0, 1, 21), ("seats", 21, 6, 10), ("resources", 81, 16, 27), ("kinds", 513, 16, 36),
    ("spots", 1089, 100, 45), ("laws", 5589, 48, 27), ("proposal", 6885, 1, 100), ("places", 6985, 128, 35),
]
# act_spot holds the first place action; the pointer's spots slot holds `places`.
V2 = dict(layout_version=2, act_size=515, act_spot=387, act_link=387, act_bank=3,
          tables=V2_TABLES, pointer_tables=("kinds", "places", "places", "resources"))
LAYOUTS = {1: V1, 2: V2}


def pad8(n):
    return (n + 7) // 8 * 8


STATE_RULES = {"carry": 0, "turn": 1, "zero": 2}


def header_bytes(layout, E, hidden, layers, pointer, state_rule, act_size=None):
    """The weights-file header (magic + UInt32s) for this layout and model."""
    tables = layout["tables"]
    names = [t[0] for t in tables]
    vals = [2, layout["layout_version"], E, hidden, layers, act_size or layout["act_size"], pointer,
            layout["act_spot"], layout["act_link"], layout["act_bank"], len(tables)]
    for _, off, rows, width in tables:
        vals += [off, rows, width]
    vals += [names.index(n) for n in layout["pointer_tables"]]
    vals += [STATE_RULES[state_rule]]
    return b"CHPW" + struct.pack("<%dI" % len(vals), *vals)


def block_shapes(widths, E, hidden, layers, act_size, pointer):
    """Shapes of the weight blocks, in file order."""
    shapes = [(E, w) for w in widths]
    shapes += [(hidden, len(widths) * E), (act_size + 1, hidden)]
    if pointer:
        shapes.append(({1: 2, 2: 4, 3: 3}[pointer] * E, hidden))
    shapes += [(3 * hidden, hidden)] * layers
    return shapes


def read_weights(path):
    b = open(path, "rb").read()
    assert b[:4] == b"CHPW", "missing magic"
    h = lambda k: struct.unpack_from("<I", b, 4 + 4 * k)[0]
    assert h(0) == 2, "format version"
    E, hidden, layers, act, pointer = h(2), h(3), h(4), h(5), h(6)
    nt = h(10)
    tables = [(h(11 + 3 * t), h(12 + 3 * t), h(13 + 3 * t)) for t in range(nt)]
    idx = [h(11 + 3 * nt + k) for k in range(4)]
    rule = h(11 + 3 * nt + 4)
    pos = 4 + 4 * (11 + 3 * nt + 5)
    blocks = []
    for r, c in block_shapes([t[2] for t in tables], E, hidden, layers, act, pointer):
        a = np.frombuffer(b, dtype="<f4", count=r * c, offset=pos).astype(np.float64)
        blocks.append(a.reshape(r, c))
        pos += 4 * pad8(r * c)
    assert pos == len(b), "size mismatch: expected %d bytes, got %d" % (pos, len(b))
    net = dict(E=E, hidden=hidden, layers=layers, act=act, pointer=pointer,
               act_spot=h(7), act_link=h(8), act_bank=h(9), tables=tables, idx=idx, rule=rule)
    net["w_in"] = blocks[:nt]
    net["w_out"], net["decoder"] = blocks[nt], blocks[nt + 1]
    k = nt + 2
    if pointer:
        net["ptr"] = blocks[k]
        k += 1
    net["grus"] = blocks[k:]
    return net


# ---- reference forward pass (same math as the training branch) ----

def sigmoid(x):
    return 1 / (1 + np.exp(-x))


def mingru_step(W, x, state):
    h = W.shape[1]
    c = W @ x
    hidden, gate, proj = c[:h], c[h:2 * h], c[2 * h:]
    tilde = np.where(hidden >= 0, hidden + 0.5, sigmoid(hidden))
    new = state + sigmoid(gate) * (tilde - state)
    s = sigmoid(proj)
    return s * new + (1 - s) * x, new


def forward(net, obs, state):
    E = net["E"]
    keep, pooled = [], []
    for (off, rows, width), w in zip(net["tables"], net["w_in"]):
        x = obs[off:off + rows * width].reshape(rows, width)
        real = x[:, 0] > 0.5
        r = np.maximum(x @ w.T, 0.0)
        keep.append(r)
        pooled.append(r[real].sum(0) / max(int(real.sum()), 1))
    x = net["w_out"] @ np.concatenate(pooled)
    new_state = []
    for W, s in zip(net["grus"], state):
        x, s2 = mingru_step(W, x, s)
        new_state.append(s2)
    logits = (net["decoder"] @ x)[:-1]
    if net["pointer"] == 3:   # layout 2: rows of places, and bank trades (entity_numpy.pointer_scores)
        _, pi, _, ri = net["idx"]
        rp, rr = keep[pi], keep[ri]
        q = net["ptr"] @ x
        out = np.zeros(net["act"])
        a = net["act_spot"]
        out[a:a + rp.shape[0]] = rp @ q[:E]
        bank = (rr @ q[E:2 * E])[:, None] + (rr @ q[2 * E:])[None, :]
        a = net["act_bank"]
        out[a:a + bank.size] = bank.reshape(-1)
        logits = logits + out
    elif net["pointer"]:
        ki, si, li, ri = net["idx"]
        rk, rs, rl = keep[ki], keep[si], keep[li]
        q = net["ptr"] @ x
        out = np.zeros(net["act"])
        spot = np.einsum("e,ve,ke->kv", q[:E], rs, rk[1:])
        a = net["act_spot"]
        out[a:a + spot.size] = spot.reshape(-1)
        a = net["act_link"]
        out[a:a + rl.shape[0]] = rl @ (q[E:2 * E] * rk[0])
        if net["pointer"] == 2:
            rr = keep[ri]
            bank = (rr @ q[2 * E:3 * E])[:, None] + (rr @ q[3 * E:])[None, :]
            a = net["act_bank"]
            out[a:a + bank.size] = bank.reshape(-1)
        logits = logits + out
    return logits, new_state


# ---- commands ----

def make_synthetic(out, E=32, hidden=128, layers=1, pointer=3, seed=1234, scale=0.1, state_rule="carry", layout=None):
    layout = layout or V2
    act = layout["act_size"] + 1   # the trainer's decoder also scores the no-op
    rng = np.random.default_rng(seed)
    payload = bytearray()
    widths = [t[3] for t in layout["tables"]]
    for r, c in block_shapes(widths, E, hidden, layers, act, pointer):
        a = (rng.standard_normal(r * c) * scale).astype("<f4")
        a = np.concatenate([a, np.zeros(pad8(r * c) - r * c, dtype="<f4")])
        payload += a.tobytes()
    data = header_bytes(layout, E, hidden, layers, pointer, state_rule, act) + bytes(payload)
    open(out, "wb").write(data)
    print("wrote %s (%d bytes)" % (out, len(data)))


def make_obs(out, n, seed=99, layout=None):
    layout = layout or V2
    rng = np.random.default_rng(seed)
    size = sum(t[2] * t[3] for t in layout["tables"])
    lines = []
    for i in range(n):
        if i == n // 2:
            lines.append("reset")
        elif i % 3 == 0:
            lines.append("turn")
        obs = np.zeros(size)
        for _, off, rows, width in layout["tables"]:
            nreal = rng.integers(1, rows + 1)
            for r in range(nreal):
                row = rng.random(width)
                row[0] = 1.0
                obs[off + r * width: off + (r + 1) * width] = row
        lines.append(" ".join("%.6g" % v for v in obs))
    open(out, "w").write("\n".join(lines) + "\n")
    print("wrote %s (%d observations)" % (out, n))


def expect(weights, obs_path, out):
    net = read_weights(weights)
    zero = lambda: [np.zeros(net["hidden"]) for _ in range(net["layers"])]
    state = zero()
    res = []
    for line in open(obs_path):
        line = line.strip()
        if not line or line == "reset":
            state = zero()
            continue
        if line == "turn":
            if net["rule"] == 1:   # turn: 0.5 everywhere at each turn start
                state = [np.full(net["hidden"], 0.5) for _ in range(net["layers"])]
            continue
        if net["rule"] == 2:       # zero: zero state at every decision
            state = zero()
        obs = np.array([float(v) for v in line.split()])
        logits, state = forward(net, obs, state)
        res.append(" ".join(repr(float(v)) for v in logits))
    open(out, "w").write("\n".join(res) + "\n")
    print("wrote %s (%d rows of %d logits)" % (out, len(res), net["act"]))


def main(argv):
    if len(argv) >= 2 and argv[0] == "make-synthetic":
        make_synthetic(argv[1], state_rule=argv[2] if len(argv) >= 3 else "carry")
    elif len(argv) >= 3 and argv[0] == "make-obs":
        make_obs(argv[1], int(argv[2]))
    elif len(argv) >= 4 and argv[0] == "expect":
        expect(argv[1], argv[2], argv[3])
    else:
        print(__doc__)
        sys.exit(2)


if __name__ == "__main__":
    main(sys.argv[1:])
