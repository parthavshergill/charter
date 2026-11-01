"""Read a PufferLib .bin checkpoint and run the policy with no PufferLib code.

The file is raw little-endian float32 with no header. Each block starts on a
multiple of 8 floats. Order: encoder, decoder (value is the last output), then
one block per GRU layer. Usage: policy_reader.py FILE OBS HIDDEN LAYERS ACTIONS
"""
import array
import math
import sys

path, obs_n, hid, layers, act_n = sys.argv[1], *map(int, sys.argv[2:6])
w = array.array("f")
with open(path, "rb") as f:
    w.frombytes(f.read())
pos = 0


def block(rows, cols):
    global pos
    data = w[pos:pos + rows * cols]
    pos = (pos + rows * cols + 7) & ~7
    return [data[r * cols:(r + 1) * cols] for r in range(rows)]


def linear(m, x):
    return [sum(a * b for a, b in zip(row, x)) for row in m]


def sigmoid(v):
    return 1.0 / (1.0 + math.exp(-v))


enc = block(hid, obs_n)
dec = block(act_n + 1, hid)
gru = [block(3 * hid, hid) for _ in range(layers)]
assert pos == len(w), (pos, len(w))
state = [[0.0] * hid for _ in range(layers)]
obs = [(i % 7) / 7.0 for i in range(obs_n)]
for step in range(3):
    x = linear(enc, obs)
    for lay in range(layers):
        c = linear(gru[lay], x)
        out = []
        for h in range(hid):
            hidden, gate, hw = c[h], c[hid + h], c[2 * hid + h]
            tilde = hidden + 0.5 if hidden >= 0 else sigmoid(hidden)
            s = state[lay][h]
            m = s + sigmoid(gate) * (tilde - s)
            hs = sigmoid(hw)
            out.append(hs * m + (1 - hs) * x[h])
            state[lay][h] = m
        x = out
    print("py step", step, " ".join(f"{v:.4f}" for v in linear(dec, x)))
