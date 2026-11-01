"""Run a trained policy in NumPy, with no PufferLib code, for rl/eval.

A policy is a weights file plus a JSON meta next to it (`<file>.json`):

    {"name": "flat-1", "format": "puffer-flat", "obs_size": 4434, "act_size": 696, "hidden": 128, "layers": 1,
     "settings": {"vote_mode": "bot"}}

Formats:
- `puffer-flat`: a PufferLib `.bin` checkpoint at the pinned commit: raw float32, blocks padded to 8 floats, in the
  order encoder (hidden x obs), decoder (act + 1 x hidden, the last row is the value), then one MinGRU block
  (3 hidden x hidden) per layer. rl/puffer-smoke/policy_reader.py checked this order against PufferLib's C forward.
- `npz-flat`: the same arrays in an `.npz`: `encoder`, `decoder`, `gru0`, `gru1`, ...
- `puffer-attention`: a `.bin` checkpoint of the `attention` encoder (rl/arch/attention/attention_np.py).

A custom encoder adds a format here with its own forward. The MinGRU and decoder stay the same.
"""
import numpy as np


def sigmoid(x):
    return 1.0 / (1.0 + np.exp(-x))


def mingru_step(W, x, state):
    """One MinGRU layer at PufferLib's pinned commit. Returns (output, new state)."""
    h = W.shape[1]
    c = W @ x
    hidden, gate, proj = c[:h], c[h:2 * h], c[2 * h:]
    tilde = np.where(hidden >= 0, hidden + 0.5, sigmoid(hidden))
    new = state + sigmoid(gate) * (tilde - state)
    s = sigmoid(proj)
    return s * new + (1 - s) * x, new


class FlatNet:
    def __init__(self, encoder, decoder, grus, act_size):
        self.encoder, self.decoder, self.grus = encoder, decoder, grus
        self.act_size = act_size

    def forward(self, obs, state):
        x = self.encoder(obs) if callable(self.encoder) else self.encoder @ obs
        out = []
        for W, s in zip(self.grus, state):
            x, s2 = mingru_step(W, x, s)
            out.append(s2)
        y = self.decoder @ x
        return y[:-1], y[-1], out

    def initial_state(self):
        return [np.zeros(W.shape[1], np.float32) for W in self.grus]

    def player(self, seed, greedy=True):
        return Player(self, seed, greedy)


class Player:
    """Plays one seat. The state carries over between this seat's decisions and resets each game."""

    def __init__(self, net, seed, greedy):
        self.net, self.rng, self.greedy = net, np.random.default_rng(seed), greedy
        self.reset()

    def reset(self):
        self.state = self.net.initial_state()

    def act(self, game):
        obs = game.obs()
        mask = game.mask()
        logits, _, self.state = self.net.forward(obs, self.state)
        logits = logits[:len(mask)].astype(np.float64)
        logits[mask == 0] = -np.inf
        if self.greedy:
            return int(np.argmax(logits))
        p = np.exp(logits - logits.max())
        p /= p.sum()
        return int(self.rng.choice(len(p), p=p))


def read_puffer_bin(path, obs_size, hidden, layers, act_size):
    w = np.fromfile(path, dtype="<f4")
    pos = 0

    def block(rows, cols):
        nonlocal pos
        a = w[pos:pos + rows * cols].reshape(rows, cols)
        pos = (pos + rows * cols + 7) & ~7
        return a

    enc = block(hidden, obs_size)
    dec = block(act_size + 1, hidden)
    grus = [block(3 * hidden, hidden) for _ in range(layers)]
    if pos != len(w) and (len(w) + 7) & ~7 != pos:
        raise ValueError(f"{path}: {len(w)} floats, expected {pos} for this shape")
    return enc, dec, grus


def load_policy(path, meta):
    fmt = meta.get("format", "puffer-flat")
    if fmt == "puffer-flat":
        enc, dec, grus = read_puffer_bin(path, meta["obs_size"], meta["hidden"], meta["layers"], meta["act_size"])
    elif fmt == "npz-flat":
        z = np.load(path)
        enc, dec = z["encoder"], z["decoder"]
        grus = [z[f"gru{i}"] for i in range(meta["layers"])]
    elif fmt == "puffer-attention":
        from arch.attention.attention_np import load as load_attention
        enc, dec, grus = load_attention(path, meta)
    else:
        raise ValueError(f"unknown policy format {fmt}")
    return FlatNet(enc if callable(enc) else enc.astype(np.float32), dec.astype(np.float32), [g.astype(np.float32) for g in grus],
                   meta["act_size"])
