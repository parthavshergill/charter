"""PyTorch reference of the policy: an encoder, PufferLib's MinGRU, and its linear decoder.

A custom encoder written for PufferLib (CUDA, hand-written gradients) must match one of these on the same weights and
inputs: `reference_test.py` checks forward outputs and gradients. The shapes follow `rl/layout.json`.

Encoders:
- `flat`: one linear map, no bias, no activation, as PufferLib's default.
- `entity`: per table of entities (rows), a shared linear + ReLU per row, a max over the rows whose `real` is 1, then
  the pooled vectors and the single-row tables go through one linear map + ReLU. Modelled on `ocean/asteroids`.
- `attention`: each row of every table becomes a token (a per-table linear map), one masked single-head
  self-attention layer with a residual, a mean over real tokens, and a linear map + ReLU.
"""
import json
import os

import torch
import torch.nn as nn
import torch.nn.functional as F

LAYOUT = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "layout.json")))
ENTITY_TABLES = ["seats", "resources", "kinds", "tiles", "spots", "links", "laws"]
SINGLE_TABLES = ["global", "proposal"]


def table(name):
    return next(t for t in LAYOUT["tables"] if t["name"] == name)


def rows_of(obs, name):
    """(batch, rows, width) for a table of the observation."""
    t = table(name)
    return obs[:, t["offset"]:t["offset"] + t["rows"] * t["width"]].reshape(-1, t["rows"], t["width"])


class Flat(nn.Module):
    def __init__(self, obs_size, hidden):
        super().__init__()
        self.w = nn.Parameter(torch.randn(hidden, obs_size) * obs_size ** -0.5)

    def forward(self, obs):
        return obs @ self.w.T


class Entity(nn.Module):
    def __init__(self, obs_size, hidden, width=32):
        super().__init__()
        self.per = nn.ModuleDict({n: nn.Linear(table(n)["width"], width) for n in ENTITY_TABLES})
        single = sum(table(n)["width"] for n in SINGLE_TABLES)
        self.out = nn.Linear(width * len(ENTITY_TABLES) + single, hidden)

    def forward(self, obs):
        parts = []
        for n in ENTITY_TABLES:
            x = rows_of(obs, n)
            h = F.relu(self.per[n](x))
            real = x[..., 0:1] > 0.5
            h = torch.where(real, h, torch.full_like(h, -1e9))
            pooled = h.max(dim=1).values
            parts.append(torch.where(real.any(dim=1), pooled, torch.zeros_like(pooled)))
        for n in SINGLE_TABLES:
            parts.append(rows_of(obs, n).flatten(1))
        return F.relu(self.out(torch.cat(parts, dim=1)))


class Attention(nn.Module):
    def __init__(self, obs_size, hidden, d=32):
        super().__init__()
        self.embed = nn.ModuleDict({n: nn.Linear(table(n)["width"], d) for n in ENTITY_TABLES + SINGLE_TABLES})
        self.q, self.k, self.v = nn.Linear(d, d, bias=False), nn.Linear(d, d, bias=False), nn.Linear(d, d, bias=False)
        self.out = nn.Linear(d, hidden)
        self.d = d

    def forward(self, obs):
        toks, masks = [], []
        for n in ENTITY_TABLES + SINGLE_TABLES:
            x = rows_of(obs, n)
            toks.append(self.embed[n](x))
            masks.append(x[..., 0] > 0.5)
        t = torch.cat(toks, dim=1)
        m = torch.cat(masks, dim=1)
        att = (self.q(t) @ self.k(t).transpose(1, 2)) / self.d ** 0.5
        att = att.masked_fill(~m[:, None, :], -1e9).softmax(dim=-1)
        t = t + att @ self.v(t)
        mf = m.float()[..., None]
        pooled = (t * mf).sum(1) / mf.sum(1).clamp(min=1)
        return F.relu(self.out(pooled))


ENCODERS = {"flat": Flat, "entity": Entity, "attention": Attention}


class MinGRU(nn.Module):
    """One MinGRU layer as PufferLib computes it at the pinned commit (no bias)."""

    def __init__(self, hidden):
        super().__init__()
        self.w = nn.Parameter(torch.randn(3 * hidden, hidden) * hidden ** -0.5)

    def forward(self, x, state):
        h = x.shape[1]
        c = x @ self.w.T
        hidden, gate, proj = c[:, :h], c[:, h:2 * h], c[:, 2 * h:]
        tilde = torch.where(hidden >= 0, hidden + 0.5, torch.sigmoid(hidden))
        new = state + torch.sigmoid(gate) * (tilde - state)
        s = torch.sigmoid(proj)
        return s * new + (1 - s) * x, new


class Policy(nn.Module):
    def __init__(self, encoder="flat", obs_size=None, hidden=128, layers=1, act_size=None):
        super().__init__()
        obs_size = obs_size or LAYOUT["base_size"]
        act_size = act_size or LAYOUT["act_size"] + 1
        self.encoder = ENCODERS[encoder](obs_size, hidden)
        self.grus = nn.ModuleList([MinGRU(hidden) for _ in range(layers)])
        self.decoder = nn.Parameter(torch.randn(act_size + 1, hidden) * hidden ** -0.5)
        self.hidden = hidden

    def forward(self, obs, state):
        """obs (batch, obs_size), state list of (batch, hidden). Returns logits, value, new state."""
        x = self.encoder(obs)
        new = []
        for g, s in zip(self.grus, state):
            x, s2 = g(x, s)
            new.append(s2)
        y = x @ self.decoder.T
        return y[:, :-1], y[:, -1], new

    def initial_state(self, batch):
        return [torch.zeros(batch, self.hidden) for _ in self.grus]


def count_params(module):
    return sum(p.numel() for p in module.parameters())
