"""PyTorch version of the `attention` encoder, written plainly so it can be read and checked.

What the encoder does, for one observation:

1. The one-row tables (`global`, `proposal`) are joined and pass through one linear layer and a ReLU. This is
   the context `c`, of width `D`.
2. Each row of every other table is a token. Each table has its own linear layer and ReLU, giving width `D`.
   A row whose `real` column (column 0) is 0 is padding: no head looks at it.
3. `HEADS` heads each ask one question of all the tokens. The question comes from the context:
   `q = Wq c`. Each head scores the tokens with `k = Wk x`, takes the softmax over the real tokens only, and
   returns the weighted sum of `v = Wv x`. With no real token, a head returns 0.
4. The heads' answers and `c` are joined, and one linear layer maps them to the trainer's hidden size.

There are no biases. Column 0 of every row is 1 for a real row, so it acts as the bias.

Weights, in the order the CUDA encoder registers them (and the order of the checkpoint):
`w_ctx [D, ctx_width]`, then one `w_<table> [D, width]` per token table in layout order, then
`wq, wk, wv [HEADS*HEAD_DIM, D]`, then `wout [hidden, HEADS*HEAD_DIM + D]`.
"""
from __future__ import annotations

import math

import torch

try:
    from .attention_plan import ATT, D, HEAD_DIM, HEADS, Block, Plan, flops_per_obs, load_plan, param_count, param_shapes, plan_from_layout  # noqa: F401
except ImportError:  # run from this folder
    from attention_plan import ATT, D, HEAD_DIM, HEADS, Block, Plan, flops_per_obs, load_plan, param_count, param_shapes, plan_from_layout  # noqa: F401


def init_params(plan: Plan, hidden: int, seed: int = 0) -> dict[str, torch.Tensor]:
    """Uniform(-gain/sqrt(fan_in), gain/sqrt(fan_in)), as `puf_kaiming_init` does: gain sqrt(2) before a ReLU."""
    g = torch.Generator().manual_seed(seed)
    out = {}
    for name, (r, c) in param_shapes(plan, hidden):
        gain = math.sqrt(2.0) if name.startswith("w_") else 1.0
        bound = gain / math.sqrt(c)
        out[name] = (torch.rand(r, c, generator=g, dtype=torch.float64) * 2 - 1) * bound
    return out


def forward(plan: Plan, p: dict[str, torch.Tensor], obs: torch.Tensor) -> torch.Tensor:
    """obs [B, obs_size] -> [B, hidden]. Standard multi-head attention, with no shortcuts."""
    B = obs.shape[0]
    ctx_in = torch.cat([obs[:, b.offset:b.offset + b.width] for b in plan.context], dim=1)
    c = torch.relu(ctx_in @ p["w_ctx"].T)                                   # [B, D]
    xs, masks = [], []
    for b in plan.tokens:
        rows = obs[:, b.offset:b.offset + b.rows * b.width].reshape(B, b.rows, b.width)
        xs.append(torch.relu(rows @ p[f"w_{b.name}"].T))                    # [B, rows, D]
        masks.append(rows[:, :, 0] > 0.5)
    x = torch.cat(xs, dim=1)                                                # [B, N, D]
    real = torch.cat(masks, dim=1)                                          # [B, N]
    q = (c @ p["wq"].T).reshape(B, HEADS, HEAD_DIM)
    k = (x @ p["wk"].T).reshape(B, -1, HEADS, HEAD_DIM)
    v = (x @ p["wv"].T).reshape(B, -1, HEADS, HEAD_DIM)
    s = torch.einsum("bha,bnha->bhn", q, k) / math.sqrt(HEAD_DIM)
    s = s.masked_fill(~real[:, None, :], float("-inf"))
    any_real = real.any(dim=1)[:, None, None]
    a = torch.where(any_real, torch.softmax(torch.where(any_real, s, torch.zeros_like(s)), dim=2),
                    torch.zeros_like(s))
    y = torch.einsum("bhn,bnha->bha", a, v).reshape(B, ATT)
    return torch.cat([y, c], dim=1) @ p["wout"].T


def grads(plan: Plan, p: dict[str, torch.Tensor], obs: torch.Tensor, grad_out: torch.Tensor):
    """Gradients of sum(forward * grad_out) with respect to every weight, by autograd."""
    leaves = {k: v.detach().clone().requires_grad_(True) for k, v in p.items()}
    out = forward(plan, leaves, obs)
    (out * grad_out).sum().backward()
    return out.detach(), {k: v.grad.detach() for k, v in leaves.items()}
