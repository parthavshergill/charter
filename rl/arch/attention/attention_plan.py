"""The `attention` encoder's sizes, where its inputs sit in the observation, and its weights' shapes.
No torch here, so rl/eval can use it. attention_ref.py says what the encoder computes."""
from __future__ import annotations

import json
from dataclasses import dataclass

D = 32
HEADS = 8
HEAD_DIM = 8
ATT = HEADS * HEAD_DIM


@dataclass(frozen=True)
class Block:
    name: str
    offset: int
    rows: int
    width: int


@dataclass(frozen=True)
class Plan:
    """Which parts of the observation are context and which are tokens."""
    obs_size: int
    context: tuple[Block, ...]
    tokens: tuple[Block, ...]

    @property
    def ctx_width(self) -> int:
        return sum(b.width for b in self.context)

    @property
    def n_tokens(self) -> int:
        return sum(b.rows for b in self.tokens)


def plan_from_layout(layout: dict, obs_size: int) -> Plan:
    """One-row tables are context; the others are tokens. The `moves` table counts only if the
    observation includes it (`obs_size == full_size`)."""
    ctx, tok = [], []
    for t in layout["tables"]:
        if t["offset"] + t["rows"] * t["width"] > obs_size:
            continue
        b = Block(t["name"], t["offset"], t["rows"], t["width"])
        (ctx if t["rows"] == 1 else tok).append(b)
    assert obs_size in (layout["base_size"], layout["full_size"]), obs_size
    return Plan(obs_size, tuple(ctx), tuple(tok))


def load_plan(path: str, obs_size: int | None = None) -> Plan:
    layout = json.load(open(path))
    return plan_from_layout(layout, obs_size or layout["base_size"])


def param_shapes(plan: Plan, hidden: int) -> list[tuple[str, tuple[int, int]]]:
    shapes = [("w_ctx", (D, plan.ctx_width))]
    shapes += [(f"w_{b.name}", (D, b.width)) for b in plan.tokens]
    shapes += [("wq", (ATT, D)), ("wk", (ATT, D)), ("wv", (ATT, D)), ("wout", (hidden, ATT + D))]
    return shapes


def param_count(plan: Plan, hidden: int) -> int:
    return sum(r * c for _, (r, c) in param_shapes(plan, hidden))


def flops_per_obs(plan: Plan, hidden: int) -> int:
    """Multiply-adds for one observation in the CUDA encoder, which folds Wk and Wv out of the token loop."""
    n = plan.n_tokens
    emb = D * (plan.ctx_width + sum(b.rows * b.width for b in plan.tokens))
    att = n * HEADS * D * 2 + ATT * D * 3
    return emb + att + hidden * (ATT + D)
