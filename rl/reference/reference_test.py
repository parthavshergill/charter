"""The reference test: does an encoder's forward and backward match the PyTorch reference?

    python3 rl/reference/reference_test.py                       # self-test, with a seeded error
    python3 rl/reference/reference_test.py --check CANDIDATE.npz --encoder entity

A candidate `.npz` holds, for the same weights and inputs: `obs` (batch x obs_size), every parameter of the reference
encoder by its PyTorch name (`per.spots.weight`, ...), the encoder output `out`, the upstream gradient `grad_out`, and
the candidate's gradients `grad.<name>` for each parameter. `--dump` writes such a file from the reference itself,
to start from. Tolerance: relative error 1e-3 on outputs and gradients, as bf16 kernels need.

The self-test also checks rl/reference/policy.py, the NumPy forward the eval uses, against the PyTorch policy.
"""
import argparse
import os
import sys

import numpy as np
import torch

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "env"))
from encoders import ENCODERS, LAYOUT, Policy, count_params  # noqa: E402

TOL = 1e-3


def real_obs(batch, seed=0):
    """Observations from real games, so padding and `real` columns look as they do in training."""
    from charter import Game
    rng = np.random.default_rng(seed)
    games = ["island", "not-catan", "slime-parliament", "pirate-republic"]
    out = []
    g = Game({"game": games[0], "lineup": ["caller"] * 4, "seed": seed, "vote_mode": "policy", "law_every": 2})
    k = 0
    while len(out) < batch:
        if g.over:
            k += 1
            g = Game({"game": games[k % len(games)], "lineup": ["caller"] * 4, "seed": seed + k,
                      "vote_mode": "policy", "law_every": 2})
        if rng.random() < 0.3:
            out.append(g.obs().copy())
        legal = g.legal()
        g.step(int(legal[rng.integers(len(legal))]))
    return torch.tensor(np.stack(out))


def reference_dump(encoder, obs, seed=0):
    torch.manual_seed(seed)
    enc = ENCODERS[encoder](obs.shape[1], 128)
    out = enc(obs)
    grad_out = torch.randn_like(out)
    out.backward(grad_out)
    d = {"obs": obs.numpy(), "out": out.detach().numpy(), "grad_out": grad_out.numpy()}
    for n, p in enc.named_parameters():
        d[n] = p.detach().numpy()
        d["grad." + n] = p.grad.numpy()
    return d


def rel(a, b):
    return float(np.abs(a - b).max() / max(1e-6, np.abs(b).max()))


def check(encoder, cand):
    """Errors of a candidate against the reference, as (name, relative error) with those over TOL."""
    obs = torch.tensor(cand["obs"])
    enc = ENCODERS[encoder](obs.shape[1], cand["out"].shape[1])
    with torch.no_grad():
        for n, p in enc.named_parameters():
            p.copy_(torch.tensor(cand[n]))
    out = enc(obs)
    out.backward(torch.tensor(cand["grad_out"]))
    errs = [("out", rel(cand["out"], out.detach().numpy()))]
    errs += [("grad." + n, rel(cand["grad." + n], p.grad.numpy())) for n, p in enc.named_parameters()]
    return errs, [e for e in errs if e[1] > TOL]


def numpy_policy_matches():
    """rl/reference/policy.py against the PyTorch policy, flat encoder, over three steps."""
    from policy import FlatNet
    torch.manual_seed(1)
    pol = Policy("flat", hidden=32, layers=2)
    obs = real_obs(3, seed=5)
    net = FlatNet(pol.encoder.w.detach().numpy(), pol.decoder.detach().numpy(),
                  [g.w.detach().numpy() for g in pol.grus], LAYOUT["act_size"] + 1)
    st_t, st_n, worst = pol.initial_state(1), net.initial_state(), 0.0
    for i in range(3):
        lt, vt, st_t = pol(obs[i:i + 1], st_t)
        ln, vn, st_n = net.forward(obs[i].numpy(), st_n)
        worst = max(worst, rel(ln, lt[0].detach().numpy()), abs(float(vn) - float(vt[0].detach())))
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check")
    ap.add_argument("--encoder", default="flat")
    ap.add_argument("--dump")
    args = ap.parse_args()
    if args.check:
        errs, bad = check(args.encoder, np.load(args.check))
        for n, e in errs:
            print(f"{'FAIL' if e > TOL else 'ok  '} {n}: {e:.2e}")
        sys.exit(1 if bad else 0)
    obs = real_obs(16)
    if args.dump:
        np.savez(args.dump, **reference_dump(args.encoder, obs))
        print(f"wrote {args.dump}")
        return
    fails = 0
    for name in ENCODERS:
        d = reference_dump(name, obs)
        _, bad = check(name, d)
        params = count_params(Policy(name))
        print(f"{'PASS' if not bad else 'FAIL'} reference {name} against itself; policy parameters {params}")
        fails += bool(bad)
        # Seeded error: one gradient entry off by 1%.
        key = next(k for k in d if k.startswith("grad.") and d[k].size > 1)
        d[key] = d[key].copy()
        d[key].flat[0] += 0.01 * np.abs(d[key]).max() + 0.1 * abs(d[key].flat[0]) + 1e-3
        _, bad = check(name, d)
        print(f"{'PASS' if bad else 'FAIL'} reference {name} seeded error in {key} caught: {bad[:1]}")
        fails += not bad
    worst = numpy_policy_matches()
    print(f"{'PASS' if worst < 1e-4 else 'FAIL'} NumPy policy (eval) matches PyTorch: worst error {worst:.1e}")
    fails += worst >= 1e-4
    print("ALL PASS" if not fails else f"{fails} FAILED")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
