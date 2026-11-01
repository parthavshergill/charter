"""Reference test for the CUDA `attention` encoder.

The CUDA encoder's forward output and hand-written weight gradients must match the plain PyTorch version
(attention_ref.py, float64 autograd) on the same weights and observations. Three builds run:

- float32: must match tightly (each tensor's largest error under 1e-4 of its largest value).
- bf16, what training uses: given the same bf16-rounded inputs, must match loosely (whole-tensor relative
  error under 2e-2, largest error under 5e-2 of the largest value). bf16 keeps 8 bits of mantissa, and
  each gradient sums over every row of the batch.
- float32 with a seeded error (CA_SEEDED_ERROR drops a term from the softmax's gradient): the test must
  find it. If this build passes, the test is too weak and the whole run fails.

It also checks that attention_layout.h matches the layout, and that the NumPy forward rl/eval uses
(attention_np.py), reading a checkpoint laid out as PufferLib writes it, gives the PyTorch numbers.

Usage: python reference_test.py PUFFERLIB_DIR LAYOUT_JSON BUILD_DIR [--obs OBS_NPY] [--bench B]
`--obs` adds real observations from the environment to the random ones.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

import numpy as np
import torch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import attention_ref as R  # noqa: E402

HIDDEN = 128


def random_obs(plan: R.Plan, B: int, rng: np.random.Generator) -> np.ndarray:
    """Observations shaped like the real ones: each token table has a run of real rows (column 0 is 1)
    and zeroed padding after it. Observation 0 has no real row at all; observation 1 has every row real."""
    obs = np.abs(rng.normal(size=(B, plan.obs_size))) * rng.choice([0.0, 1.0], size=(B, plan.obs_size), p=[0.3, 0.7])
    for blk in plan.context:
        obs[:, blk.offset] = 1.0
    for blk in plan.tokens:
        for b in range(B):
            n = 0 if b == 0 else blk.rows if b == 1 else int(rng.integers(0, blk.rows + 1))
            for r in range(blk.rows):
                o = blk.offset + r * blk.width
                if r < n:
                    obs[b, o] = 1.0
                else:
                    obs[b, o:o + blk.width] = 0.0
    return obs.astype(np.float32)


def build(pufferlib: Path, out: Path, extra: list[str]) -> None:
    cuda = os.environ.get("CUDA_HOME", "/usr/local/cuda")
    cmd = [f"{cuda}/bin/nvcc", "-O2", "-std=c++17", "-arch=native",
           f"-I{pufferlib}", f"-I{pufferlib}/src", f"-I{pufferlib}/vendor", f"-I{HERE}",
           f"-I{cuda}/include", f"-I{cuda}/include/cccl", f"-I{pufferlib}/raylib-5.5_linux_amd64/include",
           f'-DENV_HEADER="{pufferlib}/ocean/minimal/minimal.h"', "-DPUFFER_ENV_NAME=\"minimal\"",
           "-Xcompiler=-fopenmp", "-Xcompiler=-Wno-narrowing", "--diag-suppress=2361,111,128,177,550",
           *extra, str(HERE / "attention_test.cu"), "-o", str(out),
           f"-L{cuda}/lib64", "-lcudart", "-lnccl", "-lnvidia-ml", "-lcublas", "-lcusolver", "-lcurand",
           f"{pufferlib}/raylib-5.5_linux_amd64/lib/libraylib.a", "-lGL", "-lm", "-lpthread", "-ldl", "-lrt", "-lomp5"]
    print("build:", out.name, " ".join(extra), flush=True)
    subprocess.run(cmd, check=True)


def compare(name: str, got: np.ndarray, ref: np.ndarray, tol: float, tol_l2: float | None):
    """Largest error over the largest value must be under `tol`; with `tol_l2`, also
    |got - ref| / |ref| (whole tensor) under `tol_l2`."""
    scale = float(np.abs(ref).max()) or 1.0
    err = float(np.abs(got - ref).max()) / scale
    l2 = float(np.linalg.norm(got - ref) / (np.linalg.norm(ref) + 1e-30))
    ok = err < tol and (tol_l2 is None or l2 < tol_l2)
    return ok, f"  {name:14s} max err/scale {err:.2e}  rel L2 {l2:.2e}  {'ok' if ok else 'FAIL'}"


def bf16_round(x: np.ndarray) -> np.ndarray:
    return torch.tensor(x, dtype=torch.float32).to(torch.bfloat16).to(torch.float32).numpy()


def run_case(binary: Path, case: Path, plan: R.Plan, P: dict, obs: np.ndarray, gout: np.ndarray,
             tol: float, tol_l2: float | None, bench: int = 0, bf16: bool = False) -> tuple[bool, list[str], str]:
    B = obs.shape[0]
    if bf16:   # the bf16 build rounds its inputs; give the reference the same rounded inputs
        obs, gout = bf16_round(obs), bf16_round(gout.astype(np.float32))
        P = {k: torch.tensor(bf16_round(v.numpy().astype(np.float32)), dtype=torch.float64) for k, v in P.items()}
    case.mkdir(parents=True, exist_ok=True)
    shapes = R.param_shapes(plan, HIDDEN)
    np.concatenate([P[n].numpy().astype(np.float32).ravel() for n, _ in shapes]).tofile(case / "weights.f32")
    obs.tofile(case / "obs.f32")
    gout.astype(np.float32).tofile(case / "gout.f32")
    args = [str(binary), str(case), str(B), str(HIDDEN)] + ([str(bench)] if bench else [])
    proc = subprocess.run(args, capture_output=True, text=True)
    if proc.returncode != 0:
        return False, [f"  binary failed ({proc.returncode}): {proc.stderr.strip()}"], proc.stdout
    # The reference sees the same float32-rounded inputs, computed in float64.
    P64 = {k: torch.tensor(v.numpy().astype(np.float32), dtype=torch.float64) for k, v in P.items()}
    ref_out, ref_g = R.grads(plan, P64, torch.tensor(obs, dtype=torch.float64), torch.tensor(gout, dtype=torch.float64))
    lines, ok = [], True
    for fname in ("out.f32", "out_rollout.f32"):
        got = np.fromfile(case / fname, dtype=np.float32).reshape(B, HIDDEN)
        o, line = compare(fname.split(".")[0], got, ref_out.numpy(), tol, tol_l2)
        ok &= o
        lines.append(line)
    flat = np.fromfile(case / "grads.f32", dtype=np.float32)
    at = 0
    for n, (r, c) in shapes:
        got = flat[at:at + r * c].reshape(r, c)
        at += r * c
        o, line = compare("d" + n, got, ref_g[n].numpy(), tol, tol_l2)
        ok &= o
        lines.append(line)
    return ok, lines, proc.stdout


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("pufferlib", type=Path)
    ap.add_argument("layout", type=Path)
    ap.add_argument("build_dir", type=Path)
    ap.add_argument("--obs", type=Path, default=None)
    ap.add_argument("--bench", type=int, default=0)
    ap.add_argument("--json", type=Path, default=None)
    a = ap.parse_args()
    a.build_dir.mkdir(parents=True, exist_ok=True)
    subprocess.run([sys.executable, str(HERE / "gen_layout.py"), str(a.layout),
                    str(a.build_dir / "attention_layout.h")], check=True)
    if (a.build_dir / "attention_layout.h").read_text() != (HERE / "attention_layout.h").read_text():
        print("FAILED: attention_layout.h does not match the layout; run gen_layout.py")
        return 1
    plan = R.load_plan(str(a.layout))
    rng = np.random.default_rng(7)
    obs = random_obs(plan, 37, rng)
    if a.obs is not None:
        real = np.load(a.obs).astype(np.float32).reshape(-1, plan.obs_size)[:64]
        obs = np.concatenate([obs, real], 0)
        print(f"added {real.shape[0]} observations from the environment")
    gout = rng.normal(size=(obs.shape[0], HIDDEN))
    P = R.init_params(plan, HIDDEN, seed=11)
    # Larger weights than the init make the softmax less uniform, so its gradient matters more.
    P = {k: (v * 3 if k in ("wq", "wk") else v) for k, v in P.items()}

    builds = [("float32", ["-DPRECISION_FLOAT"], 1e-4, None, True),
              ("bf16", ["-DCA_PROFILE"], 5e-2, 2e-2, True),
              ("float32 + seeded error", ["-DPRECISION_FLOAT", "-DCA_SEEDED_ERROR"], 1e-4, None, False)]
    report, all_ok = {}, True
    for label, flags, tol, tol_l2, should_pass in builds:
        binary = a.build_dir / ("attention_test_" + label.replace(" ", "").replace("+", "_"))
        build(a.pufferlib, binary, flags)
        ok, lines, stdout = run_case(binary, a.build_dir / f"case_{binary.name}", plan, P, obs, gout,
                                     tol, tol_l2, bench=a.bench if label == "bf16" else 0, bf16=label == "bf16")
        verdict = "passed" if ok else "failed"
        good = ok == should_pass
        all_ok &= good
        print(f"{label}: {verdict} ({'as it should' if good else 'WRONG: expected ' + ('pass' if should_pass else 'fail')})")
        print("\n".join(lines))
        print(stdout.strip())
        report[label] = {"passed": ok, "expected_pass": should_pass, "lines": lines, "stdout": stdout}
    # The NumPy forward rl/eval uses, read from a checkpoint laid out as PufferLib writes it.
    import attention_np
    ckpt = a.build_dir / "fake_ckpt.bin"
    act = json.load(open(a.layout))["act_size"] + 1
    dec = rng.normal(size=(act + 1, HIDDEN)).astype(np.float32)
    gru = rng.normal(size=(3 * HIDDEN, HIDDEN)).astype(np.float32)
    blocks = [P[n].numpy().astype(np.float32) for n, _ in R.param_shapes(plan, HIDDEN)] + [dec, gru]
    flat = []
    for blk in blocks:
        flat.append(blk.ravel())
        flat.append(np.zeros((-blk.size) % 8, np.float32))
    np.concatenate(flat).tofile(ckpt)
    enc, dec2, grus = attention_np.load(str(ckpt), {"obs_size": plan.obs_size, "hidden": HIDDEN, "layers": 1,
                                                    "act_size": act}, layout_path=str(a.layout))
    P32 = {k: torch.tensor(v.numpy().astype(np.float32), dtype=torch.float64) for k, v in P.items()}
    ref = R.forward(plan, P32, torch.tensor(obs, dtype=torch.float64)).numpy()
    got = np.stack([enc(o) for o in obs])
    np_ok, line = compare("numpy out", got, ref, 1e-4, None)
    np_ok &= bool(np.array_equal(dec2, dec) and np.array_equal(grus[0], gru))
    print(f"numpy eval forward: {'passed' if np_ok else 'failed'}\n{line}")
    all_ok &= np_ok
    report["numpy"] = {"passed": np_ok, "lines": [line]}
    print("REFERENCE TEST", "PASSED" if all_ok else "FAILED",
          f"(params {R.param_count(plan, HIDDEN)} at hidden {HIDDEN}, {obs.shape[0]} observations)")
    if a.json:
        a.json.write_text(json.dumps({"passed": all_ok, "builds": report}, indent=1))
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
