"""Reference test for the entity encoder.

The CUDA encoder (charter_entity.cu) and the PyTorch one (entity_torch.py) get
the same weights and the same observations. Their outputs must match, and the
CUDA encoder's hand-written weight gradients must match PyTorch's autograd.
Then the test builds the CUDA encoder twice more with a seeded error, and each
of those builds must fail the same comparison.

Usage: python test_reference.py <pufferlib dir> <layout.json> <work dir>
Needs nvcc and a GPU. Prints one JSON line per build and exits 1 on failure.
"""
import ctypes, json, subprocess, sys
from pathlib import Path

import numpy as np
import torch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from entity_torch import encode  # noqa: E402
from gen_layout import header, tables  # noqa: E402

BATCH, HIDDEN = 37, 128
# Largest difference over largest value. bf16 keeps 8 bits, about 0.4% per stored number, and the
# hidden values and gradients are stored in bf16 between steps, so its bound is looser.
TOL = {"float": 1e-4, "bf16": 5e-2}


def build(puffer, work, seeded, precision):
    raylib = next(puffer.glob("raylib-*/include"))
    so = work / f"entity_test_{precision}_{seeded}.so"
    flags = ["-DPRECISION_FLOAT"] if precision == "float" else []
    cmd = ["nvcc", "-shared", "-o", str(so), str(HERE / "test_entity_cuda.cu"),
           *flags, f"-DCE_SEEDED_ERROR={seeded}",
           "-I", str(puffer / "src"), "-I", str(puffer / "vendor"), "-I", str(raylib), "-I", str(work), "-I", str(HERE),
           "-Xlinker", "--no-as-needed", "-lcublas", "-lcurand", "-lnccl", "-lnvidia-ml", "-lcusolver",
           str(raylib.parent / "lib/libraylib.a"), "-lGL", "-lm", "-lpthread", "-ldl", "-lrt",
           "-Xcompiler", "-fPIC", "-Xcompiler", "-fopenmp", "-lgomp", "-O2"]
    subprocess.run(cmd, cwd=puffer, check=True)
    lib = ctypes.CDLL(str(so))
    P, I = ctypes.c_void_p, ctypes.c_int
    lib.ce_test_init.argtypes = [I, I]
    lib.ce_test_param_shape.argtypes = [I, ctypes.POINTER(I), ctypes.POINTER(I)]
    lib.ce_test_set_param.argtypes = [I, P]
    lib.ce_test_get_grad.argtypes = [I, P]
    lib.ce_test_forward.argtypes = [P, P]
    lib.ce_test_backward.argtypes = [P]
    lib.ce_test_last_error.restype = ctypes.c_char_p
    return lib


def ptr(a):
    return a.ctypes.data_as(ctypes.c_void_p)


def make_obs(ts, size, rng):
    """Random observations. Each row is real with chance 0.6, every table of some
    samples has no real rows, and padding rows hold large nonzero numbers, so a
    missing mask changes the result."""
    obs = rng.normal(size=(BATCH, size)).astype(np.float32)
    for _, off, rows, width in ts:
        block = obs[:, off:off + rows * width].reshape(BATCH, rows, width)
        real = rng.random((BATCH, rows)) < 0.6
        real[: BATCH // 6] = False
        block[:, :, 0] = real
        block[~real, 1:] *= 5.0
    return obs


def to_bf16(a):
    return torch.tensor(a).to(torch.bfloat16).to(torch.float32).numpy()


def run(lib, ts, size, rng, precision):
    lib.ce_test_init(BATCH, HIDDEN)
    n = lib.ce_test_num_params()
    shapes = []
    for i in range(n):
        r, c = ctypes.c_int(), ctypes.c_int()
        lib.ce_test_param_shape(i, ctypes.byref(r), ctypes.byref(c))
        shapes.append((r.value, c.value))
    ws = [(rng.normal(size=s) / np.sqrt(s[1])).astype(np.float32) for s in shapes]
    for i, w in enumerate(ws):
        lib.ce_test_set_param(i, ptr(np.ascontiguousarray(w)))
    obs = make_obs(ts, size, rng)
    up = rng.normal(size=(BATCH, HIDDEN)).astype(np.float32)
    if precision == "bf16":  # the GPU holds these in bf16, so give the reference the same numbers
        ws, obs, up = [to_bf16(w) for w in ws], to_bf16(obs), to_bf16(up)

    out = np.zeros((BATCH, HIDDEN), np.float32)
    lib.ce_test_forward(ptr(obs), ptr(out))
    lib.ce_test_backward(ptr(up))
    grads = [np.zeros(s, np.float32) for s in shapes]
    for i, g in enumerate(grads):
        lib.ce_test_get_grad(i, ptr(g))
    err = lib.ce_test_last_error().decode()

    tw = [torch.tensor(w, dtype=torch.float64, requires_grad=True) for w in ws]
    tables_ = [(off, rows, width) for _, off, rows, width in ts]
    ref = encode(torch.tensor(obs, dtype=torch.float64), tables_, tw[:-1], tw[-1])
    (ref * torch.tensor(up, dtype=torch.float64)).sum().backward()

    def rel(a, b):
        b = b.detach().numpy()
        return float(np.abs(a - b).max() / (np.abs(b).max() + 1e-12))

    return {"cuda_error": err, "forward": rel(out, ref),
            "grads": [rel(g, w.grad) for g, w in zip(grads, tw)]}


def main():
    puffer, layout_path, work = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
    work.mkdir(parents=True, exist_ok=True)
    layout = json.load(open(layout_path))
    (work / "charter_entity_layout.h").write_text(header(layout))
    ts = tables(layout)
    ok = True
    for precision, seeded in (("float", 0), ("float", 1), ("float", 2), ("bf16", 0)):
        lib = build(puffer, work, seeded, precision)
        res = run(lib, ts, layout["base_size"], np.random.default_rng(seeded + 7), precision)
        worst = max([res["forward"]] + res["grads"])
        passed = worst < TOL[precision] and res["cuda_error"] == "no error"
        expect = seeded == 0
        res.update(precision=precision, seeded_error=seeded, worst=worst, matches_reference=passed,
                   as_expected=passed == expect)
        print(json.dumps(res))
        ok &= passed == expect
    print("REFERENCE TEST", "PASSED" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
