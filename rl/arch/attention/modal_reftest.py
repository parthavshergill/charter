"""Run the attention encoder's reference test on a Modal T4, on the harness's image (rl/modal_app.py), with
observations from real games added to the random ones.

    cd rl && CHARTER_RL_NAME=attention CHARTER_RL_BUDGET=15 modal run arch/attention/modal_reftest.py [--bench 16384]

The app is the harness's `charter-rl-<CHARTER_RL_NAME>`, and the harness's money guard limits the job.
"""
import os
import sys

os.environ.setdefault("CHARTER_RL_NAME", "attention")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", ".."))
sys.path.insert(0, "/src/rl")   # inside the container
import modal  # noqa: E402

import modal_app as H  # noqa: E402

app = modal.App(H.APP, image=H.image)
MAX_SECONDS = 1200


@app.function(gpu=H.GPU, cpu=4, memory=8192, timeout=MAX_SECONDS)
def reftest(bench: int = 0) -> str:
    import importlib.util
    import subprocess

    import numpy as np
    H.sh("ln -sf /usr/lib/x86_64-linux-gnu/libnvidia-ml.so.1 /usr/lib/x86_64-linux-gnu/libnvidia-ml.so")
    H.sh("pip install -q torch==2.5.1 --index-url https://download.pytorch.org/whl/cpu 2>&1 | tail -1")
    # Real observations, sampled by the harness's own reference test.
    sys.path.insert(0, f"{H.SRC}/reference")
    sys.path.insert(0, f"{H.SRC}/env")
    spec = importlib.util.spec_from_file_location("harness_reftest", f"{H.SRC}/reference/reference_test.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    obs = mod.real_obs(64, seed=3).numpy()
    np.save("/tmp/real_obs.npy", obs)
    cmd = ["python3", f"{H.SRC}/arch/attention/reference_test.py", H.PUFFER, f"{H.SRC}/layout.json",
           "/tmp/build", "--obs", "/tmp/real_obs.npy"] + (["--bench", str(bench)] if bench else [])
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.stdout + ("\n--- stderr ---\n" + p.stderr[-4000:] if p.returncode else "") + f"\nexit {p.returncode}"


@app.local_entrypoint()
def main(bench: int = 0, max_dollars: float = 0.3):
    seconds = H.guard(max_dollars, H.GPU, 4, 8, MAX_SECONDS)
    out = reftest.with_options(timeout=seconds).remote(bench)
    print(out)
