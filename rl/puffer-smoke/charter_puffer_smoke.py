"""Smoke test: does PufferLib build and train on a Modal GPU?

Run with MODAL_PROFILE=charter. Everything lives in the app named
charter-puffer-smoke and the volume of the same name. No secrets are attached.
Every function has a hard timeout, and `modal run` stops the app on exit.
"""

import os
import shlex
import subprocess
import time

import modal

PUFFER_COMMIT = "ea7f989371270d2948f96728bda8aec5e7634a4c"
CUDA = "12-9"
GPU = "T4"
REPO = "/opt/pufferlib"
VOL = "/vol"

CUDA_REPO = "https://developer.download.nvidia.com/compute/cuda/repos/debian12/x86_64"

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install(
        "build-essential", "clang", "ccache", "git", "curl", "unzip", "gnupg",
        "libomp-dev", "libgl1-mesa-dev", "ca-certificates", "time",
    )
    .run_commands(
        f"curl -fsSL {CUDA_REPO}/Packages.gz -o /tmp/p.gz && rm /tmp/p.gz",
        f"echo 'deb [trusted=yes] {CUDA_REPO}/ /' > /etc/apt/sources.list.d/cuda.list",
        "apt-get update -q",
        "DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends "
        f"cuda-nvcc-{CUDA} cuda-libraries-dev-{CUDA} cuda-nvml-dev-{CUDA} "
        "libnccl2 libnccl-dev",
        # build.sh links -lomp5. Debian ships it as libomp.so.5.
        "ln -sf /usr/lib/x86_64-linux-gnu/libomp.so.5 /usr/lib/x86_64-linux-gnu/libomp5.so",
        f"git clone https://github.com/PufferAI/PufferLib.git {REPO}",
        f"cd {REPO} && git checkout -q {PUFFER_COMMIT}",
    )
    .env({"PATH": "/usr/local/cuda/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"})
)

LEAN = "/opt/lean-4.35.0-linux"
lean_image = image.apt_install("zstd", "binutils", "libgl1").run_commands(
    "curl -fsSL https://github.com/leanprover/lean4/releases/download/v4.35.0/"
    "lean-4.35.0-linux.tar.zst | tar --zstd -xf - -C /opt",
    f"{LEAN}/bin/lean --version",
)

LEAN = "/opt/lean-4.35.0-linux"
lean_image = image.apt_install("zstd", "binutils", "libgl1").run_commands(
    "curl -fsSL https://github.com/leanprover/lean4/releases/download/v4.35.0/"
    "lean-4.35.0-linux.tar.zst | tar --zstd -xf - -C /opt",
    f"{LEAN}/bin/lean --version",
)

app = modal.App("charter-puffer-smoke", image=image)
vol = modal.Volume.from_name("charter-puffer-smoke", create_if_missing=True)


def sh(cmd, timeout=None, cwd=REPO, env=None):
    """Run a command, stream its output, and return its exit code."""
    print(f"$ {cmd}", flush=True)
    merged = dict(os.environ, **(env or {}))
    start = time.time()
    p = subprocess.Popen(cmd, shell=True, cwd=cwd, env=merged)
    try:
        code = p.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        subprocess.run(["pkill", "-TERM", "-f", "puffer"], check=False)
        time.sleep(5)
        p.kill()
        code = "timeout"
    print(f"[exit {code} after {time.time() - start:.0f}s]", flush=True)
    return code


@app.function(gpu=GPU, cpu=2, memory=4096, timeout=600)
def probe():
    sh("nvidia-smi; nvcc --version; g++ --version | head -1; lscpu | grep -E 'Model name|^CPU\\(s\\)'; "
       "ls -la /usr/lib/x86_64-linux-gnu/libomp* ; ls /usr/local/cuda/lib64 | grep -E 'nvidia-ml|cublas.so$'; "
       "ls /usr/lib/x86_64-linux-gnu | grep -E 'nccl|nvidia-ml'; "
       f"cd {REPO} && git log -1 --format=%H")


@app.function(gpu=GPU, cpu=4, memory=16384, timeout=2400, volumes={VOL: vol})
def run(env_name, train_args="", train_seconds=240, build_flags="", tag="run",
        post="", post_seconds=300):
    """Build one env, train it for a bounded time, and save logs and weights."""
    t0 = time.time()
    build_env = {"CCACHE_DIR": f"{VOL}/ccache", "CUDA_HOME": "/usr/local/cuda"}
    out = f"{VOL}/{tag}"
    os.makedirs(out, exist_ok=True)
    code = sh(f"./build.sh {shlex.quote(env_name)} {build_flags} 2>&1 | tail -40; "
              "test -x ./puffer", timeout=1500, env=build_env)
    print(f"BUILD exit={code} seconds={time.time() - t0:.0f}", flush=True)
    if code != 0:
        vol.commit()
        return {"build": code}
    args = (f"train --base.checkpoint_dir={out}/ckpt --base.log_dir={out}/logs "
            f"{train_args}")
    t1 = time.time()
    code = sh(f"timeout --kill-after=10 {train_seconds} ./puffer {args} 2>&1 | "
              f"tr '\\r' '\\n' | tee {out}/train.log | awk 'NR%200==1'",
              timeout=train_seconds + 30)
    print(f"TRAIN exit={code} seconds={time.time() - t1:.0f}", flush=True)
    sh(f"tail -30 {out}/train.log; ls -la {out}/ckpt/* | tail -5; du -sh {out}/ckpt; "
       "nvidia-smi --query-gpu=name,utilization.gpu,memory.used --format=csv")
    vol.commit()
    if post:
        t2 = time.time()
        sh(f"export OUT={out}; {post}", timeout=post_seconds)
        print(f"POST seconds={time.time() - t2:.0f}", flush=True)
        vol.commit()
    return {"build": 0, "train": code, "total_seconds": time.time() - t0}


@app.function(image=lean_image, gpu=GPU, cpu=4, memory=16384, timeout=1800, volumes={VOL: vol})
def lean_test(files, script, seconds=1500):
    """Link a Lean-compiled game into a PufferLib env. Runs the script from the repo."""
    os.makedirs("/tmp/lean", exist_ok=True)
    for name, text in files.items():
        with open(f"/tmp/lean/{name}", "w") as f:
            f.write(text)
    sh("ln -sf /usr/lib/x86_64-linux-gnu/libnvidia-ml.so.1 /usr/lib/x86_64-linux-gnu/libnvidia-ml.so")
    os.makedirs(f"{VOL}/lean", exist_ok=True)
    with open("/tmp/lean/script.sh", "w") as f:
        f.write(script)
    code = sh("bash /tmp/lean/script.sh", timeout=seconds,
              env={"CCACHE_DIR": f"{VOL}/ccache", "CUDA_HOME": "/usr/local/cuda",
                   "LEAN": LEAN, "OUT": f"{VOL}/lean"})
    vol.commit()
    return code


@app.function(image=lean_image, cpu=4, memory=8192, timeout=900, volumes={VOL: vol})
def cpu_only(script, seconds=800):
    """No GPU here: run the --cpu player on weights trained earlier."""
    return sh(script, timeout=seconds, env={"CC": "clang"})


@app.function(image=lean_image, gpu=GPU, cpu=4, memory=16384, timeout=1800, volumes={VOL: vol})
def lean_test(files, script, seconds=1500):
    """Link a Lean-compiled game into a PufferLib env. Runs the script from the repo."""
    os.makedirs("/tmp/lean", exist_ok=True)
    for name, text in files.items():
        with open(f"/tmp/lean/{name}", "w") as f:
            f.write(text)
    sh("ln -sf /usr/lib/x86_64-linux-gnu/libnvidia-ml.so.1 /usr/lib/x86_64-linux-gnu/libnvidia-ml.so")
    os.makedirs(f"{VOL}/lean", exist_ok=True)
    with open("/tmp/lean/script.sh", "w") as f:
        f.write(script)
    code = sh("bash /tmp/lean/script.sh", timeout=seconds,
              env={"CCACHE_DIR": f"{VOL}/ccache", "CUDA_HOME": "/usr/local/cuda",
                   "LEAN": LEAN, "OUT": f"{VOL}/lean"})
    vol.commit()
    return code


@app.function(image=lean_image, cpu=4, memory=8192, timeout=900, volumes={VOL: vol})
def cpu_only(script, seconds=800):
    """No GPU here: run the --cpu player on weights trained earlier."""
    return sh(script, timeout=seconds, env={"CC": "clang"})


@app.local_entrypoint()
def main(action="probe", env_name="breakout", train_args="", train_seconds=240,
         build_flags="", tag="run", post_file="", post_seconds=300):
    post = open(post_file).read() if post_file else ""
    if action == "probe":
        probe.remote()
    elif action == "lean":
        names = ["SmokeGame.lean", "smoke_shim.c", "bench.c", "leantiny.h", "leantiny.ini"]
        files = {n: open(f"lean/{n}").read() for n in names}
        for n in ["policy_harness.c", "policy_reader.py"]:
            files[n] = open(n).read()
        for n in ["policy_harness.c", "policy_reader.py"]:
            files[n] = open(n).read()
        print(lean_test.remote(files, post, int(post_seconds)))
    elif action == "cpu":
        print(cpu_only.remote(post, int(post_seconds)))
    else:
        print(run.remote(env_name, train_args, int(train_seconds), build_flags, tag,
                         post, int(post_seconds)))
