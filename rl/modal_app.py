"""Train, evaluate and test the Charter policy on Modal.

    modal run rl/modal_app.py --action test
    modal run rl/modal_app.py --action train --run flat-1 --minutes 20 --max-dollars 1 [--train-args "..."]
    modal run rl/modal_app.py --action eval --run flat-1 [--games 200]
    modal run rl/modal_app.py --action train --run entity-1 --encoder entity [--meta-extra '{"entity_dim": 32}']

`--encoder NAME` compiles in a custom encoder from rl/arch/NAME/ (or rl/NAME/); see `build_puffer`. The checkpoint's
meta then says `"format": "puffer-NAME"`, and rl/reference/policy.py loads it through `arch.NAME.policy` (or
`NAME.policy`). `--meta-extra` adds fields to the meta.

Needs only MODAL_TOKEN_ID and MODAL_TOKEN_SECRET. Behind an HTTPS proxy, install `modal[api-proxy-support]` and set
SSL_CERT_FILE to the proxy's CA bundle.

Names: the app is `charter-rl-<CHARTER_RL_NAME>` (default `builder`), and each run writes only to `/vol/<run>/` on
the volume `charter-rl`.

Money: every job has a timeout, and the timeout is cut so that its price at Modal's list rates stays under
`--max-dollars`. Before each job, today's spend of this app's name (from `modal billing report`) plus that most is
checked against `CHARTER_RL_BUDGET` dollars (default 10), and the job is refused if it would go over.
"""
import json
import os
import shlex
import subprocess
import sys
import time

import modal

NAME = os.environ.get("CHARTER_RL_NAME", "builder")
APP = f"charter-rl-{NAME}"
BUDGET = float(os.environ.get("CHARTER_RL_BUDGET", "10"))
PUFFER_COMMIT = "ea7f989371270d2948f96728bda8aec5e7634a4c"
LEAN = "/opt/lean-4.35.0-linux"
PUFFER = "/opt/pufferlib"
REPO = "/repo"      # the Lean sources and the built library, baked into the image
SRC = "/src/rl"     # the rest of rl/, added at start, so a Python change does not rebuild Lean
VOL = "/vol"
GPU = "T4"
CUDA = "12-9"
CUDA_REPO = "https://developer.download.nvidia.com/compute/cuda/repos/debian12/x86_64"

# Modal list prices, dollars per second. Kept high on purpose: they bound spend, they do not predict it.
PRICE = {"T4": 0.000164, "cpu": 0.0000131, "gib": 0.00000222}

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
IGNORE = ["**/.lake/**", "**/__pycache__/**", "**/build/**", "**/node_modules/**", "**/.git/**"]

image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("build-essential", "clang", "ccache", "git", "curl", "unzip", "gnupg", "libomp-dev",
                 "libgl1-mesa-dev", "ca-certificates", "time", "zstd", "binutils", "libgl1")
    .run_commands(
        # NVIDIA's signed repository, through its keyring package.
        f"curl -fsSL {CUDA_REPO}/cuda-keyring_1.1-1_all.deb -o /tmp/k.deb && dpkg -i /tmp/k.deb && rm /tmp/k.deb",
        "apt-get update -q",
        "DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends "
        f"cuda-nvcc-{CUDA} cuda-libraries-dev-{CUDA} cuda-nvml-dev-{CUDA} cuda-nvtx-{CUDA} libnccl2 libnccl-dev",
        "ln -sf /usr/lib/x86_64-linux-gnu/libomp.so.5 /usr/lib/x86_64-linux-gnu/libomp5.so",
        "curl -fsSL https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst"
        " | tar --zstd -xf - -C /opt",
        f"git clone -q https://github.com/PufferAI/PufferLib.git {PUFFER} && cd {PUFFER} && git checkout -q {PUFFER_COMMIT}",
        f"cd {PUFFER} && curl -fsSL https://github.com/raysan5/raylib/releases/download/5.5/"
        "raylib-5.5_linux_amd64.tar.gz | tar xz",
    )
    .pip_install("numpy==2.2.6")
    .env({"PATH": f"{LEAN}/bin:/usr/local/cuda/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin",
          "CUDA_HOME": "/usr/local/cuda", "CHARTER_RL_LIB": f"{REPO}/rl/build/libcharter_rl.so",
          "CHARTER_RL_LOGS": f"{REPO}/.lake/build/bin/charter-rl-logs"})
)
for part in ["Charter", "Server", "Evolved", "packages", "forks", "rl/lean", "rl/env"]:
    image = image.add_local_dir(os.path.join(ROOT, part), f"{REPO}/{part}", copy=True, ignore=IGNORE)
for part in ["Charter.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
    image = image.add_local_file(os.path.join(ROOT, part), f"{REPO}/{part}", copy=True)
image = image.run_commands(
    f"cd {REPO} && lake build CharterRL.Capi charter-rl-check charter-rl-logs 2>&1 | tail -3",
    f"cd {REPO} && rl/env/build.sh 2>&1 | tail -2",
).add_local_dir(HERE, SRC, ignore=IGNORE + ["lean/**"])

app = modal.App(APP, image=image)
vol = modal.Volume.from_name("charter-rl", create_if_missing=True)


def sh(cmd, timeout=None, cwd=None, env=None):
    """Run a shell command, stream its output, and return (exit code, output)."""
    print(f"$ {cmd}", flush=True)
    p = subprocess.Popen(cmd, shell=True, cwd=cwd, env=dict(os.environ, **(env or {})),
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, errors="replace")
    out = []
    start = time.time()
    try:
        for line in p.stdout:
            out.append(line)
            print(line, end="", flush=True)
            if timeout and time.time() - start > timeout:
                p.kill()
                out.append("[killed: timeout]\n")
                break
        code = p.wait()
    except Exception as e:  # noqa: BLE001
        p.kill()
        code = f"error {e}"
    return code, "".join(out)


def encoder_dir(name):
    """Where a custom encoder lives: rl/arch/<name>/, or rl/<name>/."""
    for d in (f"{SRC}/arch/{name}", f"{SRC}/{name}"):
        if os.path.isdir(d):
            return d
    raise SystemExit(f"no encoder {name}: expected rl/arch/{name}/ or rl/{name}/")


def build_puffer(move_rows=False, out="puffer", patch=True, encoder="flat"):
    """Build PufferLib's trainer with the Charter env compiled in, and rl/puffer/patches applied unless patch is False.

    A custom encoder (`encoder` other than `flat`) lives in rl/arch/<name>/ (or rl/<name>/) and brings:
    - `patches/*.patch`, optional: applied after rl/puffer/patches, only for this encoder (the src/ocean.cu hook);
    - `puffer_build.sh`, run as `bash puffer_build.sh PUFFER_DIR OCEAN_DIR LAYOUT_JSON`, which copies its files into
      OCEAN_DIR (ocean/charter/) and prints the extra nvcc flags (for example `-DPUFFER_CHARTER_ENTITY`) on its last
      line of output."""
    d = f"{PUFFER}/ocean/charter"
    os.makedirs(d, exist_ok=True)
    sh(f"cp {SRC}/puffer/charter.h {d}/charter.h && cp {REPO}/rl/env/charter_rl.h {d}/charter_rl.h && "
       f"cp {SRC}/puffer/charter.ini {PUFFER}/config/charter.ini && "
       + (f"cd {PUFFER} && git checkout -q -- src && git apply {SRC}/puffer/patches/*.patch && git diff --stat" if patch
          else f"cd {PUFFER} && git checkout -q -- src"))
    lib = f"{REPO}/rl/build"
    extra = f"-L{lib} -lcharter_rl -Xlinker=-rpath -Xlinker={lib}" + (" -DCHARTER_MOVE_ROWS" if move_rows else "")
    if encoder != "flat":
        e = encoder_dir(encoder)
        if os.path.isdir(f"{e}/patches"):
            code, text = sh(f"cd {PUFFER} && git apply {e}/patches/*.patch && git diff --stat")
            if code != 0:
                return code, text
        code, text = sh(f"bash {e}/puffer_build.sh {PUFFER} {d} {SRC}/layout.json")
        if code != 0:
            return code, text
        extra += f" -I{d} " + (text.strip().splitlines() or [""])[-1]
    code, text = sh(f"cd {PUFFER} && NVCC_EXTRA={shlex.quote(extra)} ./build.sh charter {out} 2>&1 | tail -20 && test -x {out}",
                    env={"CCACHE_DIR": f"{VOL}/ccache"})
    return code, text


@app.function(cpu=4, memory=8192, timeout=1500, volumes={VOL: vol})
def test(quick: bool = False):
    """The environment's checks, the PufferLib env on the CPU, a trainer build, and a short eval."""
    results = {}
    t = time.time()
    code, text = sh(f"{REPO}/.lake/build/bin/charter-rl-check {'--quick' if quick else ''}", cwd=REPO, timeout=900)
    results["check"] = {"exit": code, "seconds": round(time.time() - t), "lines": [
        l for l in text.splitlines() if l.startswith(("PASS", "FAIL", "SPEED", "ALL", "1 F", "2 F"))]}
    t = time.time()
    code, text = sh(f"cd {SRC}/.. && cc -O2 -I rl/puffer -I {REPO}/rl/env -I {PUFFER}/src "
                    f"-I {PUFFER}/raylib-5.5_linux_amd64/include rl/puffer/test_env.c -L {REPO}/rl/build -lcharter_rl "
                    f"-Wl,-rpath,{REPO}/rl/build -o /tmp/test_env && /tmp/test_env 3")
    results["puffer_env_cpu"] = {"exit": code, "seconds": round(time.time() - t), "lines": text.strip().splitlines()[-6:]}
    t = time.time()
    code, text = build_puffer()
    results["puffer_build"] = {"exit": code, "seconds": round(time.time() - t), "tail": text.strip().splitlines()[-3:]}
    vol.commit()
    return results


@app.function(gpu=GPU, cpu=8, memory=16384, timeout=4 * 3600, volumes={VOL: vol})
def train(run: str, train_args: str = "", seconds: int = 600, move_rows: bool = False, patch: bool = True,
          encoder: str = "flat", meta_extra: str = ""):
    """Build the trainer and train for at most `seconds`. Writes /vol/<run>/: train.log, ckpt/, meta.json."""
    out = f"{VOL}/{run}"
    os.makedirs(out, exist_ok=True)
    t0 = time.time()
    sh("ln -sf /usr/lib/x86_64-linux-gnu/libnvidia-ml.so.1 /usr/lib/x86_64-linux-gnu/libnvidia-ml.so; "
       "nvidia-smi --query-gpu=name,driver_version --format=csv,noheader")
    code, text = build_puffer(move_rows, patch=patch, encoder=encoder)
    if code != 0:
        return {"build": code, "tail": text[-2000:]}
    build_s = time.time() - t0
    args = (f"train --headless --base.checkpoint_dir={out}/ckpt --base.log_dir={out}/logs "
            + (" --env.move_rows=1" if move_rows else "") + f" {train_args}")
    t1 = time.time()
    code, _ = sh(f"cd {PUFFER} && timeout --kill-after=20 {seconds} ./puffer {args} 2>&1 | tr '\\r' '\\n' | "
                 f"sed 's/\\x1b\\[[0-9;?]*[A-Za-z]//g' > {out}/train.log; echo exit ${{PIPESTATUS[0]}}")
    train_s = time.time() - t1
    _, tail = sh(f"grep -E 'bot_eval|ssert|Abort|rror|missing' {out}/train.log | head -20; tail -40 {out}/train.log")
    ckpts = sorted(os.path.join(dp, f) for dp, _, fs in os.walk(f"{out}/ckpt") for f in fs if f.endswith(".bin"))
    hidden, layers = 128, 1
    for tok in train_args.split():
        if tok.startswith("--policy.hidden_size="):
            hidden = int(tok.split("=")[1])
        if tok.startswith("--policy.num_layers="):
            layers = int(tok.split("=")[1])
    obs = 7122 if move_rows else 4434
    for c in ckpts[-1:] + ckpts[:1]:
        meta = {"name": f"{run}/{os.path.basename(c)}", "format": f"puffer-{encoder}", "encoder": encoder,
                "obs_size": obs, "act_size": 696, "hidden": hidden, "layers": layers,
                "settings": {"vote_mode": "bot", "move_rows": move_rows}}
        meta.update(json.loads(meta_extra) if meta_extra else {})
        json.dump(meta, open(c + ".json", "w"))
    vol.commit()
    return {"build_seconds": round(build_s), "train_seconds": round(train_s), "checkpoints": len(ckpts),
            "first": ckpts[0] if ckpts else None, "last": ckpts[-1] if ckpts else None, "tail": tail[-6000:]}


@app.function(cpu=8, memory=8192, timeout=3 * 3600, volumes={VOL: vol})
def evaluate(subjects: list, out: str, games: int = 200, quick: bool = False, opponents: str = "", logs: int = 2):
    """Run rl/eval on these subjects (`random`, `hand`, `champion`, or policy paths on the volume) and save the report,
    with `logs` saved games per table in `out/games/`."""
    vol.reload()
    opp = f"--opponents {shlex.quote(opponents)}" if opponents else ""
    code, text = sh(f"cd {SRC}/.. && python3 rl/eval/eval.py {' '.join(map(shlex.quote, subjects))} --games {games} "
                    f"--jobs 8 --out {out} {'--quick' if quick else ''} {opp} --logs {logs}")
    vol.commit()
    return {"exit": code, "report": open(f"{out}/report.md").read() if os.path.exists(f"{out}/report.md") else text[-4000:]}


# ---- Money -------------------------------------------------------------------------------------------------

def spent_today():
    """Today's cost of every app named like this one, from `modal billing report`."""
    try:
        r = subprocess.run(["modal", "billing", "report", "--for", "today", "--json"], capture_output=True,
                           text=True, timeout=120)
        rows = json.loads(r.stdout)
        return sum(float(x["cost"]) for x in rows if x.get("description") == APP)
    except Exception as e:  # noqa: BLE001
        print(f"could not read the billing report ({e}); counting today's spend as the whole budget")
        return BUDGET


def price_per_second(gpu, cpu, gib):
    return (PRICE[gpu] if gpu else 0) + cpu * PRICE["cpu"] + gib * PRICE["gib"]


def guard(max_dollars, gpu, cpu, gib, want_seconds):
    """The seconds a job may run so that it costs at most max_dollars, or exit if the budget cannot cover it."""
    rate = price_per_second(gpu, cpu, gib)
    seconds = int(min(want_seconds, max_dollars / rate))
    spent = spent_today()
    worst = seconds * rate
    print(f"[money] {APP}: spent today ${spent:.2f}, this job at most ${worst:.2f} ({seconds} s), budget ${BUDGET:.2f}")
    if spent + worst > BUDGET:
        sys.exit(f"[money] refused: ${spent:.2f} + ${worst:.2f} would pass the budget of ${BUDGET:.2f}")
    return seconds


@app.local_entrypoint()
def main(action: str = "test", run: str = "smoke", minutes: float = 10, max_dollars: float = 1.0,
         train_args: str = "", games: int = 200, subjects: str = "", quick: bool = False, move_rows: bool = False,
         no_patch: bool = False, encoder: str = "flat", meta_extra: str = "", opponents: str = "", logs: int = 2,
         eval_name: str = "eval"):
    if action == "test":
        total = guard(max_dollars, None, 4, 8, 1500)
        print(json.dumps(test.with_options(timeout=total).remote(quick), indent=1))
    elif action == "train":
        # The whole job, build and start included, stops at `total`. Training gets all but 10 minutes of it.
        total = guard(max_dollars, GPU, 8, 16, int(minutes * 60) + 600)
        seconds = total - 600
        if seconds < 60:
            sys.exit("[money] too little money for a useful run")
        r = train.with_options(timeout=total).remote(run, train_args, seconds, move_rows, not no_patch, encoder,
                                                            meta_extra)
        print(json.dumps(r, indent=1))
    elif action == "eval":
        total = guard(max_dollars, None, 8, 8, 3 * 3600)
        evaluate_ = evaluate.with_options(timeout=total)
        subs = subjects.split(",") if subjects else ["random", "hand"]
        bots = ("random", "hand", "champion", "champion-closed")
        r = evaluate_.remote([s if s in bots or s.startswith("/") else f"{VOL}/{s}" for s in subs],
                            f"{VOL}/{run}/{eval_name}", games, quick, opponents, logs)
        print(r["report"])
    else:
        sys.exit(f"unknown action {action}")
