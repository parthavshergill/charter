"""entity2's helpers on Modal, on the harness's image and volume (app charter-rl-entity2).

    cd rl && modal run entity/tools/modal_extra.py::games_main --subject entity2/x/ckpt/.../N.bin --out entity2/x/games
    cd rl && modal run entity/tools/modal_extra.py::meta_main --ckpt entity2/x/ckpt/.../N.bin --like entity2/x/ckpt/.../M.bin
    cd rl && modal run entity/tools/modal_extra.py::ls_main --run entity2/x
"""
import json
import os
import shlex
import sys

sys.path[:0] = [os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "/src/rl"]
import modal_app as m  # noqa: E402

app = m.app


@app.function(cpu=4, memory=8192, timeout=1800, volumes={m.VOL: m.vol})
def games(subject: str, out: str, opponents: str, games_list: str, n: int, first: int):
    m.vol.reload()
    texts = {}
    for opp in opponents.split(","):
        code, text = m.sh(f"cd {m.SRC}/.. && python3 rl/entity/tools/games.py {shlex.quote(subject)} --opponent {opp} "
                          f"--games-list {games_list} --n {n} --first {first} --out {out}")
        texts[opp] = text[-3000:]
    m.vol.commit()
    return texts


@app.function(cpu=1, memory=1024, timeout=300, volumes={m.VOL: m.vol})
def meta(ckpt: str, like: str, extra: str = ""):
    """Write ckpt's .json meta from another checkpoint's of the same run (or from `extra` alone, with like = "")."""
    m.vol.reload()
    d = json.load(open(like + ".json")) if like else {}
    d.update(json.loads(extra) if extra else {})
    d["name"] = ckpt[len(m.VOL) + 1:]
    json.dump(d, open(ckpt + ".json", "w"))
    m.vol.commit()
    return d


@app.function(cpu=1, memory=1024, timeout=300, volumes={m.VOL: m.vol})
def ls(run: str):
    m.vol.reload()
    out = sorted(os.path.join(dp, f) for dp, _, fs in os.walk(f"{m.VOL}/{run}") for f in fs)
    return out


@app.function(gpu=m.GPU, cpu=4, memory=16384, timeout=1800, volumes={m.VOL: m.vol})
def reftest(pointer_only: bool):
    """rl/entity/test_reference.py on a GPU: the CUDA encoder (and pointer decoder) against PyTorch."""
    m.sh("ln -sf /usr/lib/x86_64-linux-gnu/libnvidia-ml.so.1 /usr/lib/x86_64-linux-gnu/libnvidia-ml.so")
    m.sh("pip install -q torch --index-url https://download.pytorch.org/whl/cpu 2>&1 | tail -1")
    code, text = m.sh(f"cd {m.SRC}/entity && python3 test_reference.py {m.PUFFER} {m.SRC}/layout.json /tmp/reftest"
                      + (" --pointer" if pointer_only else ""))
    return {"exit": code, "tail": text[-5000:]}


@app.function(cpu=8, memory=16384, timeout=3600, volumes={m.VOL: m.vol})
def bc(args: str):
    """rl/entity/bc_entity.py with these arguments (paths on the volume)."""
    m.sh("pip install -q torch --index-url https://download.pytorch.org/whl/cpu 2>&1 | tail -1")
    code, text = m.sh(f"cd {m.SRC}/.. && python3 rl/entity/bc_entity.py {args}")
    m.vol.commit()
    return {"exit": code, "tail": text[-3000:]}


@app.local_entrypoint()
def bc_main(args: str):
    r = bc.remote(args)
    print(r["tail"])


@app.local_entrypoint()
def reftest_main(pointer_only: bool = False):
    r = reftest.remote(pointer_only)
    print(r["tail"])
    print("exit", r["exit"])


@app.local_entrypoint()
def games_main(subject: str, out: str, opponents: str = "hand,random",
               games_list: str = "island,not-catan,slime-parliament,pirate-republic", n: int = 1, first: int = 0):
    sub = subject if subject in ("random", "hand") or subject.startswith("/") else f"{m.VOL}/{subject}"
    r = games.remote(sub, f"{m.VOL}/{out}", opponents, games_list, n, first)
    for k, v in r.items():
        print(f"== {k}\n{v}")


@app.local_entrypoint()
def meta_main(ckpt: str, like: str = "", extra: str = ""):
    print(json.dumps(meta.remote(f"{m.VOL}/{ckpt}", f"{m.VOL}/{like}" if like else "", extra)))


@app.local_entrypoint()
def ls_main(run: str):
    print("\n".join(ls.remote(run)))
