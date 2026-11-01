"""Print the C file of every module that rl/lean/CharterRL/Capi.lean needs, outside Lean itself.

lake writes each module's C file under the .lake/build/ir of the package that owns it. Run after
`lake build CharterRL.Capi`."""
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# Where each package keeps its sources and its C files.
SOURCES = [(ROOT, ROOT), (os.path.join(ROOT, "rl", "lean"), ROOT)]
for pkg in glob.glob(os.path.join(ROOT, "packages", "*")) + glob.glob(os.path.join(ROOT, "forks", "*")):
    SOURCES.append((pkg, pkg))
CORE = ("Init", "Std", "Lean", "Lake")


def find(mod):
    rel = mod.replace(".", "/")
    for src, pkg in SOURCES:
        lean = os.path.join(src, rel + ".lean")
        if os.path.exists(lean):
            return lean, os.path.join(pkg, ".lake", "build", "ir", rel + ".c")
    raise SystemExit(f"no source for {mod}")


def main(root="CharterRL.Capi"):
    seen, todo, out = set(), [root], []
    while todo:
        mod = todo.pop()
        if mod in seen or mod.split(".")[0] in CORE:
            continue
        seen.add(mod)
        lean, c = find(mod)
        if not os.path.exists(c):
            raise SystemExit(f"{c} is missing: run lake build {root}")
        out.append(c)
        for line in open(lean, encoding="utf-8"):
            m = re.match(r"^\s*(?:public\s+)?import\s+(.+)", line)
            if m:
                todo.extend(m.group(1).split())
    print("\n".join(sorted(out)))


if __name__ == "__main__":
    main(*sys.argv[1:])
