#!/bin/bash
# Check that the server's observation builder (Server/Policy/Obs.lean) writes the same numbers as the training
# harness's (rl/lean/CharterRL at 89a3a51, layout 2) on the same games: every world, 4 seats, up to 80 turn
# decisions, both driven by the same fixed rule. Usage: bash scripts/policy_obs_compare.sh [HARNESS_REV]
# It builds the harness in a separate worktree (../charter-harness), so it never runs two lake processes in one checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
REV=${1:-89a3a51}
WT=../charter-harness
OUT=.lake/policy-obs
mkdir -p $OUT
[ -d $WT ] || git worktree add --detach $WT $REV
git -C $WT checkout -q --detach $REV
cp scripts/policy_obs/HarnessDump.lean $WT/rl/lean/CharterRL/DumpObs.lean
(cd $WT && lake build CharterRL.Obs Server.PreviewCheck >/dev/null && lake env lean --run rl/lean/CharterRL/DumpObs.lean) > $OUT/harness.txt
lake build Server.Policy.Bot Server.PreviewCheck >/dev/null
lake env lean --run scripts/policy_obs/ServerDump.lean > $OUT/server.txt
python3 - "$OUT/harness.txt" "$OUT/server.txt" <<'PY'
import sys
from collections import Counter
tables = [("global", 0, 1, 21), ("seats", 21, 6, 10), ("resources", 81, 16, 27), ("kinds", 513, 16, 36),
          ("spots", 1089, 100, 45), ("laws", 5589, 48, 27), ("proposal", 6885, 1, 100), ("places", 6985, 128, 35)]
a = open(sys.argv[1]).read().split("\n")
b = open(sys.argv[2]).read().split("\n")
if len(a) != len(b):
    sys.exit("FAILED: %d decisions from the harness, %d from the server" % (len(a) - 1, len(b) - 1))
c = Counter()
for x, y in zip(a, b):
    xs, ys = x.split(), y.split()
    for j in range(2, len(xs)):
        if xs[j] != ys[j]:
            k = j - 2
            t = [t for t in tables if t[1] <= k < t[1] + t[2] * t[3]][0]
            c[(xs[0], t[0], (k - t[1]) % t[3])] += 1
print("decisions compared: %d" % (len(a) - 1))
for key, n in sorted(c.items()):
    print("differs: game %s, table %s, column %d, %d times" % (key + (n,)))
print("identical" if not c else "see above: a difference is a bug, unless the game itself changed since the harness revision")
PY
