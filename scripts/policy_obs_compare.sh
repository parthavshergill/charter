#!/bin/bash
# Check that the server's observation builder (Server/Policy/Obs.lean) writes the same numbers as the training
# harness's (rl/lean/CharterRL at 89a3a51, layout 2) on the same games: every world, 4 seats, up to 80 turn
# decisions, both driven by the same fixed rule. Usage: bash scripts/policy_obs_compare.sh [HARNESS_REV]
# MOVES=1 also builds and compares the table of moves (move_rows, with declare_always), as at 52ce36e.
# MASK=1 (harness 3b98ee8 or later) drives by every legal action, declarations and trades included, and compares
# the mask and the observation with prune_declares, declare_once_per_turn, the undo rule and the ranked moves table.
# It builds the harness in a separate worktree (../charter-harness), so it never runs two lake processes in one checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
REV=${1:-89a3a51}
WT=../charter-harness
OUT=.lake/policy-obs
mkdir -p $OUT
[ -d $WT ] || git worktree add --detach $WT $REV
git -C $WT checkout -q --detach $REV
if [ "${MASK:-0}" = 1 ]; then
  cp scripts/policy_obs/HarnessMaskDump.lean $WT/rl/lean/CharterRL/DumpObs.lean
  cp scripts/policy_obs/ServerMaskDump.lean $OUT/ServerDump.lean
elif [ "${MOVES:-0}" = 1 ]; then
  sed -e 's/{ moveRows := false, preview := true, slotOrder := .game }/{ moveRows := true, preview := true, slotOrder := .game, declareAlways := true }/' \
      -e 's/(template T ep G s.turnOrder.length false)/(template T ep G s.turnOrder.length true)/' \
      scripts/policy_obs/HarnessDump.lean > $WT/rl/lean/CharterRL/DumpObs.lean
  sed -e 's/decisionFor g s p$/decisionFor g s p true/' scripts/policy_obs/ServerDump.lean > $OUT/ServerDump.lean
else
  cp scripts/policy_obs/HarnessDump.lean $WT/rl/lean/CharterRL/DumpObs.lean
  cp scripts/policy_obs/ServerDump.lean $OUT/ServerDump.lean
fi
(cd $WT && lake build CharterRL.Obs Server.PreviewCheck >/dev/null && lake env lean --run rl/lean/CharterRL/DumpObs.lean) > $OUT/harness.txt
lake build Server.Policy.Bot Server.PreviewCheck >/dev/null
lake env lean --run $OUT/ServerDump.lean > $OUT/server.txt
python3 - "$OUT/harness.txt" "$OUT/server.txt" <<'PY'
import sys
from collections import Counter
tables = [("global", 0, 1, 21), ("seats", 21, 6, 10), ("resources", 81, 16, 27), ("kinds", 513, 16, 36),
          ("spots", 1089, 100, 45), ("laws", 5589, 48, 27), ("proposal", 6885, 1, 100), ("places", 6985, 128, 35),
          ("moves", 11465, 64, 58)]
a = open(sys.argv[1]).read().split("\n")
b = open(sys.argv[2]).read().split("\n")
# The server may have more worlds than the harness revision; compare the worlds both have.
games = {x.split()[0] for x in a if x.strip()}
b = [y for y in b if y.split()[:1] and y.split()[0] in games] + [""]
if len(a) != len(b):
    sys.exit("FAILED: %d decisions from the harness, %d from the server" % (len(a) - 1, len(b) - 1))
c = Counter()
masks = 0
for x, y in zip(a, b):
    xs, ys = x.split(), y.split()
    if len(xs) > 2 and xs[2] == "mask":
        masks += 1
        if xs != ys:
            sys.exit("FAILED: the mask differs at %s %s" % (xs[0], xs[1]))
        continue
    if len(xs) != len(ys):
        sys.exit("FAILED: observation sizes differ (%d against %d)" % (len(xs) - 2, len(ys) - 2))
    for j in range(2, len(xs)):
        if xs[j] != ys[j]:
            k = j - 2
            t = [t for t in tables if t[1] <= k < t[1] + t[2] * t[3]][0]
            c[(xs[0], t[0], (k - t[1]) % t[3])] += 1
print("decisions compared: %d" % ((len(a) - 1) // 2 if masks else len(a) - 1) + (", every mask identical" if masks else ""))
for key, n in sorted(c.items()):
    print("differs: game %s, table %s, column %d, %d times" % (key + (n,)))
print("identical" if not c else "see above: a difference is a bug, unless the game itself changed since the harness revision")
PY
