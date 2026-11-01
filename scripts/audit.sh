#!/bin/bash
# The checks behind `make audit`. It needs no sandbox, so it runs on macOS.
#
# It does not run Comparator, which needs a Linux sandbox. To run Comparator, use scripts/comparator.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Build =="
lake build Charter

echo
echo "== Axioms =="
lake env lean --run scripts/audit_axioms.lean

echo
echo "== Kernel replay (leanchecker) =="
modules=$(find Charter/Words Charter/Engine Charter/Proofs Charter/Constitution -name '*.lean' \
  | sed -e 's/\.lean$//' -e 's#/#.#g' | sort)
modules="Charter.Sha256 Charter.Words Charter.Engine Charter.Constitution Charter.Games.Tiny Charter.Games.Witnesses $modules"
modules="HexGrid HexGrid.Basic Charter.Games.HexMap Charter.Games.Island Charter.Games.IslandGame Charter.Games.IslandGameEvents $modules"
lake env leanchecker $modules
echo "Replayed $(echo "$modules" | wc -w | tr -d ' ') modules through the kernel."

echo
echo "== Banned constructs =="
banned='\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|extern|partial def)\b|debug\.skipKernelTC|maxHeartbeats 0'
if grep -rnE "$banned" Charter Charter.lean; then
  echo "Found a banned construct."
  exit 1
fi
echo "None found in Charter."

echo
echo "== Statement lock =="
bash scripts/statement_lock.sh check

echo
echo "make audit passed. This does not run Comparator. For that, use scripts/comparator.sh."
