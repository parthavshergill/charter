#!/bin/bash
# The checks behind `make audit`. It needs no sandbox, so it runs on macOS.
#
# It does not run Comparator, which needs a Linux sandbox. To run Comparator, use scripts/comparator.sh.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Build =="
lake build Charter Server.RoundTrip Server.SecrecyExamples Server.SecrecyReach

echo
echo "== Axioms =="
lake env lean --run scripts/audit_axioms.lean

echo
echo "== Kernel replay (leanchecker) =="
modules=$(find Charter/Words Charter/Engine Charter/Proofs Charter/Constitution -name '*.lean' \
  | sed -e 's/\.lean$//' -e 's#/#.#g' | sort)
modules="Charter.Sha256 Charter.Words Charter.Engine Charter.Constitution Charter.Games.Tiny Charter.Games.Witnesses $modules"
modules="HexGrid HexGrid.Basic Charter.Games.HexMap Charter.Games.Island Charter.Games.IslandGame Charter.Games.IslandGameEvents $modules"
# The text of laws: the parser, the printer, what they can say, and the proof that they agree.
text_of_laws="Server/SExp.lean Server/Rules.lean Server/Readable.lean Server/RoundTrip.lean"
modules="$modules Server.SExp Server.Rules Server.Readable Server.RoundTrip"
# What a seat may know: the choke point, its promise and the examples.
secrecy="Server/Secrecy.lean Server/SecrecyProofs.lean Server/SecrecyPromise.lean Server/SecrecyExamples.lean Server/SecrecyReach.lean"
modules="$modules Server.Secrecy Server.SecrecyProofs Server.SecrecyPromise Server.SecrecyExamples Server.SecrecyReach"
lake env leanchecker $modules
echo "Replayed $(echo "$modules" | wc -w | tr -d ' ') modules through the kernel."

echo
echo "== Banned constructs =="
banned='\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|extern|partial def)\b|debug\.skipKernelTC|maxHeartbeats 0'
if grep -rnE "$banned" Charter Charter.lean $text_of_laws $secrecy; then
  echo "Found a banned construct."
  exit 1
fi
echo "None found in Charter, in $text_of_laws or in $secrecy."

echo
echo "== Statement lock =="
bash scripts/statement_lock.sh check

echo
echo "make audit passed. This does not run Comparator. For that, use scripts/comparator.sh."
