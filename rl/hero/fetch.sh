#!/usr/bin/env bash
# Fetch every finished eval under /hero/<run>/ on volume charter-rl into DIR/<run>/<eval>/, then write the CSV.
# fetch.sh DIR
set -uo pipefail
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt}
DIR=$1; HERE=$(dirname "$0")
for RUN in ws-v2-champ v2-mix v2-fix; do
  for E in $(modal volume ls charter-rl "/hero/$RUN" 2>/dev/null | grep -o 'e[0-9]*$'); do
    mkdir -p "$DIR/$RUN/$E"
    [ -s "$DIR/$RUN/$E/report.json" ] && continue
    (cd "$DIR/$RUN/$E" && modal volume get --force charter-rl "/hero/$RUN/$E/report.json" report.json >/dev/null 2>&1 &&
      modal volume get --force charter-rl "/hero/$RUN/$E/report.md" report.md >/dev/null 2>&1) || rm -f "$DIR/$RUN/$E/report.json"
  done
done
python3 "$HERE/collect.py" "$DIR"/*/e* > "$HERE/data/eval.csv"
# run, steps, then eval's "can it play" sentence
for R in "$DIR"/*/e*/report.md; do
  E=$(dirname "$R"); echo "$(basename "$(dirname "$E")") $(basename "$E" | sed 's/^e0*//;s/^$/0/') $(grep -o 'PASS: [^.]*\|FAIL: [^.]*' "$R")"
done > "$HERE/data/can_play.txt"
wc -l "$HERE/data/eval.csv"
