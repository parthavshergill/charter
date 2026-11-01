#!/bin/bash
# The statement lock. It records hashes of the files that state the constitution and define its words.
#
# bash scripts/statement_lock.sh check    fails if any of those files changed. `make audit` runs this.
# bash scripts/statement_lock.sh update   records the current files. Run this only when the owner has
#                                         approved a change to the statements.
set -euo pipefail
cd "$(dirname "$0")/.."
lock=scripts/statement_lock.sha256
files() {
  ls Charter/Constitution.lean Charter/Constitution/Promises.lean Charter/Constitution/Supporting.lean \
    Charter/Words.lean Charter/Words/*.lean | sort
}
case "${1:-check}" in
  update) files | xargs shasum -a 256 > "$lock"; echo "Recorded $(wc -l < "$lock" | tr -d ' ') files." ;;
  check)
    if ! diff <(files) <(cut -c67- "$lock") > /dev/null; then
      echo "The statement lock lists different files. The owner must approve this change."; exit 1
    fi
    if ! shasum -a 256 -c --quiet "$lock"; then
      echo "A locked file changed. The owner must approve this change."; exit 1
    fi
    echo "All $(wc -l < "$lock" | tr -d ' ') locked files match." ;;
  *) echo "usage: statement_lock.sh check|update"; exit 2 ;;
esac
