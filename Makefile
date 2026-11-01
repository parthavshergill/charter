# make install      builds the server, including the C parts of SQLite.
# make run          starts the server. PORT sets the port, 8787 by default.
# make audit        checks every theorem's axioms, replays the proofs through leanchecker, and scans for banned constructs.
#
# The server reads: CHARTER_TURN_MS (a person's turn, 5 minutes), CHARTER_CLAUDE_TURN_MS (a Claude seat's
# turn, 10 minutes), CHARTER_VOTE_HOLD_MS (how long other seats wait for a person's vote,
# 30 seconds), CHARTER_SEAT_MODEL, CHARTER_SEAT_EFFORT, CHARTER_SEAT_CONCURRENCY. 0 turns a limit off.
PORT ?= 8787

.PHONY: install run audit

install:
	@command -v lake >/dev/null || { echo "lake not found: install elan from https://github.com/leanprover/elan"; exit 1; }
	lake build charter-server

run:
	PORT=$(PORT) .lake/build/bin/charter-server

audit:
	bash scripts/audit.sh
