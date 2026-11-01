# make install      builds the server and the headless runner, including the C parts of SQLite.
# make run          starts the server. PORT sets the port, 8787 by default.
# make smoke        plays full games through the HTTP API, on a free port, and checks the result.
# make clerk-check  checks the clerk and the Claude seats, against a stand-in for the API.
# make deploy-check checks budgets, pausing, waking and the copy to storage, against stand-ins. See docs/deploy.md.
# make audit        checks every theorem's axioms, replays the proofs through leanchecker, and scans for banned constructs.
# make measure      times the worst turn at the limits, or at others: make measure ARGS="--laws 32".
# make contact-sheet PACK=<id>  draws all of a pack's looks in one image, in contact-sheets/. See docs/process/reskins.md.
# make sim          plays complete games with no browser. See below.
# make spectate     opens a finished run in the browser, as a spectator.
#
# make sim GAMES=1 SEATS=4 [GAME=island|not-catan|...] [SEED=n] [PERSONAS=trader,schemer,...] [KINDS=claude,bot]
#          [MAX_MINUTES=360] [RESUME=results/<run>] [STOP_ROUND=n] [BRIEFS=path.json] [OUT=results]
# STOP_ROUND stops a game when that round has ended. BRIEFS gives each seat a name, a voice and a private
# goal: see Persona.parseBriefs. PERSONAS=griefer asks for the griefer, which is never chosen otherwise.
# It needs an API key for Claude seats: ANTHROPIC_API_KEY, or CHARTER_ENV_FILE naming a file with it.
# Results go to results/<run>/, which git ignores.
#
# make spectate RESULTS=results/<run> [SPECTATE_PORT=8788]
#
# The server reads: CHARTER_TURN_MS (a person's turn, 5 minutes), CHARTER_CLAUDE_TURN_MS (a Claude seat's
# turn, 10 minutes, 25 in make sim), CHARTER_VOTE_HOLD_MS (how long other seats wait for a person's vote,
# 30 seconds), CHARTER_TABLE_AWAY_MS (a table pauses with none of its people there, 3 minutes), CHARTER_SEAT_MODEL,
# CHARTER_SEAT_EFFORT, CHARTER_SEAT_CONCURRENCY, CHARTER_DESCRIBE_MODEL, CHARTER_DESCRIBE_EFFORT. 0 turns a limit off. CHARTER_BIND sets the address to listen on,
# 127.0.0.1 by default. docs/deploy.md lists the budgets.
PORT ?= 8787
SPECTATE_PORT ?= 8788
GAMES ?= 1
SEATS ?= 4
GAME ?= island
KINDS ?= claude
MAX_MINUTES ?= 360

.PHONY: install run smoke clerk-check deploy-check audit measure sim spectate contact-sheet

install:
	@command -v lake >/dev/null || { echo "lake not found: install elan from https://github.com/leanprover/elan"; exit 1; }
	lake build charter-server charter-sim

run:
	PORT=$(PORT) .lake/build/bin/charter-server

smoke: install
	python3 scripts/smoke.py

clerk-check: install
	python3 scripts/clerk_check.py
	python3 scripts/seat_check.py

deploy-check: install
	python3 scripts/deploy_check.py

measure:
	lake build charter-measure
	.lake/build/bin/charter-measure $(ARGS)

sim: install
	.lake/build/bin/charter-sim --games $(GAMES) --seats $(SEATS) --game $(GAME) --kinds $(KINDS) --max-minutes $(MAX_MINUTES) \
	  $(if $(SEED),--seed $(SEED)) $(if $(PERSONAS),--personas $(PERSONAS)) $(if $(RESUME),--resume $(RESUME)) \
	  $(if $(STOP_ROUND),--stop-round $(STOP_ROUND)) $(if $(BRIEFS),--briefs $(BRIEFS)) $(if $(OUT),--out $(OUT))

spectate: install
	@test -n "$(RESULTS)" || { echo "say which run: make spectate RESULTS=results/<run>"; exit 1; }
	@for f in $(RESULTS)/*.db; do c=$$(basename $$f .db); echo "http://127.0.0.1:$(SPECTATE_PORT)/?game=$$c&replay=1"; done
	PORT=$(SPECTATE_PORT) CHARTER_DATA=$(RESULTS) CHARTER_SHOW_ONLY=1 .lake/build/bin/charter-server

contact-sheet:
	@test -n "$(PACK)" || { echo "say which pack: make contact-sheet PACK=<id>"; exit 1; }
	lake build charter-contact
	python3 scripts/contact_sheet.py $(PACK)

audit:
	bash scripts/audit.sh
