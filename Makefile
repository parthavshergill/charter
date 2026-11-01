# make audit  checks every theorem's axioms, replays the proofs through leanchecker, and scans for banned constructs.

.PHONY: audit

audit:
	bash scripts/audit.sh
