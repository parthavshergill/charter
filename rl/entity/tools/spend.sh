#!/usr/bin/env bash
# Total Modal spend of app charter-rl-entity2 since round 2 began (UTC dates), in dollars.
modal billing report --start "${1:-2026-11-01}" --json 2>/dev/null | python3 -c '
import json,sys; r=json.load(sys.stdin); print(round(sum(float(x["cost"]) for x in r if x.get("description")=="charter-rl-entity2"),3))'
