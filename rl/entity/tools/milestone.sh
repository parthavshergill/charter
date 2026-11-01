#!/usr/bin/env bash
# Evaluate one checkpoint as a milestone: write its meta, run rl/eval on it, and save game logs to read.
#   milestone.sh CKPT(on the volume, no /vol) LABEL META_JSON [GAMES]
# META_JSON must hold hidden, entity_dim, pointer, train_args and commit; the rest is filled in here.
set -euo pipefail
cd "$(dirname "$0")/../.."
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt} CHARTER_RL_NAME=entity2 CHARTER_RL_BUDGET=${CHARTER_RL_BUDGET:-25}
CKPT=$1; LABEL=$2; EXTRA=$3; GAMES=${4:-200}
RUN=$(dirname "$(dirname "$(dirname "$CKPT")")")   # entity2/<run>
META=$(python3 -c "import json,sys; d={'format':'puffer-entity','encoder':'entity','obs_size':4434,'act_size':696,'layers':1,'settings':{'vote_mode':'bot','move_rows':False}}; d.update(json.loads(sys.argv[1])); print(json.dumps(d))" "$EXTRA")
modal run entity/tools/modal_extra.py::meta_main --ckpt "$CKPT" --extra "$META" | tail -1
modal run modal_app.py --action eval --run "$RUN/$LABEL" --subjects "$CKPT" --games "$GAMES" --quick --max-dollars 0.6 > "${LOGS:-/tmp}/eval-$(echo $RUN | tr / -)-$LABEL.md" 2>&1 &
modal run entity/tools/modal_extra.py::games_main --subject "$CKPT" --out "$RUN/$LABEL/games" --opponents hand,random \
  --games-list island,not-catan,slime-parliament,pirate-republic,ai-bubble,strike-the-earth --n 1 > "${LOGS:-/tmp}/games-$(echo $RUN | tr / -)-$LABEL.log" 2>&1 &
wait
echo "eval: ${LOGS:-/tmp}/eval-$(echo $RUN | tr / -)-$LABEL.md"
