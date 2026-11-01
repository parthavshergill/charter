#!/usr/bin/env bash
# Write a v2 meta for a checkpoint and run rl/eval --quick on it: quick_eval.sh CKPT LABEL STALE_WAIT TRAIN_ARGS
set -euo pipefail
cd "$(dirname "$0")/../.."
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt} CHARTER_RL_NAME=entity2 CHARTER_RL_BUDGET=${CHARTER_RL_BUDGET:-25}
CKPT=$1; LABEL=$2; STALE=$3; ARGS=$4
RUN=$(dirname "$(dirname "$(dirname "$(dirname "$CKPT")")")")
STEP=$(basename "$CKPT" .bin | sed 's/^0*//')
META=$(python3 -c "import json,sys; print(json.dumps({'format':'puffer-entity','encoder':'entity','layout':2,'obs_size':11465,'act_size':516,'hidden':128,'layers':1,'entity_dim':32,'pointer':1,'stale_wait':int(sys.argv[1]),'steps':int(sys.argv[2]),'train_args':sys.argv[3],'commit':sys.argv[4],'settings':{'vote_mode':'bot','move_rows':False,'declare_always':True}}))" "$STALE" "$STEP" "$ARGS" "$(git rev-parse --short HEAD)")
modal run entity/tools/modal_extra.py::meta_main --ckpt "$CKPT" --extra "$META" > /dev/null
modal run modal_app.py --action eval --run "$RUN" --eval-name "eval-$LABEL" --subjects "$CKPT" --games ${GAMES:-400} --quick --logs 2 --opponents hand,random,champion,champion-closed \
  --max-dollars 0.6 > "${LOGS:-/tmp}/eval-$(basename $RUN)-$LABEL.md" 2>&1
echo "done $RUN $LABEL"
