#!/usr/bin/env bash
# Write a v2 meta for a checkpoint and run rl/eval --quick on it: quick_eval.sh CKPT LABEL STALE_WAIT TRAIN_ARGS
# MOVES=1 per-move rows, PRUNE=1 the two declaration switches, RESID=1 the encoder's residual block.
set -euo pipefail
cd "$(dirname "$0")/../.."
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt} CHARTER_RL_NAME=entity2 CHARTER_RL_BUDGET=${CHARTER_RL_BUDGET:-25}
CKPT=$1; LABEL=$2; STALE=$3; ARGS=$4
RUN=$(dirname "$(dirname "$(dirname "$(dirname "$CKPT")")")")
STEP=$(basename "$CKPT" .bin | sed 's/^0*//'); STEP=${STEP:-0}
META=$(python3 -c "import json,sys; d={'format':'puffer-entity','encoder':'entity','layout':2,'obs_size':11465,'act_size':516,'hidden':128,'layers':1,'entity_dim':32,'pointer':1,'stale_wait':int(sys.argv[1]),'steps':int(sys.argv[2]),'train_args':sys.argv[3],'commit':sys.argv[4],'settings':{'vote_mode':'bot','move_rows':False,'declare_always':True}}
moves=sys.argv[5]=='1'
if moves: d.update(moves=1, obs_size=15177); d['settings']['move_rows']=True
if sys.argv[6]=='1': d['settings'].update(prune_declares=True, declare_once_per_turn=True)
if sys.argv[7]=='1': d['resid']=1
print(json.dumps(d))" "$STALE" "$STEP" "$ARGS" "$(git rev-parse --short HEAD)" "${MOVES:-0}" "${PRUNE:-0}" "${RESID:-0}")
modal run entity/tools/modal_extra.py::meta_main --ckpt "$CKPT" --extra "$META" > /dev/null
modal run modal_app.py --action eval --run "$RUN" --eval-name "eval-$LABEL" --subjects "$CKPT" --games ${GAMES:-400} --quick --logs 2 --opponents ${OPPS:-table,hand} \
  --max-dollars 0.6 > "${LOGS:-/tmp}/eval-$(basename $RUN)-$LABEL.md" 2>&1
if [ "${SERVER:-1}" = 1 ]; then   # the server-like row: each world's own map, no laws proposed (PR #11)
  modal run modal_app.py --action eval --run "$RUN" --eval-name "eval-$LABEL-srv" --subjects "$CKPT" --games ${GAMES:-400} --quick --logs 2 \
    --opponents ${OPPS:-table,hand} --eval-args="--random-map 0 --laws off" --max-dollars 0.6 > "${LOGS:-/tmp}/eval-$(basename $RUN)-$LABEL-srv.md" 2>&1
fi
echo "done $RUN $LABEL"
