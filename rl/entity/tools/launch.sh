#!/usr/bin/env bash
# Start one detached training run on Modal: launch.sh RUN MINUTES MAX_DOLLARS ENTITY_DIM "TRAIN ARGS"
# The run writes /vol/entity2/RUN/ on the volume charter-rl; the local log goes to $LOGS/RUN.log.
set -euo pipefail
cd "$(dirname "$0")/../.."
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt} CHARTER_RL_NAME=entity2 CHARTER_RL_BUDGET=${CHARTER_RL_BUDGET:-25}
LOGS=${LOGS:-/tmp/entity2-logs}; mkdir -p "$LOGS"
nohup modal run --detach modal_app.py --action train --run "entity2/$1" --minutes "$2" --max-dollars "$3" \
  --encoder entity --meta-extra "{\"entity_dim\": $4}" --train-args "$5" > "$LOGS/$1.log" 2>&1 &
echo "started $1 (pid $!)"
