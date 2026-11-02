#!/usr/bin/env bash
# Copy checkpoints into /vol/hero/ckpt/<run>/<step>.bin on volume charter-rl, each with a meta copied from the run's
# own meta (steps set), so eval reads them without touching the training agents' folders.
# stage.sh RUN_DIR STALE_WAIT TRAIN_ARGS STEP...   (RUN_DIR like entity2/ws-v2-champ/ckpt/charter/1793571670459)
set -euo pipefail
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt}
SRC=$1; STALE=$2; ARGS=$3; shift 3
RUN=$(echo "$SRC" | cut -d/ -f2)
TMP=$(mktemp -d)
for STEP in "$@"; do
  F=$(printf "%016d" "$STEP")
  modal volume cp charter-rl "/$SRC/$F.bin" "/hero/ckpt/$RUN/$F.bin" 2>/dev/null || true
  python3 -c "import json,sys; print(json.dumps({'format':'puffer-entity','encoder':'entity','layout':2,'obs_size':11465,'act_size':516,'hidden':128,'layers':1,'entity_dim':32,'pointer':1,'stale_wait':int(sys.argv[1]),'steps':int(sys.argv[2]),'train_args':sys.argv[3],'source':sys.argv[4],'settings':{'vote_mode':'bot','move_rows':False,'declare_always':True,'stale_wait':bool(int(sys.argv[1]))}}))" "$STALE" "$STEP" "$ARGS" "/$SRC/$F.bin" > "$TMP/$F.bin.json"
  modal volume put -f charter-rl "$TMP/$F.bin.json" "/hero/ckpt/$RUN/$F.bin.json" >/dev/null
  echo "staged $RUN $STEP"
done
