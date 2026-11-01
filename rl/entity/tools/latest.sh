#!/usr/bin/env bash
# Print the newest checkpoint of a run on the volume (no /vol prefix), and its step: latest.sh entity2/RUN
export SSL_CERT_FILE=${SSL_CERT_FILE:-/root/.ccr/ca-bundle.crt}
for d in $(modal volume ls charter-rl "/$1/ckpt/charter/" 2>/dev/null); do modal volume ls charter-rl "/$d" 2>/dev/null; done \
  | grep '\.bin$' | sort | tail -1 | awk -F/ '{s=$NF; sub(/\.bin$/,"",s); print $0, s+0}'
