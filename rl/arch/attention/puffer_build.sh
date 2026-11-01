#!/usr/bin/env bash
# Build hook for rl/modal_app.py --encoder attention: bash puffer_build.sh PUFFER_DIR OCEAN_DIR LAYOUT_JSON
# Copies the encoder into OCEAN_DIR (PufferLib's ocean/charter/), after checking that attention_layout.h matches the
# layout, and prints the extra nvcc flags on its last line. patches/0001 includes the encoder from src/ocean.cu.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ocean="$2"
layout="$3"
python3 "$here/gen_layout.py" "$layout" /tmp/attention_layout.h
cmp -s /tmp/attention_layout.h "$here/attention_layout.h" || { echo "attention_layout.h does not match $layout: run gen_layout.py"; exit 1; }
cp "$here/attention.cu" "$here/attention_layout.h" "$ocean/"
echo "-DCHARTER_ATTENTION"
