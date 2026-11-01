#!/bin/bash
# Build and run rl/puffer/test_env.c. Usage: rl/puffer/test_env.sh PUFFERLIB_DIR [seconds] [extra cflags]
set -euo pipefail
cd "$(dirname "$0")/../.."
P=$1
RAYLIB=$(ls -d $P/raylib-5.5_linux_amd64 2>/dev/null || true)
cc -O2 ${3:-} -I rl/puffer -I rl/env -I $P/src -I $RAYLIB/include rl/puffer/test_env.c \
  -L rl/build -lcharter_rl -Wl,-rpath,$PWD/rl/build -o rl/build/test_env
rl/build/test_env ${2:-3}
