#!/bin/bash
# Build rl/build/libcharter_rl.so: the Charter engine, the arena's bots and the training environment, as one C library
# over Lean's shared runtime. Needs `lean` and `lake` on PATH. Usage: rl/env/build.sh [jobs]
set -euo pipefail
cd "$(dirname "$0")/../.."
JOBS=${1:-$(nproc)}
LEAN_HOME=$(lean --print-prefix)
OUT=rl/build
mkdir -p $OUT/obj
lake build CharterRL.Capi
python3 rl/env/modules.py > $OUT/modules.txt
# One object per module, rebuilt only when its C file changes.
build_one() {
  c=$1
  o=$OUT/obj/$(echo "${c#$PWD/}" | tr '/' '_' | sed 's/\.c$/.o/')
  if [ ! -f "$o" ] || [ "$c" -nt "$o" ]; then
    leanc -O3 -DNDEBUG -fPIC -c "$c" -o "$o"
  fi
  echo "$o"
}
export -f build_one
export OUT
xargs -P "$JOBS" -I{} bash -c 'build_one {}' < $OUT/modules.txt > $OUT/objects.txt
cc -O2 -fPIC -c rl/env/capi.c -I rl/env -I"$LEAN_HOME/include" -o $OUT/capi.o
cc -shared -o $OUT/libcharter_rl.so $OUT/capi.o $(cat $OUT/objects.txt) \
  -L"$LEAN_HOME/lib/lean" -lleanshared -lInit_shared \
  -Wl,-rpath,"$LEAN_HOME/lib/lean" -Wl,-rpath,"$LEAN_HOME/lib"
echo "built $OUT/libcharter_rl.so from $(wc -l < $OUT/objects.txt) modules"
