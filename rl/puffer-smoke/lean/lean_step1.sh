set -x
mkdir -p ocean/leantiny && cp /tmp/lean/leantiny.h ocean/leantiny/leantiny.h && cp /tmp/lean/leantiny.ini config/leantiny.ini
cd /tmp/lean
$LEAN/bin/lean --version
$LEAN/bin/lean -c SmokeGame.c SmokeGame.lean || exit 2
grep -n 'initialize_SmokeGame(' SmokeGame.c | head -2
$LEAN/bin/leanc -O3 -fPIC -c SmokeGame.c -o SmokeGame.o || exit 3
$LEAN/bin/leanc -O3 -fPIC -c smoke_shim.c -o smoke_shim.o || exit 4
$LEAN/bin/leanc --print-ldflags | cut -c1-500
ls $LEAN/lib/lean | grep -E '^lib' | head -30
ls $LEAN/lib | head -30
objdump -d --no-show-raw-insn $LEAN/lib/lean/libleanrt.a 2>/dev/null | grep -A6 '<lean_initialize_thread>:' | head -12
objdump -d --no-show-raw-insn $LEAN/lib/lean/libleanrt.a 2>/dev/null | grep -A6 '<lean_finalize_thread>:' | head -12
$LEAN/bin/leanc -O3 bench.c SmokeGame.o smoke_shim.o -o bench -lpthread || exit 5
for t in 1 2 4; do ./bench $t 200000 init; done
for t in 1 4; do ./bench $t 200000 noinit; done
ls -la bench SmokeGame.o smoke_shim.o
