set -x
R=/opt/pufferlib
mkdir -p ocean/leantiny && cp /tmp/lean/leantiny.h ocean/leantiny/leantiny.h && cp /tmp/lean/leantiny.ini config/leantiny.ini
cd /tmp/lean
$LEAN/bin/lean -c SmokeGame.c SmokeGame.lean || exit 2
$LEAN/bin/leanc -O3 -fPIC -c SmokeGame.c -o SmokeGame.o || exit 3
$LEAN/bin/leanc -O3 -fPIC -c smoke_shim.c -o smoke_shim.o || exit 4
gcc -O3 -c bench.c -o bench.o || exit 5
$LEAN/bin/leanc -O3 bench.o SmokeGame.o smoke_shim.o -o bench -lpthread || exit 6
ls -la bench
set +x
echo "== BENCH Lean game, plain C threads"
for t in 1 2 4; do ./bench $t 200000 init; done
echo "== BENCH without lean_initialize_thread"
for t in 1 4; do ./bench $t 200000 noinit; echo "noinit threads=$t exit=$?"; done
cd $R

echo "== BUILD c baseline"
./build.sh leantiny puffer_c 2>&1 | tail -5

echo "== BUILD lean, shared runtime, no build.sh edit"
LSH="/tmp/lean/SmokeGame.o /tmp/lean/smoke_shim.o -L$LEAN/lib/lean -lleanshared -lInit_shared -Xlinker=-rpath -Xlinker=$LEAN/lib/lean -Xlinker=-rpath -Xlinker=$LEAN/lib"
NVCC_EXTRA="-DSMOKE_LEAN $LSH" ./build.sh leantiny puffer_shared 2>&1 | tail -15
ls -la puffer_shared; ldd puffer_shared | grep -iE 'lean|c\+\+|stdc|omp' 

echo "== BUILD lean, static runtime, three-line build.sh branch"
cp build.sh build_static.sh
python3 - <<'PY'
import os
L = os.environ["LEAN"] + "/lib"
s = open("build_static.sh").read()
marker = 'elif [ -d "ocean/$ENV" ]; then\n    SRC_DIR="ocean/$ENV"\n'
assert marker in s
block = ('elif [ "$ENV" = "leantiny" ]; then\n    SRC_DIR="ocean/$ENV"\n'
         f'    EXTRA_LDFLAGS+=(/tmp/lean/SmokeGame.o /tmp/lean/smoke_shim.o -L{L}/lean -L{L} '
         '-Xlinker --start-group -lInit -lStd -lleanrt -Xlinker --end-group -lgmp -luv -l:libc++.a -l:libc++abi.a)\n')
s = s.replace(marker, block + marker, 1)
open("build_static.sh", "w").write(s)
PY
diff build.sh build_static.sh
NVCC_EXTRA="-DSMOKE_LEAN" bash build_static.sh leantiny puffer_static 2>&1 | tail -15
ls -la puffer_static; ldd puffer_static | grep -iE 'lean|c\+\+|stdc|omp'

run() {
  tag=$1; bin=$2; shift 2
  echo "== TRAIN $tag"
  timeout --kill-after=10 200 ./$bin train --base.checkpoint_dir=$OUT/$tag/ckpt --base.log_dir=$OUT/$tag/logs --train.total_timesteps=20000000 "$@" 2>&1 | tr '\r' '\n' | sed 's/\x1b\[[0-9;?]*[A-Za-z]//g' > $OUT/$tag.log
  echo "exit ${PIPESTATUS[0]}"
  grep -E 'bot_eval|Assert|assert|Abort|Segm|rror' $OUT/$tag.log | head -20
  tail -18 $OUT/$tag.log | cut -c1-82
}
if [ -x puffer_c ]; then run c puffer_c; fi
if [ -x puffer_shared ]; then run shared puffer_shared; fi
if [ -x puffer_static ]; then run static puffer_static; fi

BEST=puffer_static; [ -x $BEST ] || BEST=puffer_shared
TAG=static; [ -x puffer_static ] || TAG=shared
if [ -x $BEST ]; then
  FIRST=$(find $OUT/$TAG/ckpt -name '*.bin' | sort | head -1)
  LAST=$(find $OUT/$TAG/ckpt -name '*.bin' | sort | tail -1)
  ls -la $FIRST $LAST
  E="--headless --selfplay.enabled=0 --vec.num_policies=1 --vec.hist_policy_percent=0 --env.num_agents=1 --vec.total_agents=1024 --base.eval_episodes=4096"
  for bot in 0 1; do
    for who in FIRST LAST; do
      echo "== EVAL $who vs Lean bot $bot"
      timeout 60 ./$BEST eval ${!who} $E --env.bot_policy=$bot 2>&1 | tr '\r' '\n' | grep -E 'CUDA_EVAL|Abort|rror'
    done
  done
  echo "== MATCH 4 seats: trained seat 0 vs untrained seats 1-3"
  timeout 60 ./$BEST match --headless --base.load_model_path=$LAST --base.load_enemy_model_path=$FIRST --vec.total_agents=1024 --base.eval_episodes=4096 2>&1 | tr '\r' '\n' | grep -E 'CUDA_EVAL|Abort|rror'
  echo "== MATCH 4 seats: untrained seat 0 vs trained seats 1-3"
  timeout 60 ./$BEST match --headless --base.load_model_path=$FIRST --base.load_enemy_model_path=$LAST --vec.total_agents=1024 --base.eval_episodes=4096 2>&1 | tr '\r' '\n' | grep -E 'CUDA_EVAL|Abort|rror'
fi
echo "== DONE"
