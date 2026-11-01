R=/opt/pufferlib
mkdir -p ocean/leantiny && cp /tmp/lean/leantiny.h ocean/leantiny/leantiny.h && cp /tmp/lean/leantiny.ini config/leantiny.ini
cd /tmp/lean
$LEAN/bin/lean -c SmokeGame.c SmokeGame.lean || exit 2
$LEAN/bin/leanc -O3 -fPIC -c SmokeGame.c -o SmokeGame.o || exit 3
$LEAN/bin/leanc -O3 -fPIC -c smoke_shim.c -o smoke_shim.o || exit 4
cd $R
LSH="/tmp/lean/SmokeGame.o /tmp/lean/smoke_shim.o -L$LEAN/lib/lean -lleanshared -lInit_shared -Xlinker=-rpath -Xlinker=$LEAN/lib/lean -Xlinker=-rpath -Xlinker=$LEAN/lib"
NVCC_EXTRA="-DSMOKE_LEAN $LSH" ./build.sh leantiny puffer_shared 2>&1 | tail -1
echo "== proof the binary calls Lean"
objdump -d --no-show-raw-insn puffer_shared | grep -E 'call.*<smoke_(step|new|read_obs|thread_init)' | sort -k3 | uniq -c -f2 | head -8
objdump -d --no-show-raw-insn puffer_shared | grep -cE 'call.*<smoke_'
A="--base.checkpoint_dir=$OUT/s3/ckpt --base.log_dir=$OUT/s3/logs --train.total_timesteps=20000000"
echo "== TRAIN 4 seats, three distinct frozen opponents per frozen env"
timeout --kill-after=10 200 ./puffer_shared train $A --env.distinct_opps=1 --vec.num_policies=4 --vec.hist_policy_percent=0.25 2>&1 | tr '\r' '\n' | sed 's/\x1b\[[0-9;?]*[A-Za-z]//g' > $OUT/s3.log
echo "train exit ${PIPESTATUS[0]}"
grep -E 'bot_eval|ssert|Abort' $OUT/s3.log | sort -u | head
grep -E 'pool/|Steps  ' $OUT/s3.log | tail -3 | cut -c1-82
FIRST=$(find $OUT/s3/ckpt -name '*.bin' | sort | head -1)
LAST=$(find $OUT/s3/ckpt -name '*.bin' | sort | tail -1)
M="--headless --vec.total_agents=1024 --base.eval_episodes=4096 --env.distinct_opps=0 --vec.num_threads=4"
echo "== MATCH trained seat 0 vs untrained seats 1-3"
timeout 60 ./puffer_shared match --base.load_model_path=$LAST --base.load_enemy_model_path=$FIRST $M 2>&1 | tr '\r' '\n' | grep -E 'CUDA_EVAL|Abort|ssert|missing'
echo "== MATCH untrained seat 0 vs trained seats 1-3"
timeout 60 ./puffer_shared match --base.load_model_path=$FIRST --base.load_enemy_model_path=$LAST $M 2>&1 | tr '\r' '\n' | grep -E 'CUDA_EVAL|Abort|ssert|missing'
echo "== CPU build of the Lean env"
NVCC_EXTRA="-DSMOKE_LEAN $(echo $LSH | sed 's/-Xlinker=/-Wl,/g')" CC=clang ./build.sh leantiny leantiny_cpu --cpu 2>&1 | tail -4
if [ -x leantiny_cpu ]; then
  timeout 60 ./leantiny_cpu $LAST --headless --base.eval_episodes=500 --env.num_agents=1 --env.bot_policy=0 2>&1 | grep -E 'CPU_|ssert|Abort'
fi
echo "== policy read by another program"
cp /tmp/lean/policy_harness.c /tmp/lean/policy_reader.py .
W=$(find /vol/breakout/ckpt -name '*.bin' | sort | tail -1)
clang -O2 -Isrc policy_harness.c -lm -o harness 2>&1 | tail -3
./harness $W 118 32 4 3
python3 -I /tmp/lean/policy_reader.py $W 118 32 4 3
echo "== DONE"
