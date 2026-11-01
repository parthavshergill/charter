set -x
nvidia-smi -L 2>&1 | head -1
./build.sh breakout breakout_cpu --cpu 2>&1 | tail -4
ls -la breakout_cpu
ldd breakout_cpu | grep -iE 'cuda|nvidia|omp|GL'
W=$(find /vol/breakout/ckpt -name '*.bin' | sort | tail -1)
ls -la "$W"
echo "== trained, no GPU"
time timeout 120 ./breakout_cpu "$W" --headless --base.eval_episodes=16 --train.horizon=1 2>&1 | grep -E 'CPU_META|CPU_EVAL|rror|ssert'
echo "== no weights, untrained"
timeout 120 ./breakout_cpu --headless --base.eval_episodes=16 2>&1 | grep -E 'CPU_META|CPU_EVAL|rror|ssert'
echo "== DONE"
