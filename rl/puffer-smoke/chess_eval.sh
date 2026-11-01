export OUT=/vol/chess
./build.sh chess 2>&1 | tail -1
FIRST=$(find $OUT/ckpt -name '*.bin' | sort | head -1)
LAST=$(find $OUT/ckpt -name '*.bin' | sort | tail -1)
find $OUT/ckpt -name '*.bin' | wc -l
ls -la "$FIRST" "$LAST"
COMMON="--headless --selfplay.enabled=0 --vec.num_policies=1 --vec.hist_policy_percent=0 --vec.total_agents=1024 --vec.num_buffers=1 --vec.num_threads=4 --base.eval_episodes=1000 --env.fen_curric_pct=0"
show() { tr '\r' '\n' | sed 's/\x1b\[[0-9;?]*[A-Za-z]//g' | grep -E 'CUDA_EVAL|Abort|Assert|chess_moves|perf |wins_as|games_as|draw_rate|hist_score  ' | tail -7 | cut -c1-82; }
echo "== untrained vs random mover"
timeout 90 ./puffer eval "$FIRST" --env.mode=0 $COMMON 2>&1 | show
echo "== trained vs random mover"
timeout 90 ./puffer eval "$LAST" --env.mode=0 $COMMON 2>&1 | show
echo "== match trained (seat 0) vs untrained (seat 1)"
timeout 90 ./puffer match --headless --base.load_model_path="$LAST" --base.load_enemy_model_path="$FIRST" --vec.total_agents=1024 --vec.num_buffers=1 --vec.num_threads=4 --base.eval_episodes=1000 --env.fen_curric_pct=0 2>&1 | show
echo "== DONE"
