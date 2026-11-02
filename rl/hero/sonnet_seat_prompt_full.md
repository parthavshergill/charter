You are playing one seat in a game of Charter, a board game for 4 players. Play to win.

**Rules.** Read `/home/user/charter/Server/player_rules.md`, the sections "Reading a law" and "The rules", including laws, deals, trades and the strategy notes. Skip "How you answer": in this game you act through a command instead, described below. The moves you may make are exactly the ones the command lists.

**Your game:** code `{CODE}`, you are seat `{SEAT}`.

**How to play.**
- Run `python3 /home/user/charter/rl/hero/seat.py wait --game {CODE} --seat {SEAT} --timeout 540`. It waits until you have something to decide. Then it shows the board, every seat's points, hands and pieces, and a numbered list of your legal moves.
- To make move N and then wait for your next decision, run this as one command: `python3 /home/user/charter/rl/hero/seat.py play --game {CODE} --seat {SEAT} N; python3 /home/user/charter/rl/hero/seat.py wait --game {CODE} --seat {SEAT} --timeout 540`
- Always give the Bash tool `timeout: 600000`. If `wait` times out, run it again: the other players are still thinking.
- Keep going until it says the game is over.
- On your turn you may also talk, offer trades to other seats, propose laws and declare numbers. Each of these is a command, after which you run `wait` again:
  - `seat.py say --game {CODE} --seat {SEAT} [--to T] TEXT`: talk to the table, or privately to seat T.
  - `seat.py offer --game {CODE} --seat {SEAT} --give brick:1,wool:1 --get ore:1 [--to T]`: offer a trade.
  - `seat.py propose --game {CODE} --seat {SEAT} (--text RULE | --sample ID) [--check]`: propose a law, either in the rule language or one of the sample laws listed in the view. `--check` previews it without proposing.
  - `seat.py declare --game {CODE} --seat {SEAT} --res RES --n N`: declare a number.
  Votes, signing deals and accepting offers appear as numbered moves.
- Use only these commands. Don't read other files or code, don't look at the server or other seats' commands, and don't run anything else.

**Play well.** On your turn, think about where to build, what you need, and when a bank trade helps. A free setup piece you don't place is lost, so place both setup pieces. You win the moment you reach the target points. If nobody does by the last round, the most points wins.

**When the game is over,** run `python3 /home/user/charter/rl/hero/seat.py result --game {CODE}`. Reply with the result line and two or three sentences on your plan and why you won or lost.
