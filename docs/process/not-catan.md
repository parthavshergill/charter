# Not Catan: how far the rule language gets

Not Catan is an extension pack. It tries to build the board game Catan inside Charter, with only `GameDef` and founding laws. No engine, spec or proof file changed. The gaps are the point: this file is the evidence for where to push the rule language.

**The Claude games were stopped early, on the owner's decision.** Neither game finished. There is no winner, no end of game and no exit interview. So anything about endings, pace to 10 points, or how seats judged the whole game is unknown. See [What was played](#what-was-played).

The pack is in `Charter/Games/NotCatan.lean`. `Charter/Games/NotCatanTests.lean` plays each law and each rejected idea through `Engine.step`, and it runs in every build. "Tested" below means that file. "Seen" means the logs of the stopped Claude games.

## The trick that makes most of this possible

A law cannot read the dice. But a map can hold a region that no tile draws. `alarmRegion` pays one more resource, `alarm`, on a 7, to every piece on every corner. A law that reacts to a harvest of `alarm` therefore reacts to a 7. The first law sends the alarm straight to the treasury, so no hand keeps it, and "the treasury holds alarm" means "a 7 came up this round". The law clears it at the round's end.

`G.Valid` accepts this because a region only has to name a real resource and real spots. A resource that no piece and no fee costs is treated as a counter: the screen and the Claude seats leave it out of hands, trades and what a corner pays.

Another worker is adding laws that read the dice. When that lands, this trick can go.

## What fits, and what does not

| Feature | Status | How | What is missing | Evidence |
| --- | --- | --- | --- | --- |
| 19 hexes, tile mix 4/4/4/3/3 and a desert | Exact | Tiles and regions | | Tested |
| Number tokens, standard distribution | Exact | No 6 or 8 touches another | | Tested |
| Map changes each game | Not possible | The map is fixed in `GameDef`. Both Claude games opened on the same corner, spot 7 | A map chosen from the seed | Seen |
| Desert position | Fixed | In the middle, because laws' monuments stand on the first tile | | |
| Costs, 5/4/15 limits, 2d6, 10 points, 4-for-1, 19 of each | Exact | Existing fields | | Tested |
| Two setup passes, snake order, free settlement and road | Exact | Engine | | Tested |
| Roads cannot pass a rival's settlement | Differs | A road only needs to touch your own piece | A placement rule about rivals | Read in `placementOk` |
| No game length limit | Differs | A game stops at 30 rounds at most | `maxRoundsAllowed` | |
| Player-to-player trading | Close | Offers on your own turn, as in the original | Open hands change it: every seat can count every card | Seen: 89 offers, 30 accepted |
| Starting goods from the second settlement | Rough | At a round's end, a seat with an empty hand and two towns gets 1 timber, 1 brick, 1 grain | No trigger in setup, and the goods do not depend on the corner | Tested. It never fired in the Claude games |
| Discard on a 7 | Rough | Hidden region and flag. At the round's end, hands over 7 lose half of each good, rounded down, to the bank | The check is late and takes half of each good, not half by choice. (2,2,2,1,1) loses 3 of 8, not 4 | Tested and seen |
| Discard at the moment of the roll | Rejected | Passes `lawProblems`, and takes the whole hand. A harvest law runs once per piece, and short payers pay in proportion | A trigger that runs once per seat per roll | Tested |
| By cases, one per piece count | Refused | `lawProblems`: "this law is too big". Rounding would also make it take nothing at 9 pieces | `div` only by a fixed number | Tested |
| A tax on big hands each round | Rejected | Passes, but a 7 means nothing | | Tested |
| Robber blocks a hex | Rough | For the rest of a round with a 7, seats at 5 points or more hand back each harvest | A law cannot see which hex paid. No seat can choose a hex. It hits income for a short time, not one hex for a long time | Tested and seen |
| Blocking one fixed hex | Works, not used | A second hidden region on one hex's corners pays a counter. Needs a resource per hex, and the cap is 8. It cannot move | A chosen hex, and a state per hex | Tested (`hexBlockGame` is valid) |
| Stealing | Rough | Not on a 7. A new knight takes 1 good from every seat ahead: ore, else grain, else wool | No named victim and no randomness. The law's fixed order hides nothing | Tested and seen |
| Knight, as a card to play | Rough | A piece on a settlement for 1 ore, 1 wool, 1 grain, limit 5. It acts when built | No hand of cards, and no playing before the roll | Tested and seen |
| Largest army | Rough | The third knight pays 3 laurel, and 3 laurel buy a wreath worth 2 points. Laurels exist for two wreaths in all | Points come only from pieces, and pieces never move. So a rival cannot take it | Tested and seen |
| Longest road | Rough | The same, for the sixth road | A law counts roads, not a path. No law can measure a graph | Tested and seen |
| Victory point cards | Rough | A relic: 3 ore, 3 wool, 3 grain, 1 point, limit 2, in plain sight | Nothing can be hidden: hands and pieces are public | Tested. Nobody built one |
| Other development cards | Rejected | Each passes as a fixed piece: a monopoly on ore, two fixed goods, the goods for two roads. A "draw" from the bank's ore can be counted in advance | A choice when played, and randomness. Only one more kind of piece fits | Tested |
| Ports, each with its own rate | Not possible | The bank has one rate for everyone, and a law cannot see a trade | A rate per seat, or a trigger on trades | Tested (`setBankRate` is global) |
| Ports, rough | Rough, weak | A harbor on any settlement swaps by itself when its owner is paid: 3 of a surplus for 1 of the next good along a line | No choice of good, and not tied to the coast. It runs on a harvest because at a round's end it plans 48 payments at 6 seats, not 8, out of a limit of 128 | Tested. Nobody built one |
| Short bank pays nobody | Rough | After a harvest that empties the bank, everyone paid gives it back | Wrong when the bank is emptied exactly. Misses a shortfall that leaves a remainder. Engine `settle` pays in proportion | Tested. It never fired in the Claude games: the bank never fell below 5 of any good |

**Setup.** The map has the Island's shape, so the Island's blocked-road game also plays here (`blockedRoadGame`). At 4 seats a seat can lose a free road, but only by choosing a spot with no free link. A seat is never forced: the last setup turn sees at most 28 blocked spots and 7 roads, so at least 19 spots have a free link. The count is checked in the tests. A one-time run of 160,000 random setups at 3 and 4 seats, half of them crowding seat 0, found no forced case and no chosen one. That script is not kept.

**The budget.** The pack uses 7 of 8 resources, 7 of 8 kinds of piece, 7 of 16 laws, and 59 of 128 planned payments at 4 seats. A table can add only one new kind of piece. All seven laws parse back from their formal text, so a majority can rewrite one. `Effect` can nest deeper than the formal text can: the first drafts of three laws could not be written by a player, so they were flattened.

## What was played

| Game | Seats | Stopped at | Points when stopped | Built, with setup | Offers, accepted | Laws |
| --- | --- | --- | --- | --- | --- | --- |
| Claude, WZMTC (seed 4101) | Marguerite (trader), Odalric (schemer), Tomasz (newcomer), Bruno (builder) | Round 15 of 30 | 7, 4, 6, 6 | 15 settlements, 20 roads, 4 cities, 10 knights, 2 wreaths, 0 harbors, 0 relics | 52, 16 | None proposed |
| Claude, ZGHNA (seed 4102) | Tomasz (schemer), Odalric (trader), Vesna (builder), Marguerite (beautifier) | Round 14 of 30 | 7, 6, 7, 6 | 18 settlements, 24 roads, 4 cities, 4 knights, 2 wreaths, 0 harbors, 0 relics | 37, 14 | 3 proposed, 2 passed, 1 lapsed |

Both ran `charter-sim`, which is what `make sim` runs, from a copy of the binary, about 16 minutes each, at the same time. Seats read a wordier form of the laws' sentences than the screen shows now. Both logs load and replay. Results are in `results/`, which git ignores, with no summary or `.jsonl` files, because the runner was stopped. The API use the seat logs recorded was about 1.2 million input tokens, 1 million cached and 124,000 output in each game. The dice showed more 7s than usual: 13 of 57 rolls and 10 of 55, against an expected 1 in 6. Treat every finding about the 7 with that in mind.

Bots, with no Claude involved. Bots do not trade or propose laws here, they buy any attached piece as soon as they can, and they always pick the same corners. So these show that the pack runs to the end, and not how it plays:

- Four games at 4 seats, on the final map: over at rounds 23, 21, 30 and 30. Seat 2 won all four. Two reached the round limit.
- Three at 4 seats and one at 3, on an earlier map: over at rounds 21, 23, 20 and 25.
- Two Island games, for comparison: over at rounds 16 and 21.
- A browser game of one scripted seat and three bots: a bot reached 10 in round 29.

`make smoke` also plays bot games at 3 and 4 seats, and restarts the server on them.

## What the stopped games show

These are from about half a game each. They say nothing about how a game ends.

**The 7 changed how seats held cards.** This is the clearest success. Seats read the alarm correctly, and they planned around the delay, which the original does not allow. Tomasz: "Nine cards in hand and a 7 would cut them in half, so I spent three on a knight." Marguerite refused a trade because it "would also put me at 8 cards while the alarm is still in the treasury."

**The thief is too strong late.** The threshold of 5 points stops meaning "the leaders". By round 13 in both games most or all seats were over it, so a 7 cancelled most of the table's income for the rest of the round. Vesna, with cities on the hot numbers: "Six grain harvested, six grain taken by Law 1 again." Tomasz: "The dice gave me a 4 and the rules gave me nothing." A fairer test would compare a seat to the others, and a law cannot ask "is this seat ahead of all others".

**Knights worked as politics, not as a rule of thumb.** Seats counted who a knight would rob before selling ore. In ZGHNA, Tomasz and Vesna made a whispered pact against it, and it was repealed in round 10. That is the rule loop working, on a pack's own law. One seat was unsure what the piece was: "I still do not know what a knight does on the board apart from robbing seats ahead."

**The awards ended too soon.** Both wreaths were gone by round 6 in ZGHNA and round 13 in WZMTC, and could not move after that. The race for them was real: both games have seats counting it. After it, knights and extra roads were worth much less. One seat drafted a law to pay out the laurels in the treasury, and another thought about it. ZGHNA built 4 knights against 10 in WZMTC, because roads got there first. Six roads may be too cheap against three knights. Two games are not enough to say.

**Harbors and relics went unbuilt in about 15 rounds each.** The harbor gives no choice and no clear gain, and seats preferred their settlements: "a harbor would eat the brick I need". Its one use was a trick: Tomasz proposed making harbors worth a point with exactly the goods for two in hand. All three other seats saw it at once, and it lapsed. Relics are a late purchase, so stopping at round 15 may be why. We do not know.

**Trading looked like the Island's.** About a third of offers were accepted. Open hands made seats refuse the leader, and scarcity turned into hoarding: "Everyone is hoarding grain against me, which is the correct play."

**How close is it to the original?** This is our reading of partial logs, since no seat was interviewed. The opening and the build race feel right: same corners logic, same prices, the same hunt for ore and brick. The robber's feeling is mostly missing. Nobody chooses a victim, nobody moves anything, and nobody plays a card. Those choices are most of the drama of a 7 in the original. Whether it is fun to the end is unknown.

## What would most close the gap

Laws reading the dice are being built elsewhere, so they are not listed here.

1. **A move with an argument.** A way for a seat to choose a target when it builds or plays: a seat, a hex or a good. This one feature would turn the rough robber, knight, monopoly and plenty into close copies. Commandment II does not stand in the way: the law still names no seat, and the seat chooses at play time. The games show the need: seats had to read a fixed order to learn who a knight robs.
2. **A title that moves.** Points that follow a condition, or a token worth points while held. The games show the awards ending early and stuck. A law could then also say "whoever has the most knights". It needs a "most" over seats, which `Cond` lacks. The thief's threshold needs the same.
3. **A trigger on trades, and a rate per seat.** Without these a port cannot exist, and the rough harbor went unused.
4. **A law that can see which region paid, and a state per region.** This is what a blocked hex needs.
5. **Once-per-seat harvest triggers, and a trigger at the end of setup.** These fix the discard timing and the starting goods. Hidden information and random draws would come after these, and they would change far more, since the proofs assume open state.
