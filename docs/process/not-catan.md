# Not Catan: how far the rule language gets

Not Catan is an extension pack. It builds what it can of the board game Catan inside Charter, with only `GameDef` and founding laws. No engine, spec or proof file changed for it. The gaps are the point: this file is the evidence for where to push the rule language.

The pack is in `Charter/Games/NotCatan.lean`. `Charter/Games/NotCatanTests.lean` plays each law and each rejected idea through `Engine.step`, and it runs in every build. "Tested" below means that file.

**No Claude game has been played on this version.** Two Claude games were played on an earlier version, with a different 7 rule, and were stopped early. See [The earlier version](#the-earlier-version). This version has run only with bots and scripted moves, which shows that it runs to the end and not how it plays.

## The founding laws

There are four, and they fit on one screen.

| Law | Its statement |
| --- | --- |
| A 7 costs big hands half | When a 7 is rolled, for each player, if their timber, grain, ore, wool and brick together is more than 7, they pay half of their timber, grain, ore, wool and brick, each rounded down, to the bank. |
| A new knight takes ore from each seat ahead | Anyone who builds a knight gets 1 ore from every other player with more points than the builder and at least 1 ore. |
| The third knight or sixth road earns a wreath | Anyone with exactly 2 knights who builds a knight gets 3 laurel from the bank. Anyone with exactly 5 roads who builds a road gets 3 laurel from the bank. Each time a wreath is built, the bank pays 3 laurel to the treasury. |
| A harvest that empties the bank pays nobody | Each time a player is paid at harvest, if the bank's holding of that resource is equal to 0, they pay all of it to the bank. |

The pack also has three pieces of its own: a knight, a relic and a wreath. It uses 6 of 8 resources, 6 of 8 kinds of piece, 4 of 16 laws, and 28 of 128 planned payments at 4 seats. So a table has room for its own laws and pieces.

## What fits, and what does not

| Feature | Status | How | What is missing | Evidence |
| --- | --- | --- | --- | --- |
| 19 hexes, tile mix 4/4/4/3/3 and a desert | Exact | Tiles and regions | | Tested |
| Number tokens, standard distribution | Exact | No 6 or 8 touches another | | Tested |
| Map changes each game | Not possible | The map is fixed in `GameDef` | A map chosen from the seed | Read in `GameDef` |
| Desert position | Fixed | In the middle, because laws' monuments stand on the first tile | | |
| Costs, 5/4/15 limits, 2d6, 10 points, 4-for-1, 19 of each | Exact | Existing fields | | Tested |
| Two setup passes, snake order, free settlement and road | Exact | Engine | | Tested |
| Roads cannot pass a rival's settlement | Differs | A road only needs to touch your own piece | A placement rule about rivals | Read in `placementOk` |
| No game length limit | Differs | A game stops at 30 rounds at most | `maxRoundsAllowed` | |
| Player-to-player trading | Close | Offers on your own turn, as in the original | Open hands change it: every seat can count every card | Engine |
| Discard on a 7 | Close | A founding law on the roll, once per seat. No hex pays | It takes half of each good, rounded down, and not half by the seat's choice. (2,2,2,1,1) loses 3 of 8, not 4 | Tested |
| Robber | Left out | The owner does not want it as a goal. The earlier version's rough copy was removed | A chosen hex and a chosen victim | |
| Stealing | Rough | A new knight takes 1 ore from every seat ahead | No named victim and no randomness. Only ore | Tested |
| Knight, as a card to play | Rough | A piece on a settlement for 1 ore, 1 wool, 1 grain, limit 5. It acts when built | No hand of cards, and no playing before the roll | Tested |
| Largest army | Rough | The third knight pays 3 laurel, and 3 laurel buy a wreath worth 2 points. Laurels exist for two wreaths in all | Points come only from pieces, and pieces never move. So a rival cannot take it | Tested |
| Longest road | Rough | The same, for the sixth road | A law counts roads, not a path. No law can measure a graph | Tested |
| Victory point cards | Rough | A relic: 3 ore, 3 wool, 3 grain, 1 point, limit 2, in plain sight. No law | Nothing can be hidden: hands and pieces are public | Tested as a piece |
| Other development cards | Left out | Each passes as a fixed piece: a monopoly on ore, two fixed goods, the goods for two roads. A "draw" from the bank's ore can be counted in advance | A choice when played, and randomness | Tested, not in the pack |
| Ports, each with its own rate | Not possible | The bank has one rate for everyone, and a law cannot see a trade | A rate per seat, or a trigger on trades | Tested (`setBankRate` is global) |
| Ports, rough | Cut | A harbor that swaps a surplus by itself when its owner is paid. It works, it took four long lines, and nobody built one in the earlier games | Choice of good, and a tie to the coast | Tested, not in the pack |
| Starting goods from the second settlement | Cut | An empty hand on two towns gets 3 goods at a round's end. It works, it never fired in the earlier games | A trigger in setup, and goods that depend on the corner | Tested, not in the pack |
| Short bank pays nobody | Rough | After a harvest that empties the bank, everyone paid gives it back | Wrong when the bank is emptied exactly. Misses a shortfall that leaves a remainder. Engine `settle` pays in proportion | Tested |

**Setup.** The map has the Island's shape, so the Island's blocked-road game also plays here (`blockedRoadGame`). At 4 seats a seat can lose a free road, but only by choosing a spot with no free link. A seat is never forced: the last setup turn sees at most 28 blocked spots and 7 roads, so at least 19 spots have a free link. The count is checked in the tests. A one-time run of 160,000 random setups at 3 and 4 seats, half of them crowding seat 0, found no forced case and no chosen one. That script is not kept.

**The formal text.** All four laws parse back from their formal text, so a majority can rewrite one.

## What was played on this version

Bots and scripted moves only. No Claude seat. Bots do not trade or propose laws here, they buy any attached piece as soon as they can, and they always pick the same corners. So these show that the pack runs to the end, and not how it plays.

- Four games at 4 seats, by `charter-sim`: over at rounds 24, 25, 30 and 26. Seats 2, 1, 1 and 1 won. One reached the round limit.
- One game at 3 seats: over at round 26.
- In the browser, one scripted seat and three bots: a bot reached 10 in round 28. The chronicle showed "By law, on a 7, Bot Grace paid the bank 1 timber, 2 grain and 1 ore."
- `make smoke` plays bot games at 3 and 4 seats, and restarts the server on them.

## The earlier version

Two Claude games were played on an earlier version of this pack, and the owner had them stopped. Neither finished. There is no winner, no end of game and no exit interview. **Their findings about the 7 come from a different rule.**

That version had seven laws. A law could not read the dice then, so a region no tile drew paid a counter called `alarm` on a 7, and the counter stayed in the treasury until the round's end. Hands over 7 lost half at the round's end, not at the roll. A thief law took the harvests of seats with 5 points or more until then. A knight took ore, else grain, else wool. It also had the harbor and the first hand. All of that is gone.

| Game | Seats | Stopped at | Points when stopped | Built, with setup | Offers, accepted | Laws |
| --- | --- | --- | --- | --- | --- | --- |
| WZMTC (seed 4101) | Marguerite (trader), Odalric (schemer), Tomasz (newcomer), Bruno (builder) | Round 15 of 30 | 7, 4, 6, 6 | 15 settlements, 20 roads, 4 cities, 10 knights, 2 wreaths, 0 harbors, 0 relics | 52, 16 | None proposed |
| ZGHNA (seed 4102) | Tomasz (schemer), Odalric (trader), Vesna (builder), Marguerite (beautifier) | Round 14 of 30 | 7, 6, 7, 6 | 18 settlements, 24 roads, 4 cities, 4 knights, 2 wreaths, 0 harbors, 0 relics | 37, 14 | 3 proposed, 2 passed, 1 lapsed |

**Those saved tables no longer replay.** The server leaves them out and says why: WZMTC stops at event 76 ("this piece cannot be placed there now"), and ZGHNA at event 52 ("there is no such proposal"). The 7 now moves goods at a different moment, and the founding laws take fewer proposal ids. Any other saved Not Catan table from that version goes the same way.

What those games still say, about parts that did not change:

- **The wreath race was real, and it ended too soon.** Both wreaths were gone by round 6 in ZGHNA and round 13 in WZMTC, and could not move after that. ZGHNA built 4 knights against 10 in WZMTC, because roads got there first. Six roads may be too cheap against three knights. Two games are not enough to say.
- **Trading looked like the Island's.** About a third of offers were accepted, and open hands turned scarcity into hoarding: "Everyone is hoarding grain against me, which is the correct play."
- **Relics went unbuilt in about 15 rounds.** They are a late purchase, so stopping early may be why. We do not know.
- **Both games opened on the same corner, spot 7,** because the map is fixed.

What they say about parts that changed, so only as a hint:

- **Seats planned around a big hand.** "Nine cards in hand and a 7 would cut them in half, so I spent three on a knight." But that seat could spend after the 7 and before the round's end. Now it cannot, so the rule should bite harder, and nobody has played it.
- **The thief was too strong late.** By round 13 most seats were over its threshold. It was removed, so this is closed.
- **Knights worked as politics.** Seats counted who a knight would rob before selling ore, and ZGHNA repealed the knight law in round 10 after a whispered pact. The law is now smaller, so this may not hold.
- **Harbors were used only as a trick.** Tomasz proposed making them worth a point, with the goods for two in hand. All three other seats saw it at once. Harbors are gone.

**How close is it to the original?** This is our reading of the rules, since nobody has played this version. The opening and the build race should feel right: same prices, the same hunt for ore and brick. A 7 now lands at the right moment and hurts in the right way. What is missing is every choice around it: nobody moves anything, nobody chooses a victim, and nobody plays a card. Whether it is fun to the end is unknown.

## What would most close the gap

1. **A move with an argument.** A way for a seat to choose a target when it builds or plays: a seat, a hex or a good. This one feature would turn the rough knight, monopoly and plenty into close copies. Commandment II does not stand in the way: the law still names no seat, and the seat chooses at play time.
2. **A title that moves.** Points that follow a condition, or a token worth points while held. A law could then say "whoever has the most knights". It needs a "most" over seats, which `Cond` lacks.
3. **A trigger on trades, and a rate per seat.** Without these a port cannot exist.
4. **A trigger at the end of setup.** This gives starting goods.
5. **A map from the seed.** Every game now opens the same way. Hidden information and random draws would come later, and they would change far more, since the proofs assume open state.
