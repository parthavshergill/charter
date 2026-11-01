# The first games played by Claude

We ran two complete games on the Island, with four Claude seats in each. No person played. The question was: is the game fun, and does the rule loop produce a story?

**Short answer.** Yes, in the second game. It has a real plot: a law trick, a siege by taxation, a Trojan horse voted down, and a winner who went around the wall. In the first game no, or not until the last round: it was a plain trading race for fifteen rounds, and its only law never collected anything. Two games are not a result. They show the range. Neither game used a funded deal, and that is the biggest gap.

## The runs

|  | Game 1 (seed 2026) | Game 2 (seed 2027) |
| --- | --- | --- |
| Table | WVZYF | PSZQP |
| Winner | Ines (trader), 10 points | Marguerite (schemer), 10 points |
| Others | Lucan 9, Tomasz 8, Bruno 6 | Tomasz 9, Odalric 8, Vesna 8 |
| Rounds | 16 | 19 |
| Events | 271 | 277 |
| Wall-clock time | 28.7 minutes | 32.5 minutes |
| Seat decisions (API calls) | 224, and 4 interviews | 202, and 4 interviews |
| Clerk calls | 3 | 9 |
| Input tokens, not cached | 1,526,511 | 1,367,750 |
| Input tokens, read from cache | 1,250,954 | 1,152,092 |
| Input tokens, written to cache | 15,668 | 37,483 |
| Output tokens | 168,120 | 181,403 |
| Median call, longest call | 8.2 s, 26.2 s | 8.5 s, 39.8 s |
| Rate limits, failed calls, fallbacks | 0, 0, 0 | 0, 0, 0 |
| Actions the engine refused | 2 | 3 |
| Talk: public, private, confessional | 224, 143, 224 | 200, 134, 200 |
| Offers: made, accepted | 62, 12 | 43, 10 |
| Laws: proposed, passed, repealed | 1, 1, 0 | 5, 4, 0 |
| Deals: drafted, proposed, started | 0, 0, 0 | 0, 0, 0 |

The model was `claude-opus-5-5` at effort `medium`, with four requests at a time, and thinking on. Part of the two runs overlapped, with no rate limit. At list prices each game costs about 10 dollars. About 45% of the input tokens came from the cache, because each prompt holds about 6,000 tokens of game state that change every call. A game is about 30 minutes, so many games in a night is practical.

Game 1 ran on the build before the turn timer. Game 2 ran on the build with the timer, and no timer fired in it. Both ran before the fix to the law preview. The rule engine was the same, and both logs replay on the final build.

Personas in game 1: Ines (trader), Lucan (builder), Bruno (schemer), Tomasz (newcomer). In game 2: Vesna (trader), Odalric (beautifier), Marguerite (schemer), Tomasz (newcomer). The seed chose them.

## Game 1: a trading race, then one panic

For fifteen rounds nobody proposed a law. The table made 62 offers and refused most of them. Everyone can see every hand, so everyone counts what a card would build. Tomasz said it best, to the whole table:

> "Ines, you hold three ore and one grain, and a city costs three ore and two grain. I did the same sum for Lucan. My grain stays here."

That is good play, and it became a chore. Lucan, in his interview: "It was safe, it was correct, and it felt like stamping forms. Nobody proposed a single law until round 16, so the 'laws are the point' game was really a plain build race for fifteen rounds."

There was real politics in private. Bruno, the schemer, ran a quiet embargo. He told each seat in turn that the others were one card from a build. Whispers show that alliances were real, and also cheap, because nothing bound them.

Round 16 was the only moment the rules moved. Lucan reached 9 points and needed one brick. Bruno drafted a surcharge on leaders, and the clerk told him what the language could do: "Prices can't differ by player, so this is a treasury charge after building, and a player short of ore or brick pays less." So he changed the plan to something that strips a leader's hand: anyone at 9 or more pays all their grain, ore and brick at each round's end. It passed 3 to 1. Lucan answered in public:

> "Bruno's levy hits anyone at nine. Tomasz and Ines, you're both one cottage from nine, and then it empties your pantries every round while the cook catches up."

Ines voted yes and then used the law's timing. In her confessional:

> "With them I can build a settlement at 53, a road to 43 and a settlement at 43, going straight from 8 to 10 points so the levy never touches me."

She won in the last turn of the round, so the levy never collected anything. Bruno's interview says it "gutted Lucan's 9-point pantry". That is false: the chronicle shows no law payment in this game. **Do not trust a seat's memory of what happened. Check the chronicle.**

## Game 2: the plot we hoped for

**Rounds 3 and 4: relief, and a trick.** Odalric, the beautifier, proposed Frontier Relief: each round, anyone under 4 points gets 1 timber from the bank. He said it was civic. His confessional said: "It helps the whole table and especially me, since timber is my bottleneck." It passed at once. Odalric then sat on the only brick at the table and refused to sell it. So Marguerite wrote a copy of his law for brick. Her confessional:

> "Odalric sits on the only brick and won't sell it, so I'm making the bank hand brick to everyone below four points. It costs him his monopoly, and it gets me my third settlement at spot 1 next turn."

This is the rule loop at work. A player used a law to break another player's market position, by using his own precedent. Odalric voted yes too, to save face: "Better to be the gracious founder of the relief tradition than the lone magpie."

**Round 12: the leader's tax.** Marguerite reached 9 points. Odalric proposed a levy on anyone at 9 or more. He first wrote it for 8 or more, and then raised it to 9 so that it would not hit himself soon. It passed 3 to 1. Marguerite lobbied with partial truths, and her confessional admits it: "I'm lobbying both of them, with a little fibbing." Vesna voted yes, built a city with her whole hand first so that the tax would find nothing, and whispered: "Nothing personal. You were one bank trade from ten. I count, I do not gift."

**Round 13: the second wall.** A second levy took wool and brick, and it passed.

**Rounds 13 to 18: a siege.** The levies and a table-wide refusal to sell held Marguerite at 9 for seven rounds. The seats believed that without the levies she would have won around round 13. Two laws changed the length and the shape of the game. The chronicle has 48 payments by law in all. Marguerite adapted: she learned that a short payer pays in proportion, so she kept her hand thin and collected ore, which nobody would buy from her. Her interview:

> "Turning out my pockets for six straight rounds so their 'leader tax' took a proportional share of nothing, then hoarding ore, which none of them dared buy, and banking twelve of it for the win in round 19."

The levy also hit the people who passed it. Vesna and Tomasz reached 9 and started to pay. Marguerite had warned them. Odalric stayed at 8 on purpose: "The levies were my wall; now they're my moat."

**Round 17: the Trojan horse.** Vesna, with a sealed board and 7 grain, proposed Granaries: a new piece worth 1 point for 3 grain, built on a city. It looked neutral. It was two points for her alone that turn. All three seats saw it at once, and Tomasz, the newcomer, was first:

> "Vesna holds seven grain and four cities; three grain plus three grain is two granaries, and eight plus two is ten. Counted, and I recommend everyone else counts it too."

Odalric: "Friends, behold the wooden horse at the gates of Troy!" Marguerite, in private: "Caesar wrote that law for Caesar." It lapsed with one yes.

**Round 19: around the wall.** Everyone had refused Marguerite grain and wool for six rounds. They forgot the bank:

> "They all guarded the loaf and the fleece so carefully that they forgot the bank sells them too, four ore apiece."

That is a good ending, and the game's fun came from the table reading each other's laws. It also shows a weakness: from round 14 to round 18 the table was frozen.

## Did the rule loop change the game?

- **Game 1: no.** One law, in the last round, and it never paid.
- **Game 2: yes.** Relief laws gave free timber and brick in rounds 3 to 6. Levies seem to have added about six rounds, moved 50 resources into a treasury that nobody ever spent, and changed how every seat held its cards.

Why the difference? The fee is 1 grain and 1 wool, and game 1's seats needed those cards more. Game 2 had a beautifier, whose persona says to write laws. The first law then opened the door: once one passed, the next came two turns later. In game 1 Ines and Bruno spoke of a law in private, and waited until round 16. One first law seems to matter a lot, so we should measure how often a game gets one early.

Good things seen:

- **Seats read laws for who they really hit.** All of them, the newcomer too. This is the fun the game promises.
- **The clerk helped.** Twelve drafts in the two games. It refused none, and every result was a legal rule. Its stated differences changed plans. Vesna dropped two levy drafts: "twice it showed me my levy would barely touch Marguerite before I paid the fee." Bruno's rewrite in game 1 came from the clerk's answer.
- **Nothing stalled, and no seat broke the rules.** Five refused actions in about 550 events, and two of those came just after the game had ended.
- **The voices were good.** Odalric's Roman history, Bruno's food talk, Vesna's "Counted." They hold up for a whole game, and they are fun to read.

Bad things seen:

- **No deal was ever drafted**, in either game. Funded deals are half of the design. Promises stayed in whispers, and whispers were mostly kept, so a seat had no reason to pay a deposit. Several seats then said they wanted exactly what a deal can nearly do. The prompt describes deals, but gives no reason to use them. A person may behave differently, so test this with people before changing anything.
- **Nobody repealed a law.** Marguerite spoke of it for six rounds, and nobody proposed it. Repeal needs 3 of 4 votes, and the seats who voted for a levy did not change their minds.
- **The treasury is a dead end.** In game 2 it ended with 50 resources. No law ever paid from it. The bank ran out of ore (Tomasz: "The bank has exactly one ore"), and this slowed the whole table.
- **The middle gets repetitive.** Every interview names a version of this: offer, refusal, cancel. "Six rounds of saying no to the same person is bookkeeping, not play."

## What each persona reported

These come from the exit interviews, one per seat, in voice. Quotes are in the seat's words.

| Persona | Confusing | Boring | Great |
| --- | --- | --- | --- |
| Newcomer (Tomasz, game 1) | "I lost track of my own score." Learned only in round 14 that cities stop at 4. Unsure when a levy fires. Why a 7 pays nobody, asked in several confessionals. | "Posting '2 timber for 1 brick' to the whole table, being refused by all, and posting it again next turn." | "The trading had real teeth." |
| Newcomer (Tomasz, game 2) | Thought he had 9 when he had 8. The preview showed only wool for a wool and brick levy. "Nobody explained the 'treasury'." | "Re-reading every opponent's purse each turn." | "The levy laws were good." |
| Trader (Ines) | No clean record of who holds what. Whether "each round" meant the round's end. | "Declining two-for-one ore offers from everyone, turn after turn." | "Reading who was one card from a build was real, satisfying play." |
| Trader (Vesna) | Her own score. Reached the city limit with no reachable spot before she noticed. | "From round 14 on the table was frozen." | "The laws made the table talk." Drafting showed her a weak law before she paid. |
| Builder (Lucan) | Which spots were open: "The map is a list of corner numbers with no picture." | "Declining two-for-one offers... stamping forms." | "Upgrading to cities early really did compound." |
| Schemer (Bruno) | Laws cannot set prices by player, and a toll charges after the build. | "Being asked again and again on other people's turns to decline the same desperate... offers." | "Building a levy that looks neutral but lands squarely on the leader." |
| Schemer (Marguerite) | When levies fire, and how "proportional" works. "A rule that size should not need detective work." | "A tax on patience, not on points." | "Being able to see that the granary law was an instant win for Vesna, and to vote it down." |
| Beautifier (Odalric) | When levies charge, and what the treasury holds. | Bank trades with no spot to build. "When the map closes, the base game turns into waiting on dice." | "Laws as weapons felt genuinely alive." |

Some of this is about the seat's interface and not the game. A Claude seat reads the board as a list of corners. The score complaints are about the seats' own notes: the prompt always showed the true points. Since then the prompt has said: "you have exactly N points. Trust this number and not your notes." No full game has run with that line yet.

The newcomer has not read the rules. His confusion is the most useful data here: **a person will ask why a 7 pays nobody, what the treasury is, and when a law's "each round" happens.** The screen does not answer these.

## What the rule language could not say

Seats asked for these in play or in their interviews.

1. **A price that only some players pay, which blocks the build.** Bruno: "anyone at 9+ points pays 3 extra brick to build, and can't build without paying it." A law can only charge after a build, and a short payer pays less. This is a law's natural tool against a leader, and it is missing.
2. **A rule about trades.** Tomasz: "no seat may trade grain or brick to a seat with 8 or more points." Ines: a tax on bank trades. Laws cannot see trades. Six rounds of game 2 were this idea, done by hand.
3. **Binding a vote.** Lucan and Marguerite both wanted a deal that pays for a vote. Deals cannot touch votes. Votes stayed as promises.
4. **A deal with a condition.** Vesna: pays out only if a seat stays under 10. Tomasz: void if you reach 9. Marguerite: a repeal that switches on when a second seat reaches 9. Ines: a standing option to buy at a fixed price.
5. **A charge that does not scale.** Vesna: "each resource is charged separately, not in proportion." Short payers pay in proportion, across all laws in one trigger. So a law can add nothing: the wool and brick levy's preview showed no brick at all, because two laws shared her 2 brick in proportion. That preview was right, and two seats thought it was a bug.
6. **Spending the treasury on the table.** Odalric wanted public works, such as a shared road. A law can pay the treasury to players, but it cannot build for them.
7. **A law tied to turn order.** Bruno wanted a law that fires before a certain seat's turn.

One thing the seats got wrong: Lucan believed a law cannot pay by the number of cities. It can: `(count each city)`. Nobody tested it, because he did not draft it. The clerk is free, and seats use it less than they should.

## Bugs found

Fixed:

- **A schema field order broke every action.** The API makes a reply give fields in schema order, and Lean sorts JSON keys. With a field called `t`, a model that started with it could only write actions whose other fields sort later. So it could not `place`, and it wrote drafts like "x" and "no-op" instead. The field is now called `action`, and a test holds this.
- **The runner hung at exit**, waiting on the turn timer's thread.
- **The turn could be forced by a rival.** See the turn timer in the commit history. Only the server ends a turn now.
- **The law preview was wrong for builds.** It ran the law before the cost was posted. In a check over real games, this would have given wrong figures on 96 of 2,580 builds.
- **The preview for a draft ignored the fee** the proposer is about to pay, so it could differ from the preview at the vote.
- **A preview on the game's very last turn listed rolls** that will not happen.
- **A stale move could land on a later turn** of the same seat, if the timer ended its turn while a request ran. It is now dropped.
- **A rule-based bot's vote could beat a person's click.** The driver now holds votes.

Not fixed, for someone to decide:

- A seat's memory can be wrong and it will believe it. The chronicle is true.
- Claude seats are asked about every offer they could accept, and this is 35 to 41% of the calls and a common complaint. We could ask less, but then a seat misses some trades.
- A seat that ends its turn by passing a batch adds a harmless refused action when a build wins the game.
- The clock is not in the log, so after a restart the turn in progress gets a new deadline. An abandoned table keeps running: the timer ends one turn every 5 minutes until its rounds end.

## Suggestions on balance (nothing here was changed)

- **A 7 does nothing.** This confused every newcomer. It wastes the likeliest roll. Consider a number on a hex, or a rule for it.
- **The end freezes.** Everyone sees every hand, so the table refuses to sell to a leader. Consider hidden hands, or a cost for refusing. This is the top issue for fun.
- **The treasury needs a reason to exist.** A sample law that spends it might teach this.
- **Make the first law cheap or free.** A game seems to need one early law. One free proposal per seat may start the loop.
- **Show when a law's "each round" happens, and what "in proportion" means.** The seats that understood this won.

## Where the data is

`make sim` wrote each game to `results/<run>/`, which git ignores: the event log, talk, clerk memory, seat records, `<code>.summary.json`, and `.jsonl` copies. `scripts/sim_report.py results/<run>` prints a report. `make spectate RESULTS=results/<run>` opens it in the browser, in spectator and replay view.
