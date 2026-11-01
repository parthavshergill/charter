# What the reviews found

Charter's promises were written before its engine, and then attacked by reviewers who did not write them. Those reviewers were independent and read-only: they were models that had not written the code, and they could report problems but not change anything. This file records what they found and what changed.

All ten commandments and the five supporting promises are now proved, and `make audit` checks those proofs. A review asks a different question: does the statement say enough? A proof only covers what its statement says.

## Building the engine against the first draft

The first engine and its tests found problems in the draft spec.

| Finding | Effect | Change |
|---|---|---|
| A price could list a resource twice | A seat with 1 timber passed `canPlace` for a price of 2 timber, so commandments I and VII contradicted each other: no engine could meet both | `bundleOk` rejects a resource listed twice |
| "Everyone pays the builder" made the builder pay itself | `Books.post` refuses such an entry, so the whole natural law had to be banned | `settle` drops entries whose source and destination match |
| A deal's build term fired on builds made before the deal started | A deal could owe payment for something that came first | `ActiveDeal` records `startRound` and `builtBefore` |
| The example maps were too small | A seat could end setup with no piece | Larger maps, with setup searched for stuck states |

A statement written by reading it back also failed: `↔` binds looser than `∧`, so commandment VII did not say what its comment said.

## First independent review

This review read the spec with no engine in place. Its main finding was that an engine could steal from players and still satisfy every theorem.

| Finding | Change |
|---|---|
| The journal could shrink, which emptied the checks on new entries | A step only appends to the journal |
| One seat could make a majority, because votes counted entries and not seats | The voter must be seated and must not have voted; no duplicates on open proposals |
| A deal could start on one signature and take a non-signer's money | Every signer must sign, and deposits come from signers only, in the agreed amounts |
| Deal payments could go to anyone | A payment's destination is exactly what the deal says |
| A build could take another player's money, labelled as a refund | A refund can only go from a deposit to its owner, when that deal closes |
| A turn end could add arbitrary entries first | A turn change's entries are stated exactly |
| A finished deal could keep blocking builds, even for seats that never signed | Deals bind only signers, and a running deal has not passed its last round |
| A player's balance had no general protection | Commandment V became "Your money is yours": a list of every way money can leave a seat |
| Whoever picked the seed controlled the dice, and the fingerprint was not tied to the seed | The server commits first, players add nonces, and `commitmentOf` is a real SHA-256 |
| Close seeds gave the same dice, shifted by one roll | `dieAt` scrambles the seed first |
| The winner theorem did not match its docstring | The winner has the most points, and reached the target or the rounds ran out |

It also corrected claims that said too much: "Every law the rule language can express" became "every law that passes `lawProblems`". "One law for all" now says that it is not a promise of fairness. The claim that nobody can act for another seat was removed, because seat identity is the server's job.

One suggestion was declined: a delay before laws take effect. Instant laws are part of the game's drama, and players see a preview before they vote.

## Closing the gaps it left

| Finding | Change |
|---|---|
| A `vote` could pay the voter from the bank, because only money leaving players and deposits was limited | `every_other_event_is_exact` states the entries of every remaining event |
| An engine could reject every deal or every law and keep all its promises | `proposals_are_accepted` and `deals_can_start`, and both full games now run a law and a deal |
| Definition holes let an engine be swapped, and needed a separate check | The holes were removed: the theorems are stated about `Engine.step` directly |

## Second independent review

This review read the statements with no knowledge of the earlier reasoning. It found no statement false for the engine at that point. It found one real bug and one large gap.

**The bug.** A law of 30 nested `forEach` clauses has size 63, under the limit of 64, and passes `lawProblems`. It plans about 2^31 entries at 2 seats, which hangs the server. We reproduced the doubling at depth 16 (65,536 entries). Commandment IX could not see this, because a very slow step still finishes. The fix is the payment cap in the next section.

**The gap.** The theorems pin what money moves, but leave most other state free. An engine could:

- forge an offer from another seat
- add fake votes or signatures, or swap a law's text after people voted
- extend a deal every round, or redirect its payments
- never advance the turn, or return to setup for free pieces
- use up a seat's actions, which makes the liveness promises empty
- fake a build, so that a deal pays for nothing
- let the game continue after someone reaches the target
- reject ordinary votes, which gives one seat a veto

## Hardening the statements

The first plan for the gap was one theorem about every event. We added clauses to each commandment in its place, so each clause is read next to the promise it supports. Later reviews of those clauses found more. Each row is a thing the statements still allowed, and each change is now proved. `Constitution/Examples.lean` also proves that the promises reject bad steps of these kinds.

| What the statements allowed | Change |
|---|---|
| A forged vote or signature, a swapped law, or a proposal that vanished | `ProposalsKept` is exact in both directions. Each proposal after a step is new, or changed only as the event says. Each earlier one stays open unless `ProposalCloses` says it closes |
| A deal extended, redirected, shortened or dropped, or started without every signature | `DealsKept` is exact in both directions, in the same way. Only a signer's exit can change a deal's last round, and only to an earlier one |
| A law that plans too many payments, as in the bug above | A payment cap. `lawProblems` refuses a law that could ask for more than 64 entries on one trigger, or that takes all the laws in force over 128. `limits_hold` states both |
| A forged offer. V's rules for offers applied to each entry of a step, and an offer makes no entries, so V said nothing about it | `OffersKept` and `AcceptedOffersAreExact` now hold for every accepted step |
| Accepting an offer for other amounts, or accepting one's own offer | `AcceptedOffersAreExact`: exactly the offered goods, never by its maker, and only by the seat it names, if it names one |
| Money leaving the bank or treasury for any reason | `MoneyLeavesBankOnlyFor`: a dice payout, a bank trade at its exact price, or a law in force |
| An embargo that a trade ignored, or a block with no deal behind it | `BlockedTradesAreRejected` says the engine rejects a trade across a block. `DealsBlockOnlySignersBuilds` and `DealsBlockOnlySignersTrades` name the running deal and term behind each block |
| Seats joining or leaving | `SeatsStayFixed` |
| One seat using up another seat's actions | `ActionsAreCountedExactly` and `ActionLimitIsEnforced`. This matters because the rights to vote, sign and exit need a seat under its action limit |
| Two open proposals with one id | `ProposalIdsAreUnique` |
| A turn that never moved on, or a return to setup for free pieces | `TurnMovedOn` and `PhaseChangesOnlyByTurnOrWin` |
| A fake build that makes a deal pay for nothing | `BuildsRecorded` |
| A game that continued after a seat reached the target | `the_winner_earned_it` says reaching the target ends the game |
| A rejected vote, which gives one seat a veto | `AnySeatCanVote` |
| A limit on events that meant little, because an event might not be counted | `EveryEventIsCounted` says every accepted event counts, so `maxEvents` and `maxTurns` in commandment IX are real limits. A running game has a current seat. Every game ends after finitely many events if the timer keeps running |
| A claim that neither side can choose the dice, with its assumptions unstated | Commandment VIII separates what is proved from what is assumed. It lists the assumptions, and says they are not proved |

## What the running game showed

These two problems were in the server, not the statements. No theorem could have caught them, because the theorems stop at `Engine.step`.

**The preview disagreed with the proof for builds.** The screen's preview ran the laws reacting to a build on the books before the cost was paid. Commandment VII states the cost first, and then the laws on the books with the cost paid. So a law that reads holdings could show a figure the engine would never produce. The preview now calls the functions the commandments state. `charter-sim --check-previews` plays real games and compares each preview with the entries the engine really made, and `make smoke` runs it. This is a test, not a proof. Commandment X now says that its promise covers the function, and that what the screen shows is only tested.

**A rival could end your turn.** The server had a `force` route and a button that sent `forceEndTurn` for any seated player. The engine cannot see who sends that event, and commandment IX needs it to always work, so who may send it is the server's job. The route and the button are gone. Each turn now has a deadline that the server keeps, and only the server's own timer sends the event. `make smoke` and `make clerk-check` test this. It is not proved.

## Founding laws

A game can now start with laws already in force. Such a law could have skipped the checks a voted law must pass. So `GameDef.Valid` checks each founding law with `lawProblems`, in order, at every allowed number of seats, because what a law can ask for depends on the number of seats. They are enacted in the same way as later laws. The engine and the commandments' statements did not change for this. The Island has no founding laws, so only a tiny game uses them.

`a_founded_game_exists` plays a complete game with a founding law. `tooManyPayments_invalid` shows that a game is rejected if its founding law is within the limit at 2 seats but over it at 6.

## Laws that react to the roll

A 7 paid nobody, so no law could react to it. A new clause, `onRoll`, now runs on every roll. A new number, `rolled`, is the total shown. Each statement that named `harvestEntries` for a law's payment now names `rollEntries`: the harvest, then the laws that react to the roll, planned from the moment after the harvest posted.

| Question | Answer |
|---|---|
| Does a saved game replay the same? | Yes, if it has no `onRoll` law. `no_roll_law_means_harvest_alone` proves that a roll is then the harvest alone. The parser only gained new words. |
| Can a law pay itself as "the dice"? | No. `IsDicePayout` still names `harvestEntries`. A roll law's entries have the reason `lawEffect`, so `AskedForByLaw` is the only way they pass. |
| Who is the actor? | The seat whose turn the roll starts. `RollPaysExactly` now also says `s.nextRoller = s'.currentSeat`, so the definition cannot name the wrong seat. |
| Does the actor always exist? | In a game that goes on, yes. A roll starts an action turn, and commandment IX says that an action turn has a current seat. |
| Can a law change a roll? | No. `rollAt`, `dieAt` and commandment VIII did not change. A law reads the total and nothing more. |
| What does `rolled` mean outside a roll? | 0, as `harvestedAmount` is. `lawProblems` accepts it, as it accepts `harvestedAmount`. The read-back says "0 (no dice are rolled here)". A number is not a transfer's named party or resource, so no check looks inside it. |
| Do the payment caps count it? | Yes, both of them. `Clause.effects` lists the clause. `roll_law_over_the_cap_is_rejected` and `roll_laws_over_the_total_cap_are_rejected` show this. |
| Do the hypotheses hold on a 7? | Yes. `a_seven_moves_money` plays a real game whose first roll is a 7. It pays nobody from the map, and the founding law still moves money. |

The first run in a browser found three weak points, and they are fixed.

| Finding | Change |
|---|---|
| A roll law's payments were minor lines, so the chronicle hid them by default and no caption told them | One line for each roll, which the chronicle and the caption both show |
| The read-back wrote a double comma for three amounts that round down | Amounts that all round down share the words "each rounded down", and halves read as "half of their grain and ore" |
| A sum of holdings read as "7 is less than their grain plus their timber plus their ore" | With three or more goods, it reads as "their grain, timber and ore together is more than 7", which the packs needed too |

## How accurate the law descriptions are

A law's description is Claude's words, and no proof stands behind it. So this was measured once, on real calls. The script is not kept in this repository, so it cannot be run again from here.

The test had 91 different laws: 16 that real games proposed or drafted, 9 sample laws, and 66 written to be awkward: nested `for-each-player` and `if`, shrinking payments, subtraction that stops at zero, `repeal`, `new-piece`, `on-roll`, and piece names that try to give instructions. A separate `claude-opus-5-5` call read each law and its description and flagged errors. I then read the flags, and sorted them into false statements and weak ones. A weak one leaves out something a player might want, such as "or all they have".

| Model and effort | Flagged by Opus | False statements | Weak | No description | Latency in seconds: median, 90th percentile, longest | Mean cost |
|---|---|---|---|---|---|---|
| `claude-haiku-5-5`, `low` | 11 | 5 | 6 | 0 | 1.4, 1.8, 6.0 | $0.00042 |
| `claude-haiku-5-5`, `medium` | 4 | 2 | 2 | 0 | 1.6, 4.4, 8.8 | $0.00052 |
| `claude-haiku-5-5`, `high` | 3 | 0 | 2 | 1 | 4.0, 7.0, 17.5 | $0.00082 |
| `claude-sonnet-5-5`, `low` (the default) | 0 | 0 | 0 | 0 | 1.7, 2.1, 4.6 | $0.00794 |

What these numbers mean, and what they do not:

- `low` was too weak: 5 false statements in 91. An earlier run at `low` also wrote its own corrections into its reply, as in "Wait, that sentence is wrong".
- `medium`'s two false statements were on odd laws: one reads `actor` at a round's end, and one tests `rolled` outside a roll. It made none on the 25 real and sample laws. Its weak flags were a large payment with no "or all they have", and "if they have them" on a real law, which can read as all or nothing.
- `high` used up the 4,000 token limit on one law, and it is slower.
- `claude-sonnet-5-5` at `low` did best, at about 15 times the cost, and its slowest replies were faster. So it is the default. Setting `CHARTER_DESCRIBE_MODEL` and `CHARTER_DESCRIBE_EFFORT` changes it.
- Every piece name that tried to give instructions was treated as a name on this run, at every setting. On an earlier version of the prompt, `low` turned a payment around in the way a name asked.
- This is one sample. The prompt was tuned on most of these laws. The 11 `on-roll` laws and 16 others were written after most of the tuning, and they did about as well. The checker is also a model, and in earlier runs I found false statements that it had missed.

Three changes to what the model reads did the most. Each payment says `from` and `to`, because the model often turned a payment around when it read the bare form. `if` reads `when`, because the model read a second transfer as an "else". And each thing is on its own line.

The price and the time are for the call alone, with its one retry if the reply is too long. Eight real descriptions through the running server came 1.0 seconds after the draft at the median, and 1.8 seconds at the longest.

## Bigger limits

A political economy needs more goods, more laws and longer games. A harvest runs every law once per payment, so the numbers came from timing the worst turn. `make measure` builds that turn: 6 seats, the Island's map, 16 kinds of piece on as many corners as fit, and every law as big as the limits allow, all reacting to each payment.

The first measurement was bad at the old limits: a turn change took 4.4 seconds and one preview took 33 seconds. Three causes explain this, and none of them is in a promise.

| Cause | Change |
|---|---|
| Each entry posted made every later read of the books one step longer | `Books.postAll` writes a list of entries into one table, and `record` keeps a table of the whole books each time the journal passes a multiple of 128 |
| `settle` added up an account's requests once per request | `settleFast` adds them up once |
| `legalMoves` copied the whole journal for each move it tried | It tries moves on a state with an empty journal. `step` never reads the journal |

Each faster function in `Words/Fast.lean` has a `@[csimp]` theorem that proves it equal to the plain one, and the compiler then runs it. Proofs and promises still read the plain definitions. So no promise changed for this, and the Lean kernel checks each equality.

| Limit | Old | New |
|---|---|---|
| `maxResources`, `maxPieceKinds` | 8 | 16 |
| `maxStock` | 200 | 2000 |
| `maxLawsInForce` | 16 | 48 |
| `maxLawSize` | 64 | 128 |
| `maxPlannedEntries` | 64 | 128 |
| `maxPlannedTotal` | 128 | 256 |
| `maxRoundsAllowed` | 30 | 60 |

The total stayed at 256 and not the 512 first tried, because a preview works out about 22 harvests, and at 512 one preview took 840 ms. This also caps how long a journal can grow, and that is the game's memory.

A new limit, `maxReadsTotal` of 8192, caps how many numbers and tests all the laws in force read on one trigger. `limits_hold` states it. Most of a harvest's time goes on these reads. Size and payments did not bound them: a law of 128 nodes reads each node once per seat, and a `forEach` holding only empty `forEach`s plans no payments at all. The parser cannot write that last law, but `lawProblems` now refuses it too.

Measured on the worst turn at the new limits, on the laptop that builds the game: a turn change took 27 ms, the moves a seat can make took 22 ms, and a preview of a law that reacts to harvests took 284 ms. A law that reacts only to a build or a round's end needs no dice, so its preview takes far less, unless the current turn closes the round. A preview runs once per open law and per seat, each time the game changes. The deployed container has a quarter of a CPU, so expect those figures to be several times larger there. This was not measured there.

## Measures

Markets and elections need a law to compare seats. A law still has no way to name a seat, so a measure gives a number and never a seat. `total-over` adds a number up over every seat that passes a test, and `most-over` and `least-over` give the highest and lowest. A law then compares each seat with that value, so a tie simply means that several seats match. Two more numbers came with them: division by a computed number, and the current round.

| Question | Answer |
|---|---|
| Does commandment II still hold in the same words? | Yes. Its statement did not change. `measured_rename` shows that a measure gives the same values, in the same order, in a renamed game. Inside a measure, `each` is bound to each seat in turn order, which is renamed too. |
| Is there new state? | No. A measure reads what is already there. |
| Could nested measures stall a turn? | No. `maxReadsTotal` counts a measure's contents once per seat, so five levels are refused. `nested_measures_over_the_cap_are_rejected` shows this. The payment caps did not need to change, because a measure asks for no payment. |
| Is a preview still exact? | Yes. A preview calls the same functions, and `PreviewIsExact` needed only the fact that a vote does not change the round. |
| What does dividing by zero do? | A computed zero gives 0, as in Lean. A law that writes a literal 0 below a division is refused, as it was before. |
| Why keep the fixed `div`? | Removing it would have meant editing Not Catan's laws. The text `(/ a 2)` still reads as the fixed kind, and `(/ a b)` reads as the computed kind, so a player sees one word. |
| What is the round on a roll that starts a new round? | The new round. A roll comes after the round's end and belongs to the next turn. The statements still name `rollEntries`, which reads `State.atRoll`. `IsDicePayout` did not change, because the bank's payments do not read the round. `the_round_moves_money` plays this. |
| Does a saved game replay the same? | Yes, if it has no new words. `no_roll_law_means_harvest_alone` now reads the harvest from `atRoll`, but no old law can read the round. The parser only gained new words. |

## Declarations

An auction or an election needs a seat to say a number that a law can read. The one sentence is: each seat has one public number per resource, which it can change on its turn and which clears when the round ends.

| Question | Answer |
|---|---|
| Why a move? | A move inherits "on your own turn". It counts against the action limit, and `ActionsAreCountedExactly` and the rest cover it with no new words. |
| What can a forged declaration do? | Nothing. `DeclarationsKept` says that a number changes only by that seat's own accepted declaration, or by clearing at a round's end. `a_forged_declaration_is_rejected` and `a_foreign_declaration_is_rejected` show both sides. |
| What does a declaration change? | `every_other_event_is_exact` states the whole new state. One number, the sender's action count and the count of events change. Nothing else does, so it moves no resources and writes no entry. |
| Does it read another seat's secret? | No. All numbers are public, and everyone's view has them. |
| When does it clear? | After the round-end laws run, and before the roll that starts the next round. `State.atRoll` clears it for that roll, as it sets the new round. The turn change then clears it in the state. If the last round ends, it clears too. If a seat reaches the target during a round, the game ends and the numbers stay, and nothing reads them. |
| Does commandment II hold? | Yes, in the same words. `declareBody_rename` is the new case. A declaration names no seat but its sender, and renaming carries the numbers with the seats. |
| Is a preview still exact? | Yes, for the state it is given. Declarations can change after that. So when a law reads them, the screen says the figures hold if declarations stay as they are. |
| How large can a number be? | `maxDeclared`, which is `maxStock`. A larger number could mean nothing, as no seat could hold that much. |
| Does `legalMoves` list it? | No, as with offers. Its contents are free. The view has its own `can` field, from asking `Engine.step`. |
| Does a saved game replay the same? | Yes. A game with no declarations has every number at 0, and no old law reads them. |

`an_auction_settles` plays the worked auction, with a declared bid, the most, and a test that a bid can be paid. `an_auction_tie_is_shared` shows the tie: both seats pay, and each gets half. A bid above what a seat holds does not count in that law. A law need not say this. Without such a test, a seat that bids more than it holds pays what it has and still gets the goods, because a payment shrinks in proportion. The clerk's auction example has no such test, because the request does not ask for one.

## No fee to propose

A law used to cost its proposer a fee. So a law that drained everyone could never be repealed: nobody could pay to propose the repeal. The fee is gone. Any seat can always propose, subject only to the limits on open proposals and actions. Each seat can still have only 2 proposals open.

This is a strengthening of V, because one reason money could leave a seat went away. Statements changed:

| Statement | Before | After |
|---|---|---|
| `MoneyLeavesSeatOnlyFor` | build, trade, law fee, deposit, or a law in force | build, trade, deposit, or a law in force |
| `every_other_event_is_exact` | proposing a law makes exactly `lawFeeEntries G seat` | proposing a law makes `[]` |
| `proposals_are_accepted` | accepted exactly when `lawProblems G s L = [] ∧ s.affords seat G.lawFee = true` | accepted exactly when `lawProblems G s L = []` |

`a_ruined_seat_can_ask_for_a_repeal` plays this, and `charging_to_propose_is_rejected` rejects a charge. A saved game where a law was proposed no longer replays the same way, and only test tables exist. On start, the server leaves out such a log and says which one, as `docs/deploy.md` describes.

## How the checks work

- **Axiom audit:** `make audit` fails if any theorem in a `Charter` module rests on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. So a `sorry` fails it. It also replays the proofs through `leanchecker`, and scans for banned constructs.
- **Statement lock:** `make audit` also fails if a file that states the promises or defines their words has changed. Changing the lock needs the owner's approval.
- **Claim checker:** `Charter/EngineTests.lean` tests each commandment, as far as it can be computed, on every accepted step of concrete and random games.
- **Mutation testing:** this broke the engine on purpose to confirm the tests noticed. It is not kept in this repository, so it cannot be run again from here.

## What is only tested

No theorem covers these. Tests check them, on the cases tried.

- That the hash in `Charter/Sha256.lean` is the real SHA-256.
- The exact entries of a bank trade and a setup placement. Commandment V limits what these can take from a seat.
- `legalMoves`, which the screen uses.
- That every seat can place its setup pieces. On the Island, a road can be blocked at 4 seats, and the game goes on without it.
- That the screen shows the preview's result, and the preview's build cases.
- A deal's sentences, and the clerk's, the description call's and the Claude seats' handling of replies.
- The whole server, including the turn timer and replaying a game from its log.

Neither proofs nor tests show that the screen always shows the true state, or that the dice are fair. `docs/process/trusted-surface.md` gives the full list.

**Comparator has not been run.** It needs a Linux sandbox. `make audit` does not replace it.
