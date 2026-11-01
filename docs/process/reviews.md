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
- The clerk's sentences, and the clerk's and the Claude seats' handling of replies.
- The whole server, including the turn timer and replaying a game from its log.

Neither proofs nor tests show that the screen always shows the true state, or that the dice are fair. `docs/process/trusted-surface.md` gives the full list.

**Comparator has not been run.** It needs a Linux sandbox. `make audit` does not replace it.
