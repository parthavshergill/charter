import Charter.Constitution.Promises
import Charter.Proofs.Main
import Charter.Proofs.RenameStep

/-!
# The Charter Constitution

Ten promises, called the commandments. They hold for every valid game and every law that passes
`lawProblems`.

This is the file to read and argue with. Each promise is a theorem about `Engine.step`, the code that
really runs. If a promise is not written here, it is not made.

All ten are proved. `make audit` checks them, and they pass Comparator.

How to read them:

* `Engine.step G s e = .ok s'` means: the engine accepts event `e` in state `s`, and the new state is
  `s'`. `Reachable G s` means: state `s` can really happen in game `G`.
* A seat is a player. An event is one thing a seat does, or the timer ending a turn.
* An entry is one movement of resources. The journal lists the entries, and the books hold the result.

Where to look next:

* `Constitution/Promises.lean` defines the named parts below. `Words.lean` lists the other words.
* `Constitution/Supporting.lean` has six more promises.
* `Constitution/Examples.lean` has full games, and bad steps that the promises reject.
* `docs/process/trusted-surface.md` lists every definition a reader must trust.

What is trusted:

* The Lean kernel and compiler.
* The server, for what these theorems cannot see: who may send an event for a seat, who may send
  `forceEndTurn`, and how the seed is handled, as commandment VIII says. It must also check `G.Valid`
  before it runs a game. Every theorem assumes that, and the engine never checks it.
* SHA-256, to hide the seed, as commandment VIII says. `commitmentOf` hashes a 64-bit seed with no
  salt, so a very large search could find the seed from its fingerprint.

What no theorem covers: the screen. Nothing proves that it shows the true state or sends what a
player chose. A law's `title` means nothing in the game, so the screen must use the law's clauses.
-/

namespace Charter

/-- **I. Nothing from nothing.** The amount of each resource never changes.
* Every change to the books is a written entry. Every entry moved exactly what it says.
* The total of each resource is what the game started with.
* A step only adds to the end of the journal. -/
theorem I_nothing_from_nothing (G : GameDef) (hG : G.Valid) (s : State G)
    (hs : Reachable G s) (r : Res) :
    BooksMatchJournal s ∧
    s.total r = G.stockOf r ∧
    (∀ e s', Engine.step G s e = .ok s' → JournalOnlyGrows s s') :=
  Proofs.I_nothing_from_nothing G hG s (hs.inv hG) r

-- This proof needs neither `hG` nor `hs`. The statement keeps them, so it matches the other nine.
set_option linter.unusedVariables false in
/-- **II. One law for all.** A seat's name makes no difference to the engine. Rename every seat, and
each step gives the same result, with the names changed. This covers laws, dice payouts and deals.

Turn order is renamed too, so going first remains a real difference. This is not a promise of
fairness: a law can still single out a player by what that player holds or has built. -/
theorem II_one_law_for_all (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s)
    (σ : Renaming) (e : Event) :
    (Engine.step G (σ.state s) (σ.event e)).toOption = (Engine.step G s e).toOption.map σ.state :=
  σ.step_toOption_rename s e

/-- **III. Only the majority changes the rules.**
* The laws in force change only by a yes vote on an open law, from a seat in the game that had not
  voted. That vote gives the law more than half of all seats. The change is exactly that law: its
  repeals take effect, and it joins the list, unless all of its clauses act once when it passes. What
  those clauses do happens at that vote, and every other event leaves them out.
* In the actions phase, such a vote is accepted and enacts the law, if the seat is under its action
  limit and the law passes `lawProblems`.
* On an open proposal, no seat votes or signs twice. Every seat there is in the game.
* Each open proposal has its own id. Its id, proposer and body never change.
* A new proposal comes from the seat that sent it, with no votes or signatures.
* A vote or signature on an open proposal is written down exactly, as the seat that sent it.
* A proposal stays open until a yes vote gives its law more than half of all seats, its last
  signature comes, its proposer's next turn starts, or the game ends.
* In the actions phase, any seat in the game that has not voted can vote yes or no on an open law, if
  it is under its action limit.
* Nobody joins or leaves a game. The seats and their order never change.
* An event that does not end the turn adds 1 to its sender's action count, and to no other seat's. A
  turn end resets every count.
* An event that does not end the turn keeps the phase, unless a seat reaches the target and wins.
* Why this counting matters: the rights here and in VI and VII need a seat under its action limit. No
  seat can silence another by using up its actions. -/
theorem III_only_the_majority (G : GameDef) (hG : G.Valid) (s s' : State G)
    (hs : Reachable G s) :
    LawsChangeOnlyByMajority s s' ∧
    MajorityVoteEnacts s ∧
    EachSeatCountsOnce s ∧
    ProposalIdsAreUnique s ∧
    (∀ e, Engine.step G s e = .ok s' → ProposalsKept s s' e) ∧
    AnySeatCanVote s ∧
    (∀ e, Engine.step G s e = .ok s' → SeatsStayFixed s s') ∧
    (∀ e, Engine.step G s e = .ok s' → ActionsAreCountedExactly s s' e) ∧
    (∀ e, Engine.step G s e = .ok s' → PhaseChangesOnlyByTurnOrWin s s' e) :=
  Proofs.III_only_the_majority G hG s s' (hs.inv hG)

/-- **IV. Promises are paid up front.**
* Each running deal always holds enough in deposits to cover the most it could still owe.
* At a round's end, the deals make exactly the payments due. By commandment I, each one is paid in
  full.
* The list of builds that those payments read holds exactly this round's builds. -/
theorem IV_promises_are_paid_up_front (G : GameDef) (hG : G.Valid) (s : State G)
    (hs : Reachable G s) :
    DepositsCoverDebts s ∧
    (∀ e s', Engine.step G s e = .ok s' → EndsTurn s e → s.isLastTurn = true →
      DealsPayWhatIsDue s s') ∧
    (∀ e s', Engine.step G s e = .ok s' → BuildsRecorded s s' e) :=
  Proofs.IV_promises_are_paid_up_front G hG s (hs.inv hG)

/-- **V. Your money is yours.** These rules hold for every accepted step and every entry it makes.
* A new offer's maker is the seat that sent it, and a step never alters an offer.
* Accepting an offer moves exactly the offered goods. Its maker cannot accept it. If it names a seat,
  only that seat can accept it.
* Money enters a deposit only from its owner, at the signature that starts that deal.
* Money leaves a deposit only as a refund or a payment that deal promises. So laws cannot touch it.
* A deal payment comes only from a deposit, on the step that ends a round.
* A refund goes only from a deposit to its owner, when the deal closes.
* Money leaves a seat's own account only for that seat's build, that seat's trade at the exact price
  or agreed amounts, its deposit, or what a law in force says.
* Money leaves the bank or treasury only when the dice pay out, for a bank trade at its exact price,
  or under a law in force.

What you own leaves you only for a stated reason, and this covers pieces too:
* A piece leaves its owner only for that seat's own upgrade, by a law in force at a turn change, or by a
  law's `now` clause at the vote that passes it. A law can do this only at a round's end, on a roll or at
  that vote.
* A turn change leaves exactly the pieces `turnPieces` says, and the vote that passes a law leaves exactly
  what its `now` clauses say. No other event but placing a piece changes any.
* A seat that has a piece always keeps one. -/
theorem V_your_money_is_yours (G : GameDef) (hG : G.Valid) (s s' : State G) (e : Event)
    (hs : Reachable G s) (h : Engine.step G s e = .ok s') :
    OffersKept s s' e ∧
    AcceptedOffersAreExact s s' e ∧
    (∀ x ∈ newEntries s s',
      MoneyEntersDepositOnlyToFundDeal s s' e x ∧
      MoneyLeavesDepositOnlyAsPromised s x ∧
      DealsPayOnlyAtRoundEnd s e x ∧
      RefundsGoToOwnerAtClose s s' x ∧
      MoneyLeavesSeatOnlyFor s s' e x ∧
      MoneyLeavesBankOnlyFor s e x) ∧
    PiecesKept s s' e ∧
    PieceLeavesOnlyFor s s' e ∧
    SeatsKeepAPiece s s' :=
  Proofs.V_your_money_is_yours G hG s s' e (hs.inv hG) h

/-- **VI. Every deal ends.**
* No deal can run past the term agreed when it started.
* A running deal has not passed its last round.
* A deal starts only when every signer has signed.
* A deal keeps its terms and last round until it closes at a round's end or the game ends. A signer's
  exit can only move the last round earlier, to the end of the notice period.
* Any signer can give notice in the actions phase, if it is under its action limit. The deal then
  ends within the notice period.
* When a deal ends, its deposits are empty. Everything unspent has gone back to its owners.
* A build is blocked only by a running deal that the builder signed, with a no-build term for that
  seat and piece.
* A trade is blocked only by a running deal in which one of the two seats promised, as a signer, not
  to trade with the other. The other seat need not have signed.
* The engine rejects accepting an offer, or addressing one, across a trade block. -/
theorem VI_every_deal_ends (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s) :
    DealsStayWithinTerm s ∧
    DealsHaveNotPassedLastRound s ∧
    (∀ e s', Engine.step G s e = .ok s' → DealsKept s s' e) ∧
    SignersCanExit s ∧
    EndedDealsAreEmpty s ∧
    DealsBlockOnlySignersBuilds s ∧
    DealsBlockOnlySignersTrades s ∧
    (∀ e s', Engine.step G s e = .ok s' → BlockedTradesAreRejected s e) :=
  Proofs.VI_every_deal_ends G hG s (hs.inv hG)

/-- **VII. Prices are real.** In the actions phase:
* A build is accepted exactly when it meets the current rules.
* The new piece is added, an upgrade removes the one piece it replaces, and no other piece changes.
* The build charges exactly the current cost and runs the laws that react to it. No other resources
  move, apart from refunds if the build ends the game, which commandment V limits. -/
theorem VII_prices_are_real (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s)
    (p : Seat) (k : PieceKind) (loc : Loc) (hPhase : s.phase = .actions) :
    ((∃ s', Engine.step G s (.move p (.place k loc)) = .ok s') ↔ s.canPlace p k loc = true) ∧
    ∀ s', Engine.step G s (.move p (.place k loc)) = .ok s' →
      s'.pieces = s.placedPieces p k loc ∧
      BuildChargesExactly s s' p k :=
  Proofs.VII_prices_are_real G hG s (hs.inv hG) p k loc hPhase

/-- **VIII. Nobody controls the dice.**
* The game's seed comes from the server's seed and the players' nonces, which are numbers they add.
* The public fingerprint is the SHA-256 hash of that server seed.
* The seed and its fingerprint never change.
* Each roll depends only on the seed and how many rolls came before. So no move, vote or law can
  change a roll.
* No turn can skip its roll. The dice roll exactly when a turn ends and an action turn comes next.

This much is proved. Neither side alone can choose the dice, *assuming* four things. The server
publishes the fingerprint before players add nonces. It uses each player's own nonce, when the player
supplies one. It keeps its seed secret until the game ends. SHA-256 hides the seed. These assumptions
are not proved. This does not claim the rolls are fair. -/
theorem VIII_nobody_controls_the_dice (G : GameDef) (hG : G.Valid) (s s' : State G) (e : Event)
    (hs : Reachable G s) (h : Engine.step G s e = .ok s') :
    SeedMatchesFingerprint s ∧
    s'.seed = s.seed ∧
    s'.seedCommitment = s.seedCommitment ∧
    RollComesFromSeedAlone s s' ∧
    DiceRollExactlyAtTurnChange s s' e :=
  Proofs.VIII_nobody_controls_the_dice G hG s s' e (hs.inv hG) h

/-- **IX. The game cannot stall and always ends.**
* Until the game ends, there is a current seat, and it or the timer can always end the turn.
* The engine accepts no event after the end.
* Turns and events stay within fixed limits, and the game has ended once the turn limit is reached.
  So every game ends after finitely many events if the timer keeps running.
* Every accepted event is counted. A seat at its action limit can only end its turn.
* A turn end adds 1 to the turns taken and moves the game to what comes next: another setup turn, the
  first round, the next seat in this round, a new round, or the end of the game. -/
theorem IX_cannot_stall_always_ends (G : GameDef) (hG : G.Valid) (s : State G)
    (hs : Reachable G s) :
    (s.phase ≠ .ended → s.currentSeat.isSome = true) ∧
    (s.phase ≠ .ended → TimerCanEndTurn s ∧ CurrentSeatCanEndTurn s) ∧
    (s.phase = .ended → NoEventIsAccepted s) ∧
    s.turnsTaken ≤ maxTurns G s.turnOrder.length ∧
    (s.turnsTaken = maxTurns G s.turnOrder.length → s.phase = .ended) ∧
    s.eventsApplied ≤ maxEvents G s.turnOrder.length ∧
    (∀ e s', Engine.step G s e = .ok s' → EveryEventIsCounted s s') ∧
    (∀ e s', Engine.step G s e = .ok s' → ActionLimitIsEnforced s e) ∧
    (∀ e s', Engine.step G s e = .ok s' → EndsTurn s e → TurnMovedOn s s') :=
  Proofs.IX_cannot_stall_always_ends G hG s (hs.inv hG)

/-- **X. What you vote on is what runs.**
* A state can really happen exactly when replaying some list of events gives it. So a replay tool can
  check a result, once the seed is revealed at the end.
* The engine's preview function, `predictNextTurn`, is exact. If a vote enacts a law and the turn then
  ends, by the seat or the timer, the entries are the ones it gives for that roll.
* If other moves happen first, its answer may be out of date, and the screen must say so.
* This covers the function. That the screen shows its result is tested, not proved.
* At a round's end, the deals pay first. Then the laws do exactly what the rule language says.
* When the dice roll, the entries are exactly that roll's payout, the laws reacting to it, and the laws
  reacting to the roll itself. Those last laws fire on every roll, and they act for the seat whose turn
  the roll starts.
* On the last turn of a round, those come after exactly the round-end entries: the deals' payments,
  the laws' entries and the refunds.
* A turn change with no roll makes only those round-end entries, if any. -/
theorem X_what_you_vote_on_is_what_runs (G : GameDef) (hG : G.Valid) :
    ReplayGivesTheGame G ∧
    PreviewIsExact G ∧
    RoundEndPaysDealsFirst G ∧
    RollPaysExactly G ∧
    NoRollPaysOnlyRoundEnd G :=
  Proofs.X_what_you_vote_on_is_what_runs G hG

end Charter
