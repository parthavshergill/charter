import Charter.Engine

/-!
# The parts of the promises

`Charter/Constitution.lean` states ten promises. A long promise is split here into named parts, so
that it reads like a list. Each part is one idea.

`Engine.step G s e = .ok s'` means: the engine accepts event `e` in state `s`, and the new state is
`s'`. The other words are defined in `Charter/Words`.
-/

namespace Charter

variable {G : GameDef}

/-! ## How a game runs -/

/-- `s` can really happen: it is a new game, or an accepted event after such a state. -/
inductive Reachable (G : GameDef) : State G → Prop
  | start (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
      minSeats ≤ seats → seats ≤ maxSeats → nonces ≠ [] →
      Reachable G (initialState G seats serverSeed nonces)
  | next {s s' : State G} (e : Event) :
      Reachable G s → Engine.step G s e = .ok s' → Reachable G s'

/-- A game state with proof that it is reachable. A server that stores only this type can hold no
other state. Nothing here forces a server to store it. -/
abbrev Game (G : GameDef) := { s : State G // Reachable G s }

/-- `e` ends the current turn. -/
def EndsTurn {G : GameDef} (s : State G) : Event → Prop
  | .move p .endTurn => s.currentSeat = some p
  | .forceEndTurn => True
  | _ => False

/-- The entries a step adds. -/
def newEntries {G : GameDef} (s s' : State G) : List Entry :=
  s'.journal.drop s.journal.length

/-- This event is the vote that passes this law: a yes on an open law that gives it more than half of all
seats, and the law still passes `lawProblems`. -/
def LawPasses {G : GameDef} (s : State G) (e : Event) (L : Law) : Prop :=
  ∃ seat id p, e = .vote seat id true ∧ s.openProposal? id = some p ∧ p.body = .law L ∧
    (p.withVote seat true).hasMajority s.turnOrder.length ∧ lawProblems G s L = []

/-! ## I. Nothing from nothing -/

/-- The books are exactly what the journal's entries, posted in order, give from the start. -/
def BooksMatchJournal (s : State G) : Prop :=
  (genesisBooks G).postAll s.journal = some s.books

/-- The old journal is the start of the new one. Nothing is rewritten or removed. -/
def JournalOnlyGrows (s s' : State G) : Prop := s.journal <+: s'.journal

/-! ## III. Only the majority changes the rules -/

/-- If a step changes the laws in force, the event is a yes vote on an open law, from a seat in the
game that had not voted. That vote gave the law more than half of all seats, and the laws changed by
exactly that law. `enact` says that a law of only `now` clauses does not join them. -/
def LawsChangeOnlyByMajority (s s' : State G) : Prop :=
  ∀ e, Engine.step G s e = .ok s' → s'.laws ≠ s.laws →
    ∃ seat id p L,
      e = .vote seat id true ∧ s.openProposal? id = some p ∧ p.body = .law L ∧
      seat ∈ s.turnOrder ∧ (p.votes.map (·.1)).contains seat = false ∧
      (p.withVote seat true).hasMajority s.turnOrder.length ∧
      s'.laws = enact s.laws id L

/-- In the actions phase, the vote that gives a law more than half of all seats is accepted and enacts
it, if the seat is under its action limit and the law passes `lawProblems`. -/
def MajorityVoteEnacts (s : State G) : Prop :=
  ∀ seat id p L,
    s.phase = .actions → seat ∈ s.turnOrder → s.openProposal? id = some p →
    p.body = .law L → (p.votes.map (·.1)).contains seat = false →
    s.actionsThisTurn seat < maxActionsPerTurn →
    (p.withVote seat true).hasMajority s.turnOrder.length → lawProblems G s L = [] →
    ∃ s'', Engine.step G s (.vote seat id true) = .ok s'' ∧ s''.laws = enact s.laws id L

/-- On an open proposal, no seat appears twice among the votes or the signatures, and every seat
there is in the game. -/
def EachSeatCountsOnce (s : State G) : Prop :=
  ∀ p ∈ s.openProposals, (p.votes.map (·.1)).Nodup ∧ p.signed.Nodup ∧
    (∀ x ∈ p.votes, x.1 ∈ s.turnOrder) ∧ ∀ i ∈ p.signed, i ∈ s.turnOrder

/-- Each open proposal has its own id. -/
def ProposalIdsAreUnique (s : State G) : Prop := (s.openProposals.map (·.id)).Nodup

/-- An open proposal after a step, if it stays open. Only a vote or a signature on it changes it. -/
def proposalAfter (e : Event) (p : OpenProposal) : OpenProposal :=
  match e with
  | .vote seat id yes => if id = p.id then p.withVote seat yes else p
  | .sign seat id => if id = p.id then { p with signed := p.signed ++ [seat] } else p
  | _ => p

/-- This step closes this open proposal, in a game that goes on: the vote that gives a law more than
half of all seats, the last signature, or the turn end that starts its proposer's next turn. -/
def ProposalCloses {G : GameDef} (s s' : State G) (e : Event) (p : OpenProposal) : Prop :=
  (∃ seat L, e = .vote seat p.id true ∧ p.body = .law L ∧
    (p.withVote seat true).hasMajority s.turnOrder.length) ∨
  (∃ seat d, e = .sign seat p.id ∧ p.body = .deal d ∧ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) ∨
  (EndsTurn s e ∧ (nextStage s).rolls = true ∧ s'.currentSeat = some p.by_)

/-- Open proposals change only as the event says. Each one after a step is new, with no votes or
signatures, or is an earlier one changed only by `proposalAfter`. Each earlier one stays open unless
`ProposalCloses` says it closes, or the game ended, which closes them all. -/
def ProposalsKept {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  (∀ q ∈ s'.openProposals,
    (∃ seat, e = .propose seat q.body ∧ q.id = s.nextProposalId ∧ q.by_ = seat ∧
      q.votes = [] ∧ q.signed = []) ∨
    ∃ p ∈ s.openProposals, q = proposalAfter e p) ∧
  (∀ p ∈ s.openProposals, s'.phase ≠ .ended →
    (ProposalCloses s s' e p → ∀ q ∈ s'.openProposals, q.id ≠ p.id) ∧
    (¬ ProposalCloses s s' e p → proposalAfter e p ∈ s'.openProposals)) ∧
  (s'.phase = .ended → s'.openProposals = [])

/-- In the actions phase, any seat in the game that has not voted can vote yes or no on an open law,
if it is under its action limit. -/
def AnySeatCanVote (s : State G) : Prop :=
  ∀ seat id p L yes,
    s.phase = .actions → seat ∈ s.turnOrder → s.openProposal? id = some p →
    p.body = .law L → (p.votes.map (·.1)).contains seat = false →
    s.actionsThisTurn seat < maxActionsPerTurn →
    ∃ s'', Engine.step G s (.vote seat id yes) = .ok s''

/-- Nobody joins or leaves a game: the seats and their order never change. -/
def SeatsStayFixed (s s' : State G) : Prop := s'.turnOrder = s.turnOrder

/-- A declared number changes only in two ways. A seat's own declaration, accepted on its own turn for a
real resource and within the limit, changes that one number. The end of a round clears them all. So
nobody can declare for another seat. -/
def DeclarationsKept {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  (∀ p r n, e = .move p (.declare r n) →
    s.phase = .actions ∧ s.currentSeat = some p ∧ G.isRes r = true ∧ n ≤ maxDeclared ∧
    ∀ q x, s'.declared q x = if q = p ∧ x = r then n else s.declared q x) ∧
  (EndsTurn s e → s.isLastTurn = true → ∀ q x, s'.declared q x = 0) ∧
  ((∀ p r n, e ≠ .move p (.declare r n)) → ¬ (EndsTurn s e ∧ s.isLastTurn = true) →
    s'.declared = s.declared)

/-- The seat an event speaks for. The timer's event speaks for no seat. -/
def senderOf : Event → Option Seat
  | .move p _ => some p
  | .propose p _ => some p
  | .vote p _ _ => some p
  | .sign p _ => some p
  | .exit p _ => some p
  | .forceEndTurn => none

/-- The engine looks for a winner after this event: a move other than ending a turn, or a vote. -/
def LooksForWinner : Event → Prop
  | .move _ .endTurn => False
  | .move .. => True
  | .vote .. => True
  | _ => False

/-- This step writes no entries, unless it ended the game, and then it writes only the refunds. -/
def NoEntriesUnlessEnded (s s' : State G) : Prop :=
  (s'.phase = .ended → newEntries s s' = s.deals.flatMap s.refundEntries) ∧
  (s'.phase ≠ .ended → newEntries s s' = [])

/-- A vote writes exactly what passing a law says, and nothing if it passes none. If the game ends, the
refunds come after. -/
def VoteWritesExactly {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  ∃ es, (∀ L, LawPasses s e L → es = s.decreeEntries L) ∧ ((∀ L, ¬ LawPasses s e L) → es = []) ∧
    (s'.phase = .ended → newEntries s s' = es ++ s.deals.flatMap (s.afterPosting es).refundEntries) ∧
    (s'.phase ≠ .ended → newEntries s s' = es)

/-- An accepted event that does not end the turn adds 1 to its sender's action count and leaves every
other seat's count alone. A turn end resets every count to 0. -/
def ActionsAreCountedExactly (s s' : State G) (e : Event) : Prop :=
  (EndsTurn s e → ∀ q, s'.actionsThisTurn q = 0) ∧
  (¬ EndsTurn s e → ∃ p, senderOf e = some p ∧ ∀ q,
    s'.actionsThisTurn q = if q = p then s.actionsThisTurn q + 1 else s.actionsThisTurn q)

/-- A majority passed a law that ends the game. -/
def MajorityEndedTheGame (s : State G) : Prop :=
  ∃ x ∈ s.laws, x.2.clauses.any Clause.isEndGame = true

/-- An accepted event that does not end the turn keeps the phase, unless a seat is now at the target or a
majority has ended the game, either of which ends it. -/
def PhaseChangesOnlyByTurnOrWin (s s' : State G) (e : Event) : Prop :=
  ¬ EndsTurn s e → s'.phase = s.phase ∨
    (s'.phase = .ended ∧
      ((∃ p ∈ s'.turnOrder, G.targetPoints ≤ s'.pointsOf p) ∨ MajorityEndedTheGame s'))

/-! ## IV. Promises are paid up front -/

/-- Each running deal holds enough in deposits to cover the most it could still owe. -/
def DepositsCoverDebts (s : State G) : Prop :=
  ∀ d ∈ s.deals, ∀ i r, s.worstCase d i r ≤ s.balance (.deposit d.id i) r

/-- The deal payments in this step are exactly the payments due. -/
def DealsPayWhatIsDue (s s' : State G) : Prop :=
  (newEntries s s').filter (·.reason == .dealPayment) = s.duePayments

/-- The list of this round's builds, which deal payments read. A build in the actions phase adds
exactly itself. A new round empties the list. Nothing else changes it. -/
def BuildsRecorded {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  (∀ p k loc, e = .move p (.place k loc) → s.phase = .actions →
    s'.builtThisRound = s.builtThisRound ++ [(p, k)]) ∧
  (EndsTurn s e → nextStage s = .newRound → s'.builtThisRound = []) ∧
  ((s.phase = .actions → ∀ p k loc, e ≠ .move p (.place k loc)) →
    (EndsTurn s e → nextStage s ≠ .newRound) → s'.builtThisRound = s.builtThisRound)

/-! ## V. Your money is yours

`x` is one entry that a step makes. Most definitions here limit one kind of entry. -/

/-- Each offer after a step was already there, unchanged, or is new, and a new offer's maker is the
seat that sent it. So nobody can make an offer in another seat's name. -/
def OffersKept {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  ∀ o ∈ s'.offers,
    o ∈ s.offers ∨
    ∃ to give get, e = .move o.src (.offer to give get) ∧ o = ⟨s.nextOfferId, o.src, to, give, get⟩

/-- Accepting an offer moves exactly the offered goods, and then any refunds if the goods put a seat at the
target and the game ends. Its maker cannot accept it. If it names a seat, only that seat can accept it. -/
def AcceptedOffersAreExact (s s' : State G) (e : Event) : Prop :=
  ∀ p id o, e = .move p (.accept id) → s.offers.find? (·.id == id) = some o →
    p ≠ o.src ∧ (o.to = none ∨ o.to = some p) ∧
    ∃ refunds, newEntries s s' = offerEntries o p ++ refunds ∧
      (∀ x ∈ refunds, x.reason = .refund) ∧ (refunds = [] ∨ s'.phase = .ended)

/-- This entry funds a new deal. The event is the signature that starts the deal as id `k`, everyone
has now signed, `i` is a signer, and the deal lists this deposit. -/
def FundsDeal {G : GameDef} (s s' : State G) (e : Event) (x : Entry) (k : Nat) (i : Seat) : Prop :=
  x.src = .player i ∧ x.dst = .deposit k i ∧ x.reason = .setDeposit ∧
  ∃ seat id p d,
    e = .sign seat id ∧ s.openProposal? id = some p ∧ p.body = .deal d ∧
    k = s.dealsStarted ∧ (∃ a ∈ s'.deals, a.id = k ∧ a.deal = d) ∧
    i ∈ d.signers ∧ (∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) ∧
    (i, x.res, x.amount) ∈ d.deposits

/-- Money enters a deposit only to fund a deal, from its owner. -/
def MoneyEntersDepositOnlyToFundDeal (s s' : State G) (e : Event) (x : Entry) : Prop :=
  ∀ k i, x.dst = .deposit k i → FundsDeal s s' e x k i

/-- Money leaves a deposit only as a refund, or as a payment that deal promises: the same payer,
resource, amount and payee. -/
def MoneyLeavesDepositOnlyAsPromised (s : State G) (x : Entry) : Prop :=
  ∀ k i, x.src = .deposit k i →
    x.reason = .refund ∨
    (x.reason = .dealPayment ∧ ∃ d ∈ s.deals, d.id = k ∧ ∃ p ∈ d.deal.allPays,
      p.src = i ∧ p.res = x.res ∧ p.amount = x.amount ∧ x.dst = p.dst.account)

/-- A deal payment comes only from a deposit, on the step that ends the last turn of a round. -/
def DealsPayOnlyAtRoundEnd (s : State G) (e : Event) (x : Entry) : Prop :=
  x.reason = .dealPayment → EndsTurn s e ∧ s.isLastTurn = true ∧ ∃ k i, x.src = .deposit k i

/-- A refund goes only from a deposit to its owner, and only when that deal closes. -/
def RefundsGoToOwnerAtClose (s s' : State G) (x : Entry) : Prop :=
  x.reason = .refund → ∃ k i, x.src = .deposit k i ∧ x.dst = .player i ∧
    (∃ d ∈ s.deals, d.id = k) ∧ ∀ d' ∈ s'.deals, d'.id ≠ k

/-- This entry is seat `i` paying the current cost of its own build. -/
abbrev PaysForOwnBuild (s : State G) (e : Event) (x : Entry) (i : Seat) : Prop :=
  x.reason = .cost ∧ ∃ k loc, e = .move i (.place k loc) ∧ x ∈ s.costEntries i k

/-- This entry is part of seat `i`'s own trade: with the bank at its exact price, or an accepted offer
at exactly the agreed amounts. -/
abbrev PaysInOwnTrade (s : State G) (e : Event) (x : Entry) (i : Seat) : Prop :=
  x.reason = .trade ∧
    ((∃ give get, e = .move i (.bankTrade give get) ∧ x ∈ s.bankTradeEntries i give get) ∨
     (∃ p id o, e = .move p (.accept id) ∧ s.offers.find? (·.id == id) = some o ∧
       (i = o.src ∨ i = p) ∧ x ∈ offerEntries o p))

/-- A law asks for this entry: a law in force reacting to a build, at a round's end, to the dice payout or
to the roll itself, or a law's `now` clause at the vote that passes it. -/
abbrev AskedForByLaw (s : State G) (e : Event) (x : Entry) : Prop :=
  x.reason = .lawEffect ∧
    ((∃ b k loc, e = .move b (.place k loc) ∧
       x ∈ lawEntries (s.afterPosting (s.costEntries b k)) (.build b k)) ∨
     (EndsTurn s e ∧
       (x ∈ s.roundEndLawEntries ∨
        x ∈ rollEntries s.afterRoundEnd (rollAt G s.seed s.rollsMade))) ∨
     (∃ L, LawPasses s e L ∧ x ∈ s.decreeEntries L))

/-- Money leaves a seat's own account only for that seat's build, trade or deposit, or for what a law in
force says. -/
def MoneyLeavesSeatOnlyFor (s s' : State G) (e : Event) (x : Entry) : Prop :=
  ∀ i, x.src = .player i →
    PaysForOwnBuild s e x i ∨
    PaysInOwnTrade s e x i ∨
    (∃ k, FundsDeal s s' e x k i) ∨
    AskedForByLaw s e x

/-- This entry is part of the payout for the dice roll of the turn that is starting. -/
abbrev IsDicePayout (s : State G) (e : Event) (x : Entry) : Prop :=
  x.reason = .harvest ∧ EndsTurn s e ∧
    x ∈ harvestEntries s.afterRoundEnd (rollAt G s.seed s.rollsMade)

/-- This entry is part of a bank trade at its exact price. -/
abbrev IsBankTradeAtPrice (s : State G) (e : Event) (x : Entry) : Prop :=
  x.reason = .trade ∧ ∃ p give get,
    e = .move p (.bankTrade give get) ∧ x ∈ s.bankTradeEntries p give get

/-- Money leaves the bank or the treasury only when the dice pay out, for a bank trade at its exact
price, or for what a law in force says. -/
def MoneyLeavesBankOnlyFor (s : State G) (e : Event) (x : Entry) : Prop :=
  (x.src = .bank ∨ x.src = .treasury) →
    IsDicePayout s e x ∨ IsBankTradeAtPrice s e x ∨ AskedForByLaw s e x

/-- What a step does to the pieces. A turn change leaves exactly what the laws in force say. The vote that
passes a law leaves exactly what its `now` clauses say. Any other event except placing a piece changes none. -/
def PiecesKept {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  (EndsTurn s e → s'.pieces = s.turnPieces (rollAt G s.seed s.rollsMade)) ∧
  (∀ L, LawPasses s e L → s'.pieces = applyOrders s.rules (s.decreeOrders L) s.pieces) ∧
  (¬ EndsTurn s e → (∀ p k loc, e ≠ .move p (.place k loc)) → (∀ L, ¬ LawPasses s e L) → s'.pieces = s.pieces)

/-- What you own leaves you only for a stated reason: your own upgrade, a law in force that asked for it at a
turn change, or a law's `now` clause at the vote that passes it. -/
def PieceLeavesOnlyFor {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  ∀ x ∈ s.pieces, x ∉ s'.pieces →
    (∃ k loc, e = .move x.owner (.place k loc)) ∨
    (EndsTurn s e ∧ ∃ L ∈ s.laws, L.2.clauses.any Clause.movesPieces = true) ∨
    (∃ L, LawPasses s e L ∧ L.clauses.any Clause.movesPieces = true)

/-- A seat that has a piece still has one after any step. A seat with no pieces could never build again. -/
def SeatsKeepAPiece (s s' : State G) : Prop :=
  ∀ q, (∃ x ∈ s.pieces, x.owner = q) → ∃ x ∈ s'.pieces, x.owner = q

/-! ## VI. Every deal ends -/

/-- A running deal started no later than now, and its last round is within the term agreed. -/
def DealsStayWithinTerm (s : State G) : Prop :=
  ∀ d ∈ s.deals, d.startRound ≤ s.round ∧ d.lastRound + 1 ≤ d.startRound + d.deal.rounds

/-- A running deal has not passed its last round. -/
def DealsHaveNotPassedLastRound (s : State G) : Prop :=
  ∀ d ∈ s.deals, s.round ≤ d.lastRound

/-- A running deal after a step, if it keeps running. Only a signer's exit from this deal changes it,
and that sets its last round to the earlier of its old last round and the notice period's end. -/
def dealAfter {G : GameDef} (s : State G) (e : Event) (d : ActiveDeal) : ActiveDeal :=
  match e with
  | .exit seat id =>
    if id = d.id ∧ seat ∈ d.deal.signers then
      { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
    else d
  | _ => d

/-- This step closes this running deal, in a game that goes on: it ends the last turn of the round,
and the deal is due to close. -/
def DealCloses {G : GameDef} (s : State G) (e : Event) (d : ActiveDeal) : Prop :=
  EndsTurn s e ∧ s.isLastTurn = true ∧ d ∈ s.closingDeals

/-- Running deals change only as the event says. Each one after a step is the one a signature just
started, with every signer now signed, or an earlier one changed only by `dealAfter`. Each earlier one
keeps running unless `DealCloses` says it closes, or the game ended, which closes them all. So nothing
else can shorten or remove a deal. -/
def DealsKept {G : GameDef} (s s' : State G) (e : Event) : Prop :=
  (∀ d' ∈ s'.deals,
    (∃ seat id p d, e = .sign seat id ∧ s.openProposal? id = some p ∧ p.body = .deal d ∧
      seat ∈ d.signers ∧ (∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) ∧
      d' = { id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
             startRound := s.round, builtBefore := s.builtThisRound.length }) ∨
    ∃ d ∈ s.deals, d' = dealAfter s e d) ∧
  (∀ d ∈ s.deals, s'.phase ≠ .ended →
    (DealCloses s e d → ∀ d' ∈ s'.deals, d'.id ≠ d.id) ∧
    (¬ DealCloses s e d → dealAfter s e d ∈ s'.deals)) ∧
  (s'.phase = .ended → s'.deals = [])

/-- Any signer can give notice in the actions phase, if it is under its action limit. The deal then
ends within the notice period. -/
def SignersCanExit (s : State G) : Prop :=
  ∀ d ∈ s.deals, ∀ i ∈ d.deal.signers, s.phase = .actions →
    s.actionsThisTurn i < maxActionsPerTurn →
    ∃ s', Engine.step G s (.exit i d.id) = .ok s' ∧
      ∀ d' ∈ s'.deals, d'.id = d.id → d'.lastRound ≤ s.round + d.deal.exitNotice

/-- When a step ends a deal, every deposit of that deal is empty. -/
def EndedDealsAreEmpty (s : State G) : Prop :=
  ∀ e s', Engine.step G s e = .ok s' → ∀ d ∈ s.deals, (∀ d' ∈ s'.deals, d'.id ≠ d.id) →
    ∀ i r, s'.balance (.deposit d.id i) r = 0

/-- If a build is blocked, a running deal that the builder signed says so, in a no-build term of its
own. -/
def DealsBlockOnlySignersBuilds (s : State G) : Prop :=
  ∀ p k loc, s.blockedByDeal p k loc = true →
    ∃ d ∈ s.deals, p ∈ d.deal.signers ∧ ∃ spots, Term.noBuild p k spots ∈ d.deal.terms

/-- If a trade is blocked, a running deal says so: a signer of it promised not to trade with the other
seat. The other seat need not have signed. -/
def DealsBlockOnlySignersTrades (s : State G) : Prop :=
  ∀ a b, s.tradeBlocked a b = true →
    ∃ d ∈ s.deals, ∃ x y, Term.noTrade x y ∈ d.deal.terms ∧ x ∈ d.deal.signers ∧
      ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- A trade block really stops a trade. An accepted step never takes up an offer across a block, and
never makes an addressed offer across one. -/
def BlockedTradesAreRejected (s : State G) (e : Event) : Prop :=
  (∀ p id o, e = .move p (.accept id) → s.offers.find? (·.id == id) = some o →
    s.tradeBlocked p o.src = false) ∧
  (∀ p q give get, e = .move p (.offer (some q) give get) → s.tradeBlocked p q = false)

/-! ## VII. Prices are real -/

/-- The entries of this build are its exact cost, then what the laws do in reaction, then any refunds.
There are refunds only if the build ended the game. -/
def BuildChargesExactly (s s' : State G) (p : Seat) (k : PieceKind) : Prop :=
  ∃ refunds, newEntries s s' =
      s.costEntries p k ++ lawEntries (s.afterPosting (s.costEntries p k)) (.build p k) ++ refunds ∧
    (∀ x ∈ refunds, x.reason = .refund) ∧
    (refunds = [] ∨ s'.phase = .ended)

/-! ## VIII. Nobody controls the dice -/

/-- The game's seed comes from the server's seed and the players' nonces, and the public fingerprint
is the fingerprint of that same server seed. -/
def SeedMatchesFingerprint (s : State G) : Prop :=
  ∃ serverSeed nonces, s.seed = combineSeed serverSeed nonces ∧
    s.seedCommitment = commitmentOf serverSeed

/-- A step either leaves the dice alone, or makes the next roll, whose value depends only on the seed
and how many rolls came before. -/
def RollComesFromSeedAlone (s s' : State G) : Prop :=
  (s'.rollsMade = s.rollsMade ∧ s'.lastRoll = s.lastRoll) ∨
  (s'.rollsMade = s.rollsMade + 1 ∧ s'.lastRoll = some (rollAt G s.seed s.rollsMade))

/-- The dice roll exactly when a turn ends and an action turn comes next. -/
def DiceRollExactlyAtTurnChange (s s' : State G) (e : Event) : Prop :=
  (EndsTurn s e ∧ (nextStage s).rolls = true) ↔ s'.rollsMade = s.rollsMade + 1

/-! ## IX. The game cannot stall and always ends -/

/-- The server's timer can always end the current turn. -/
def TimerCanEndTurn (s : State G) : Prop :=
  ∃ s', Engine.step G s .forceEndTurn = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1

/-- The current seat can always end its turn. -/
def CurrentSeatCanEndTurn (s : State G) : Prop :=
  ∀ p, s.currentSeat = some p →
    ∃ s', Engine.step G s (.move p .endTurn) = .ok s' ∧ s'.turnsTaken = s.turnsTaken + 1

/-- The engine accepts no event in this state. -/
def NoEventIsAccepted (s : State G) : Prop :=
  ∀ e, (Engine.step G s e).toOption = none

/-- The turns taken go up by 1, and the game moves to what `nextStage` says comes next: another setup
turn, the first round, the next seat in this round, a new round, or the end of the game. -/
def TurnMovedOn {G : GameDef} (s s' : State G) : Prop :=
  s'.turnsTaken = s.turnsTaken + 1 ∧
  match nextStage s with
  | .setupTurn i => s'.phase = .setup ∧ s'.turnIndex = i ∧ s'.round = s.round
  | .firstRound => s'.phase = .actions ∧ s'.turnIndex = 0 ∧ s'.round = s.round
  | .sameRound i => s'.phase = .actions ∧ s'.turnIndex = i ∧ s'.round = s.round
  | .newRound => s'.phase = .actions ∧ s'.turnIndex = 0 ∧ s'.round = s.round + 1
  | .gameOver => s'.phase = .ended

/-- Every accepted event is counted. -/
def EveryEventIsCounted (s s' : State G) : Prop := s'.eventsApplied = s.eventsApplied + 1

/-- An accepted event that does not end the turn came from a seat under its action limit. So a seat at
its limit can only end its turn. -/
def ActionLimitIsEnforced (s : State G) (e : Event) : Prop :=
  ¬ EndsTurn s e → ∃ p, senderOf e = some p ∧ s.actionsThisTurn p < maxActionsPerTurn

/-! ## X. What you vote on is what runs -/

/-- A state can really happen exactly when replaying some list of events gives it. -/
def ReplayGivesTheGame (G : GameDef) : Prop :=
  ∀ s, Reachable G s ↔ ∃ seats serverSeed nonces events,
    minSeats ≤ seats ∧ seats ≤ maxSeats ∧ Engine.replay G seats serverSeed nonces events = .ok s

/-- If a vote passes a law and the turn then ends, the entries are the ones `predictNextTurn` gives
for that roll, from the state with the law passed. This is about the function, not the screen. -/
def PreviewIsExact (G : GameDef) : Prop :=
  ∀ (s s₁ s₂ : State G) seat id L roll e,
    Reachable G s → Engine.step G s (.vote seat id true) = .ok s₁ → LawPasses s (.vote seat id true) L →
    EndsTurn s₁ e → Engine.step G s₁ e = .ok s₂ → s₂.lastRoll = some roll →
    newEntries s₁ s₂ = Engine.predictNextTurn G (s.withLaw id L) roll

/-- At a round's end, a step's entries start with the deals' payments, then what the laws do. -/
def RoundEndPaysDealsFirst (G : GameDef) : Prop :=
  ∀ (s s' : State G) e,
    Reachable G s → Engine.step G s e = .ok s' → EndsTurn s e → s.isLastTurn = true →
    (s.duePayments ++ lawEntries (s.afterPosting s.duePayments) .roundEnd) <+: newEntries s s'

/-- When a new turn rolls, the entries are exactly that roll's payout, the laws reacting to it, and the
laws reacting to the roll itself. On a last turn, they come after exactly the round's end entries. The
seat those laws call the actor is the seat whose turn the roll starts. -/
def RollPaysExactly (G : GameDef) : Prop :=
  ∀ (s s' : State G) e,
    Reachable G s → Engine.step G s e = .ok s' → EndsTurn s e → s'.rollsMade = s.rollsMade + 1 →
    (s.isLastTurn = false →
      newEntries s s' = rollEntries s (rollAt G s.seed s.rollsMade)) ∧
    (s.isLastTurn = true →
      newEntries s s' = s.roundEndEntries ++
        rollEntries s.afterRoundEnd (rollAt G s.seed s.rollsMade)) ∧
    s.nextRoller = s'.currentSeat

/-- A turn change with no roll makes only the round's end entries, if any. -/
def NoRollPaysOnlyRoundEnd (G : GameDef) : Prop :=
  ∀ (s s' : State G) e,
    Reachable G s → Engine.step G s e = .ok s' → EndsTurn s e → s'.rollsMade = s.rollsMade →
    newEntries s s' = s.entriesBeforeRoll

end Charter
