import Charter.Constitution.Promises
import Charter.Games.Witnesses

/-!
# Engine tests

Every `#guard` here fails the build if it is false. The file has four parts:

1. Two complete games, as named event lists. The theorems `a_full_game_exists` and
   `a_full_space_game_exists` can use them.
2. A checker that tests the constitution's claims on every step of a game.
3. Tests of single rules on concrete games.
4. Random games, each run through the checker and through a seat renaming.
-/

namespace Charter.EngineTests

open Charter Charter.Engine Charter.Games

/-! ## Helpers -/

/-- The nonces the test games use. The theorems about full games name the same ones. These nonces
give the rolls that the tests below were written for. -/
def testNonces (serverSeed : UInt64) : List UInt64 :=
  if serverSeed == 42 then [25283273] else if serverSeed == 7 then [23841] else []

/-- A new test game. -/
def testStart (G : GameDef) (seats : Nat) (serverSeed : UInt64) : State G :=
  initialState G seats serverSeed (testNonces serverSeed)

/-- The result of a game, or `none` if an event was rejected. -/
def play (G : GameDef) (seats : Nat) (seed : UInt64) (events : List Event) : Option (State G) :=
  (replay G seats seed (testNonces seed) events).toOption

/-- A property of the state after these events. False if an event was rejected. -/
def after {G : GameDef} (r : Option (State G)) (f : State G → Bool) : Bool :=
  match r with
  | some s => f s
  | none => false

/-- `step` accepts this event in this state. -/
def accepts {G : GameDef} (r : Option (State G)) (e : Event) : Bool :=
  after r fun s => (step G s e).toOption.isSome

/-- The game state is known, and `step` rejects this event in it. -/
def rejects {G : GameDef} (r : Option (State G)) (e : Event) : Bool :=
  after r fun s => (step G s e).toOption.isNone

def seatBalance {G : GameDef} (s : State G) (p : Seat) (r : Res) : Nat := s.balance (.player p) r

/-! ## Part 1: complete games -/


/-- Tiny Settlers, a setup used by the rule tests below. Seat 0 skips its second turn. -/
def settlersSetup : List Event :=
  [ placeAt 0 "settlement" 0, placeOn 0 "road" 0 1, endT 0
  , placeAt 1 "settlement" 2, placeOn 1 "road" 2 3, endT 1
  , placeAt 1 "settlement" 4, placeOn 1 "road" 4 5, endT 1
  , endT 0 ]

def settlersGame : Option (State tinySettlers) := play tinySettlers 2 42 settlersGameEvents

#guard after settlersGame fun s => s.phase == .ended
#guard after settlersGame fun s => s.winner == some 1
#guard after settlersGame fun s => s.pointsOf 1 == 4
#guard after settlersGame fun s => s.laws.map (·.1) == [1]
#guard after settlersGame fun s => s.dealsStarted == 1 && s.deals.isEmpty
#guard after settlersGame fun s => s.balance (.deposit 0 1) "timber" == 0
#guard after settlersGame fun s =>
  s.journal.contains ⟨.deposit 0 1, .player 0, "timber", 1, .dealPayment⟩ &&
  s.journal.contains ⟨.deposit 0 1, .player 1, "timber", 1, .refund⟩
#guard after settlersGame fun s => s.round == 4

def spaceGame : Option (State tinySpace) := play tinySpace 3 7 spaceGameEvents

#guard after spaceGame fun s => s.phase == .ended
#guard after spaceGame fun s => s.winner == some 0
#guard after spaceGame fun s => s.pointsOf 0 == 6
#guard after spaceGame fun s => s.laws.map (·.1) == [1]
#guard after spaceGame fun s => s.dealsStarted == 1 && s.deals.isEmpty
#guard after spaceGame fun s =>
  s.balance (.deposit 0 0) "alloy" == 0 &&
  s.journal.contains ⟨.deposit 0 0, .player 2, "alloy", 1, .dealPayment⟩ &&
  !(s.journal.map (·.reason)).contains .refund

/-! The kernel can run these games too, without compiled code. The later proofs need this. -/

example : endedWithWinnerAndLaw (replay tinySettlers 2 42 [25283273] settlersGameEvents) = true := by
  decide +kernel

example : endedWithWinnerAndLaw (replay tinySpace 3 7 [23841] spaceGameEvents) = true := by
  decide +kernel

/-! ## Part 2: the constitution's claims, checked on one step

Each function returns the names of the claims that failed, so an empty list is a pass. -/

section Claims

variable {G : GameDef}

def claim (name : String) (ok : Bool) : List String := if ok then [] else [name]

/-- Resources to look at: the game's, and one that is not in the game. -/
def resNames (G : GameDef) : List Res := G.resources.map (·.name) ++ ["not a resource"]

/-- Two sets of books agree on every account of `s` and on accounts outside the game. -/
def booksAgree (s : State G) (a b : Books) : Bool :=
  (s.accounts ++ [Account.player 999, Account.deposit maxDealsPerGame (s.turnOrder.headD 0)]).all fun x =>
    (resNames G).all fun r => a x r == b x r

/-- Commandment I. The journal rebuilds the books, and each resource keeps its total. -/
def claimI (s : State G) : List String :=
  claim "I: the journal rebuilds the books"
    (match (genesisBooks G).postAll s.journal with
     | some b => booksAgree s b s.books
     | none => false) ++
  claim "I: totals never change" ((resNames G).all fun r => s.total r == G.stockOf r) ++
  claim "I: accounts outside the game are empty"
    ((resNames G).all fun r =>
      s.balance (.player 999) r == 0 && s.balance (.deposit maxDealsPerGame 0) r == 0)

/-- Commandment I: a step only adds to the end of the journal. -/
def claimJournalPrefix (s s' : State G) : List String :=
  claim "I: a step only appends to the journal" (s.journal.isPrefixOf s'.journal)

def lawIds (laws : List (Nat × Law)) : List Nat := laws.map (·.1)

/-- Commandment III (a): the laws change only by a deciding yes vote, by exactly that law. -/
def claimIIIa (s s' : State G) (e : Event) : List String :=
  if lawIds s'.laws == lawIds s.laws then []
  else
    claim "III(a): only a deciding yes vote changes the laws" <|
      match e with
      | .vote seat id true =>
        match s.openProposal? id with
        | some p =>
          match p.body with
          | .law L =>
            s.turnOrder.contains seat && !(p.votes.map (·.1)).contains seat &&
            decide ((p.withVote seat true).yesCount * 2 > s.turnOrder.length) &&
              lawIds s'.laws == lawIds (enact s.laws id L)
          | .deal _ => false
        | none => false
      | _ => false

/-- Commandment III (b): a deciding yes vote on a valid law is accepted and enacts the law. -/
def claimIIIb (s : State G) : List String :=
  if s.phase != .actions then [] else
  claim "III(b): a deciding yes vote on a valid law is accepted" <|
    s.openProposals.all fun p =>
      match p.body with
      | .deal _ => true
      | .law L =>
        s.turnOrder.all fun seat =>
          if !(p.votes.map (·.1)).contains seat && decide (s.actionsThisTurn seat < maxActionsPerTurn) &&
             decide ((p.withVote seat true).yesCount * 2 > s.turnOrder.length) &&
             (lawProblems G s L).isEmpty then
            match step G s (.vote seat p.id true) with
            | .ok s2 => lawIds s2.laws == lawIds (enact s.laws p.id L)
            | .error _ => false
          else true

/-- Commandment III (c): no seat appears twice among a proposal's votes or signatures. -/
def claimIIIc (s : State G) : List String :=
  claim "III(c): votes and signatures have no duplicate seats" (
    s.openProposals.all fun p => decide (p.votes.map (·.1)).Nodup && decide p.signed.Nodup) ++
  claim "III(c): every seat in votes and signatures is in the game" (
    s.openProposals.all fun p =>
      (p.votes.all fun x => s.turnOrder.contains x.1) && p.signed.all s.turnOrder.contains)

/-- Commandment IV (a) and VI (a): running deals are funded and within their term. -/
def claimDealsFunded (s : State G) : List String :=
  claim "IV(a): deposits cover the worst case"
    (s.deals.all fun d => s.turnOrder.all fun i => (resNames G).all fun r =>
      decide (s.worstCase d i r ≤ s.balance (.deposit d.id i) r)) ++
  claim "VI(a): a deal cannot run past its term"
    (s.deals.all fun d => decide (s.roundsLeft d ≤ d.deal.rounds)) ++
  claim "VI(a): a deal's last round is within the term agreed at its start"
    (s.deals.all fun d =>
      decide (d.startRound ≤ s.round) && decide (d.lastRound + 1 ≤ d.startRound + d.deal.rounds)) ++
  claim "VI(a): a running deal has not passed its last round"
    (s.deals.all fun d => decide (s.round ≤ d.lastRound))

/-- Commandment VI: a deal restricts only what its signers do. -/
def claimVId (s : State G) : List String :=
  let seats := 999 :: s.turnOrder
  claim "VI: a build is blocked only by a no-build term of a deal the builder signed"
    (seats.all fun p => s.rules.pieces.all fun d => (allLocs G).all fun loc =>
      !s.blockedByDeal p d.name loc ||
        s.deals.any fun x => x.deal.signers.contains p && x.deal.terms.any fun
          | .noBuild q k _ => q == p && k == d.name
          | _ => false) ++
  claim "VI: a trade is blocked only by a no-trade term in which a signer named the other seat"
    (seats.all fun a => seats.all fun b =>
      !s.tradeBlocked a b ||
        s.deals.any fun x => x.deal.terms.any fun
          | .noTrade y z =>
            x.deal.signers.contains y && ((y == a && z == b) || (y == b && z == a))
          | _ => false)

/-- This event ends the turn. -/
def endsTurn (s : State G) : Event → Bool
  | .move p .endTurn => s.currentSeat == some p
  | .forceEndTurn => true
  | _ => false

/-- Commandment IV (b): at a round's end the deals make exactly the payments due. -/
def claimIVb (s s' : State G) (e : Event) : List String :=
  if endsTurn s e && s.isLastTurn then
    claim "IV(b): deals make exactly the payments due"
      ((newEntries s s').filter (·.reason == .dealPayment) == s.duePayments)
  else []

/-- `FundsDeal`, as a test. -/
def fundsDeal (s s' : State G) (e : Event) (x : Entry) (k : Nat) (i : Seat) : Bool :=
  x.src == .player i && x.dst == .deposit k i && x.reason == .setDeposit &&
  match e with
  | .sign seat id =>
    match s.openProposal? id with
    | some p =>
      match p.body with
      | .deal d =>
        k == s.dealsStarted && (s'.deals.any fun a => a.id == k && a.deal == d) &&
        d.signers.contains i && (d.signers.all fun j => p.signed.contains j || j == seat) &&
        d.deposits.contains (i, x.res, x.amount)
      | .law _ => false
    | none => false
  | _ => false

/-- Commandment V, the rule for money that leaves a seat's own account. -/
def mayDraw (s s' : State G) (e : Event) (x : Entry) (i : Seat) : Bool :=
  match x.reason with
  | .cost =>
    match e with
    | .move p (.place k _) => p == i && (s.costEntries i k).contains x
    | _ => false
  | .trade =>
    match e with
    | .move p (.bankTrade give get) => p == i && (s.bankTradeEntries i give get).contains x
    | .move p (.accept id) =>
      match s.offers.find? (·.id == id) with
      | some o => (i == o.src || i == p) && (offerEntries o p).contains x
      | none => false
    | _ => false
  | .setDeposit =>
    match x.dst with
    | .deposit k _ => fundsDeal s s' e x k i
    | _ => false
  | .lawEffect =>
    match e with
    | .move b (.place k _) =>
      (lawEntries (s.afterPosting (s.costEntries b k)) (.build b k)).contains x ||
      (endsTurn s e &&
        (s.roundEndLawEntries.contains x ||
         (rollEntries (s.afterPosting s.entriesBeforeRoll)
           (rollAt G s.seed s.rollsMade)).contains x))
    | _ =>
      endsTurn s e &&
        (s.roundEndLawEntries.contains x ||
         (rollEntries (s.afterPosting s.entriesBeforeRoll)
           (rollAt G s.seed s.rollsMade)).contains x)
  | _ => false

/-- Commandment V, the rule for money that leaves the bank or the treasury. -/
def mayLeaveBank (s : State G) (e : Event) (x : Entry) : Bool :=
  let harvest := (harvestEntries (s.afterPosting s.entriesBeforeRoll)
    (rollAt G s.seed s.rollsMade)).contains x
  let wholeRoll := (rollEntries (s.afterPosting s.entriesBeforeRoll)
    (rollAt G s.seed s.rollsMade)).contains x
  match x.reason with
  | .harvest => endsTurn s e && harvest
  | .trade =>
    match e with
    | .move p (.bankTrade give get) => (s.bankTradeEntries p give get).contains x
    | _ => false
  | .lawEffect =>
    (match e with
     | .move b (.place k _) =>
       (lawEntries (s.afterPosting (s.costEntries b k)) (.build b k)).contains x
     | _ => false) ||
    (endsTurn s e && (s.roundEndLawEntries.contains x || wholeRoll))
  | _ => false

/-- Commandment V: every entry of a step is allowed by one of its rules. -/
def claimV (s s' : State G) (e : Event) : List String :=
  let closed (k : Nat) : Bool := s.deals.any (·.id == k) && !s'.deals.any (·.id == k)
  claim "V: only the signature that starts a deal funds a deposit, as the deal lists"
    ((newEntries s s').all fun x =>
      match x.dst with
      | .deposit k i => fundsDeal s s' e x k i
      | _ => true) ++
  claim "V: a deposit pays only what its deal promises, to the promised payee, or refunds"
    ((newEntries s s').all fun x =>
      match x.src with
      | .deposit k i =>
        x.reason == .refund ||
        (x.reason == .dealPayment && s.deals.any fun d =>
          d.id == k && d.deal.allPays.any fun p =>
            p.src == i && p.res == x.res && p.amount == x.amount && x.dst == p.dst.account)
      | _ => true) ++
  claim "V: a deal payment comes only on the step that ends a round"
    ((newEntries s s').all fun x =>
      x.reason != .dealPayment ||
        (endsTurn s e && s.isLastTurn &&
          match x.src with
          | .deposit .. => true
          | _ => false)) ++
  claim "V: a refund goes from a deposit to its owner, only when that deal closes"
    ((newEntries s s').all fun x =>
      x.reason != .refund ||
        match x.src, x.dst with
        | .deposit k i, .player j => i == j && closed k
        | _, _ => false) ++
  claim "V: money leaves a seat's account only by an authorized rule"
    ((newEntries s s').all fun x =>
      match x.src with
      | .player i => mayDraw s s' e x i
      | _ => true) ++
  claim "V: money leaves the bank or treasury only for a harvest, a bank trade or a law"
    ((newEntries s s').all fun x =>
      match x.src with
      | .bank | .treasury => mayLeaveBank s e x
      | _ => true)

/-- Commandment VI (b): any signer can give notice. -/
def claimVIb (s : State G) : List String :=
  if s.phase != .actions then [] else
  claim "VI(b): any signer can give notice" <|
    s.deals.all fun d => d.deal.signers.all fun i =>
      if decide (s.actionsThisTurn i < maxActionsPerTurn) then
        match step G s (.exit i d.id) with
        | .ok s2 =>
          s2.deals.all fun d' => d'.id != d.id || decide (d'.lastRound ≤ s.round + d.deal.exitNotice)
        | .error _ => false
      else true

/-- Commandment VI (c): when a deal ends, its deposits are empty. -/
def claimVIc (s s' : State G) : List String :=
  claim "VI(c): a closed deal's deposits are empty" <|
    s.deals.all fun d =>
      s'.deals.any (·.id == d.id) ||
        s.turnOrder.all fun i => (resNames G).all fun r => s'.balance (.deposit d.id i) r == 0

/-- Commandment VII, for one possible build. -/
def claimVII (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : List String :=
  if s.phase != .actions then [] else
  match step G s (.move p (.place k loc)) with
  | .ok s2 =>
    let expected := s.costEntries p k ++ lawEntries (s.afterPosting (s.costEntries p k)) (.build p k)
    let entries := newEntries s s2
    let refunds := entries.drop expected.length
    claim "VII: a build is accepted only when canPlace says so" (s.canPlace p k loc) ++
    claim "VII: the pieces change by exactly this build" (s2.pieces == s.placedPieces p k loc) ++
    claim "VII: a build charges the cost and runs the laws, and nothing else"
      (entries.take expected.length == expected) ++
    claim "VII: anything more is a refund, and only if the game ended"
      ((refunds.all (·.reason == .refund)) && (refunds.isEmpty || s2.phase == .ended))
  | .error _ => claim "VII: a build that canPlace allows is accepted" (!s.canPlace p k loc)

/-- The rules of a setup placement, for one possible placement. These are tests only. -/
def claimSetup (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : List String :=
  if s.phase != .setup then [] else
  match step G s (.move p (.place k loc)) with
  | .ok s2 =>
    claim "setup: a placement is accepted only when canSetupPlace says so" (s.canSetupPlace p k loc) ++
    claim "setup: the pieces change by exactly this placement" (s2.pieces == s.placedPieces p k loc) ++
    claim "setup: a placement moves no resources" (newEntries s s2).isEmpty
  | .error _ => claim "setup: a placement that canSetupPlace allows is accepted" (!s.canSetupPlace p k loc)

/-- What a trade does, for one step and for every open offer. These are tests only. No theorem states
them. Each is written out in full here, so it does not depend on the spec's definition of a trade. -/
def claimTrades (s s' : State G) (e : Event) : List String :=
  (match e with
   | .move p (.bankTrade give get) =>
     claim "trades: a bank trade moves exactly its rate for 1"
       (newEntries s s' == s.bankTradeEntries p give get) ++
     claim "trades: a bank trade charges exactly the current rate, for exactly 1"
       (newEntries s s' ==
         [ ⟨.player p, .bank, give, s.rules.bankRate, .trade⟩, ⟨.bank, .player p, get, 1, .trade⟩ ]) ++
     claim "trades: a bank trade is on the seat's own turn" (s.isTurnOf p)
   | .move p (.accept id) =>
     match s.offers.find? (·.id == id) with
     | some o =>
       claim "trades: accepting moves exactly the offer"
         (p != o.src && (o.to.isNone || o.to == some p) && newEntries s s' == offerEntries o p) ++
       claim "trades: accepting moves exactly the offered bundles, the maker's first"
         (newEntries s s' ==
           o.give.map (fun x => ⟨.player o.src, .player p, x.1, x.2, .trade⟩) ++
           o.get.map (fun x => ⟨.player p, .player o.src, x.1, x.2, .trade⟩))
     | none => claim "trades: only an open offer can be accepted" false
   | _ => []) ++
  claim "trades: a noTrade term stops the trade"
    (s'.offers.all fun o => s'.turnOrder.all fun p =>
      !s'.tradeBlocked p o.src || (step G s' (.move p (.accept o.id))).toOption.isNone)

/-- Who can trade, in any state. These are tests only. -/
def claimWhoCanTrade (s : State G) : List String :=
  if s.phase != .actions then [] else
  let seats := 999 :: s.turnOrder
  let resources := G.resources.map (·.name)
  claim "trades: only the seat an offer is for can accept it, and never its maker"
    (s.offers.all fun o => seats.all fun p =>
      (p != o.src && (o.to.isNone || o.to == some p)) ||
        (step G s (.move p (.accept o.id))).toOption.isNone) ++
  claim "trades: a bank trade off-turn is rejected"
    (seats.all fun p => s.isTurnOf p || resources.all fun give => resources.all fun get =>
      (step G s (.move p (.bankTrade give get))).toOption.isNone) ++
  claim "trades: a noTrade term stops an offer to that seat"
    (s.turnOrder.all fun p => s.turnOrder.all fun q =>
      p == q || !s.tradeBlocked p q || !s.isTurnOf p || resources.all fun r =>
        (step G s (.move p (.offer (some q) [(r, 1)] [(r, 1)]))).toOption.isNone)

/-- Who can build, for one possible placement. These are tests only. -/
def claimWhoCanBuild (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : List String :=
  let rejected := (step G s (.move p (.place k loc))).toOption.isNone
  claim "build: a seat that cannot pay cannot build"
    (s.phase != .actions || s.affords p (s.costOf k) || rejected) ++
  claim "build: a placement off-turn is rejected, in any phase" (s.isTurnOf p || rejected)

/-- `limits_hold`. -/
def claimLimits (s : State G) : List String :=
  claim "limits: laws in force" (decide (s.laws.length ≤ maxLawsInForce)) ++
  claim "limits: law size" (s.laws.all fun x => decide (x.2.size ≤ maxLawSize)) ++
  claim "limits: open proposals per seat"
    (s.turnOrder.all fun seat => decide ((s.openProposals.filter (·.by_ == seat)).length ≤ maxOpenPerSeat)) ++
  claim "limits: running deals" (decide (s.deals.length ≤ maxActiveDeals)) ++
  claim "limits: a law in force stays under the limit on planned entries"
    (s.laws.all fun x => decide (x.2.plannedEntries s.turnOrder.length ≤ maxPlannedEntries)) ++
  claim "limits: all laws in force stay under the total limit on planned entries"
    (decide (plannedTotal s.laws s.turnOrder.length ≤ maxPlannedTotal)) ++
  claim "limits: no trigger makes a law plan more entries than it counts"
    (s.laws.all fun x =>
      let triggers : List Trigger := [.roundEnd] ++ s.turnOrder.flatMap fun p =>
        (.harvest p "grain" 1) :: (.roll p 7) :: s.rules.pieces.map fun d => .build p d.name
      triggers.all fun t =>
        decide ((Law.plan s t x.2).length ≤ x.2.plannedEntries s.turnOrder.length))

/-- Commandment VIII: the seed never changes, and rolls follow from it. -/
def claimVIII (s s' : State G) : List String :=
  claim "VIII: nobody controls the dice" <|
    s'.seed == s.seed && s'.seedCommitment == s.seedCommitment &&
    ((s'.rollsMade == s.rollsMade && s'.lastRoll == s.lastRoll) ||
     (s'.rollsMade == s.rollsMade + 1 && s'.lastRoll == some (rollAt G s.seed s.rollsMade)))

/-- A pool of laws for this game. -/
def lawPool (G : GameDef) (s : State G) : List Law :=
  let r0 := ((G.resources[0]?).map (·.name)).getD ""
  let r1 := ((G.resources[1]?).map (·.name)).getD ""
  let k0 := ((G.pieces[0]?).map (·.name)).getD ""
  let k1 := ((G.pieces[1]?).map (·.name)).getD ""
  [ { title := "cheap", clauses := [.setCost k1 [(r0, 1)]] }
  , { title := "free", clauses := [.setCost k0 []] }
  , { title := "points", clauses := [.setPoints k0 1] }
  , { title := "rate", clauses := [.setBankRate 2] }
  , { title := "tower", clauses := [.newPiece { name := "tower", cost := [(r0, 1)], points := 2
                                                placement := .attach k1, yield := 1, limit := 2 }] }
  , { title := "tax", clauses := [.onHarvest
        [.transfer .actor .treasury .harvested (.div .harvestedAmount 2)]] }
  , { title := "rent", clauses := [.onRoundEnd
        [.forEach (.lt (.lit 0) (.holding .each (.lit r0)))
          [.transfer .each .treasury (.lit r0) (.lit 2)]]] }
  , { title := "welfare", clauses := [.onRoundEnd
        [.forEach (.le (.points .each) (.lit 1))
          [.transfer .treasury .each (.lit r0) (.lit 1), .transfer .bank .each (.lit r1) (.lit 1)]]] }
  , { title := "toll", clauses := [.onBuild k0
        [.transfer .actor .treasury (.lit r1) (.count .actor k0)]] }
  , { title := "bonus", clauses := [.onHarvest
        [.when (.harvestedIs r0) [.transfer .bank .actor .harvested .harvestedAmount]]] }
  , { title := "self", clauses := [.onRoundEnd [.forEach .yes [.transfer .each .each (.lit r0) (.lit 1)]]] }
  , { title := "gift", clauses := [.onBuild k0 [.forEach .yes [.transfer .each .actor (.lit r0) (.lit 1)]]] }
  , { title := "roll gift", clauses := [.onRoll [.transfer .bank .actor (.lit r0) (.lit 1)]] }
  , { title := "roll tax", clauses := [.onRoll
        [.forEach (.le (.lit 3) .rolled) [.transfer .each .treasury (.lit r1) (.div (.holding .each (.lit r1)) 2)]]] }
  ] ++ s.laws.map fun x => { title := "repeal", clauses := [.repeal x.1] }

/-- A pool of deals between two seats of this game. -/
def dealPool (G : GameDef) (a b : Seat) (k : Nat) : List Deal :=
  let r0 := ((G.resources[0]?).map (·.name)).getD ""
  let r1 := ((G.resources[1]?).map (·.name)).getD ""
  let k0 := ((G.pieces[0]?).map (·.name)).getD ""
  [ { title := "pay", signers := [a, b], rounds := k + 1, exitNotice := k % 2
      deposits := [(a, r0, k + 2)]
      terms := [.everyRound [{ src := a, dst := .seat b, res := r0, amount := 1 }]] }
  , { title := "fund", signers := [a, b], rounds := 2, exitNotice := 0
      deposits := [(a, r1, 1), (a, r1, 1), (b, r0, 2)]
      terms := [.everyRound [{ src := a, dst := .treasury, res := r1, amount := 1 }
                            , { src := b, dst := .seat a, res := r0, amount := 1 }]] }
  , { title := "if built", signers := [b, a], rounds := 1, exitNotice := 1
      deposits := [(a, r0, 1)]
      terms := [.onBuild b k0 [{ src := a, dst := .seat b, res := r0, amount := 1 }]] }
  , { title := "keep out", signers := [a, b], rounds := 2, exitNotice := 0, deposits := []
      terms := [.noBuild a k0 [0, 1]] }
  , { title := "no trade", signers := [a, b], rounds := 2, exitNotice := 0, deposits := []
      terms := [.noTrade a b] }
  , { title := "too small", signers := [a, b], rounds := 2, exitNotice := 0, deposits := [(a, r0, 1)]
      terms := [.everyRound [{ src := a, dst := .seat b, res := r0, amount := 1 }]] } ]

/-- `every_other_event_is_exact`. -/
def claimOtherEvents (s s' : State G) (e : Event) : List String :=
  let entries := newEntries s s'
  let isPlace := match e with
    | .move _ (.place _ _) => true
    | _ => false
  claim "other events: only a place move changes the pieces" (isPlace || s'.pieces == s.pieces) ++
  claim "other events: only ending a turn moves the turn or the dice"
    (endsTurn s e || (s'.turnsTaken == s.turnsTaken && s'.turnIndex == s.turnIndex &&
      s'.round == s.round && s'.rollsMade == s.rollsMade)) ++
  match e with
  | .exit .. => claim "other events: an exit makes no entries" entries.isEmpty
  | .move _ (.offer ..) => claim "other events: an offer makes no entries" entries.isEmpty
  | .move _ (.cancel _) => claim "other events: a cancel makes no entries" entries.isEmpty
  | .move _ (.accept id) =>
    claim "other events: only an open offer is accepted" (s.offers.find? (·.id == id)).isSome
  | .move p .endTurn => claim "other events: only the current seat ends its turn" (endsTurn s (.move p .endTurn))
  | .propose _ (.deal _) => claim "other events: proposing a deal makes no entries" entries.isEmpty
  | .propose _ (.law _) =>
    claim "other events: proposing a law makes no entries" entries.isEmpty
  | .sign seat id =>
    claim "other events: a signature makes exactly the deal's deposits, or nothing" <|
      match s.openProposal? id with
      | some p =>
        match p.body with
        | .deal d =>
          if d.signers.all (fun j => p.signed.contains j || j == seat) then
            entries == depositEntries s.dealsStarted d
          else entries.isEmpty
        | .law _ => false
      | none => false
  | .vote .. =>
    claim "other events: a vote makes no entries, or only refunds if the game ends" <|
      if s'.phase == .ended then entries == s.deals.flatMap s.refundEntries else entries.isEmpty
  | _ => []

/-- `proposals_are_accepted`, on the pools of laws and deals. -/
def claimProposals (s : State G) : List String :=
  if s.phase != .actions then [] else
  s.turnOrder.flatMap fun seat =>
    if decide (s.actionsThisTurn seat < maxActionsPerTurn) &&
       decide ((s.openProposals.filter (·.by_ == seat)).length < maxOpenPerSeat) then
      let appended (s2 : State G) : Bool :=
        s2.openProposals.length == s.openProposals.length + 1 &&
        (s2.openProposals.getLast?.map fun q =>
          q.id == s.nextProposalId && q.by_ == seat && q.votes.isEmpty && q.signed.isEmpty) == some true
      claim "proposals: a law is accepted exactly when it can pass"
        ((lawPool G s).all fun L =>
          match step G s (.propose seat (.law L)) with
          | .ok s2 => (lawProblems G s L).isEmpty && appended s2
          | .error _ => !(lawProblems G s L).isEmpty) ++
      claim "proposals: a deal is accepted exactly when it can run and the seat signs it"
        (s.turnOrder.all fun other => (dealPool G seat other 0).all fun d =>
          match step G s (.propose seat (.deal d)) with
          | .ok s2 => (dealProblems s d).isEmpty && d.signers.contains seat && appended s2
          | .error _ => !((dealProblems s d).isEmpty && d.signers.contains seat))
    else []

/-- `deals_can_start`, for every open deal and every seat that could sign it now. -/
def claimDealsStart (s : State G) : List String :=
  if s.phase != .actions then [] else
  s.openProposals.flatMap fun p =>
    match p.body with
    | .law _ => []
    | .deal d =>
      d.signers.flatMap fun seat =>
        if s.turnOrder.contains seat && decide (s.actionsThisTurn seat < maxActionsPerTurn) &&
           !p.signed.contains seat then
          if d.signers.all (fun j => p.signed.contains j || j == seat) then
            let canPay := d.signers.all fun i => (d.deposits.map (·.2.1)).all fun r =>
              decide (d.depositOf i r ≤ s.balance (.player i) r)
            if (dealProblems s d).isEmpty && canPay && s.canStartDeal then
              claim "deals: the last signature starts exactly the deal" <|
                match step G s (.sign seat p.id) with
                | .ok s2 =>
                  s2.deals == s.deals ++
                    [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
                       startRound := s.round, builtBefore := s.builtThisRound.length }] &&
                  s2.dealsStarted == s.dealsStarted + 1 &&
                  newEntries s s2 == depositEntries s.dealsStarted d &&
                  (s2.openProposal? p.id).isNone
                | .error _ => false
            else []
          else
            claim "deals: a signature before the last is written down and moves nothing" <|
              match step G s (.sign seat p.id) with
              | .ok s2 =>
                s2.deals == s.deals && (newEntries s s2).isEmpty &&
                (match s2.openProposal? p.id with
                 | some q => q.signed == p.signed ++ [seat]
                 | none => false)
              | .error _ => false
        else []

/-- Commandment VIII: the seed and the fingerprint are what the server and the players set. -/
def claimSeedForm (s : State G) (serverSeed : UInt64) (nonces : List UInt64) : List String :=
  claim "VIII: the seed mixes the server's seed and the nonces"
    (s.seed == combineSeed serverSeed nonces && s.seedCommitment == commitmentOf serverSeed)

/-- Commandment IX (a) and (b): the game cannot stall, and nothing happens after the end. -/
def claimIXLive (s : State G) : List String :=
  if s.phase == .ended then
    claim "IX(b): nothing happens after the end" <|
      (step G s .forceEndTurn).toOption.isNone &&
      s.turnOrder.all fun p =>
        (step G s (.move p .endTurn)).toOption.isNone &&
        (step G s (.vote p 0 true)).toOption.isNone
  else
    claim "IX(a): the timer can always end the turn"
      (match step G s .forceEndTurn with
       | .ok s2 => s2.turnsTaken == s.turnsTaken + 1
       | .error _ => false) ++
    claim "IX(a): the current seat can always end its turn"
      (match s.currentSeat with
       | some p =>
         match step G s (.move p .endTurn) with
         | .ok s2 => s2.turnsTaken == s.turnsTaken + 1
         | .error _ => false
       | none => false)

/-- Commandment IX (c): the fixed limits on turns and events. -/
def claimIXBounds (s : State G) : List String :=
  let n := s.turnOrder.length
  claim "IX(c): turns are limited" (decide (s.turnsTaken ≤ maxTurns G n)) ++
  claim "IX(c): the last turn ends the game" (s.turnsTaken != maxTurns G n || s.phase == .ended) ++
  claim "IX(c): events are limited" (decide (s.eventsApplied ≤ maxEvents G n))

/-- Commandment X (b), (c) and (d), for a step that ends a turn. -/
def claimXTurn (s s' : State G) (e : Event) : List String :=
  if !endsTurn s e then [] else
  claim "X: the preview matches the turn change"
    (newEntries s s' == predictNextTurn G s (s'.lastRoll.getD 0)) ++
  (if s.isLastTurn then
    claim "X(c): deals pay first, then the laws react"
      ((s.duePayments ++ lawEntries (s.afterPosting s.duePayments) .roundEnd).isPrefixOf
        (newEntries s s'))
   else []) ++
  (let roll := rollAt G s.seed s.rollsMade
   if s'.rollsMade == s.rollsMade + 1 then
     if s.isLastTurn then
       claim "X(d): a last turn is the round's end and then the roll, and nothing else"
         (newEntries s s' ==
           s.roundEndEntries ++ rollEntries (s.afterPosting s.roundEndEntries) roll) ++
       claim "X(d): roll laws act for the seat whose turn starts" (s.nextRoller == s'.currentSeat)
     else
       claim "X(d): any other turn is exactly the roll" (newEntries s s' == rollEntries s roll) ++
       claim "X(d): roll laws act for the seat whose turn starts" (s.nextRoller == s'.currentSeat)
   else
     claim "X(e): a turn change with no roll makes only the round-end entries"
       (s'.rollsMade == s.rollsMade && newEntries s s' == s.entriesBeforeRoll))

/-- Commandment X (b): a deciding vote's preview is exact if the turn then ends. -/
def claimXVote (s s' : State G) (e : Event) : List String :=
  match e with
  | .vote _ id true =>
    match s.openProposal? id with
    | some p =>
      match p.body with
      | .law L =>
        if lawIds s'.laws == lawIds (enact s.laws id L) then
          let enders : List Event :=
            .forceEndTurn :: (s'.currentSeat.toList.map fun cur => .move cur .endTurn)
          enders.flatMap fun ender =>
            match step G s' ender with
            | .ok s2 =>
              claim "X(b): the preview at a vote is exact"
                (newEntries s' s2 == predictNextTurn G (s.withLaw id L) (s2.lastRoll.getD 0))
            | .error _ => []
        else []
      | .deal _ => []
    | none => []
  | _ => []

/-- `the_winner_earned_it`. -/
def claimWinner (s : State G) : List String :=
  (match s.winner with
   | none => []
   | some w =>
     claim "a winner earned it" <|
       s.phase == .ended && s.turnOrder.contains w &&
       (s.turnOrder.all fun p => decide (s.pointsOf p ≤ s.pointsOf w)) &&
       (decide (G.targetPoints ≤ s.pointsOf w) ||
         s.turnsTaken == maxTurns G s.turnOrder.length)) ++
  claim "an ended game has a winner" (s.phase != .ended || s.winner.isSome) ++
  claim "reaching the target with built points ends the game"
    (s.phase == .ended || !s.turnOrder.any fun p => decide (G.targetPoints ≤ s.builtPointsOf p))

/-- A value as text, for types that have no equality test. -/
def textOf {α : Type} [Repr α] (x : α) : String := toString (repr x)

/-- `ProposalCloses`, as a test. -/
def proposalCloses (s s' : State G) (e : Event) (p : OpenProposal) : Bool :=
  match e with
  | .vote seat id yes =>
    id == p.id && yes && decide ((p.withVote seat true).yesCount * 2 > s.turnOrder.length) &&
      match p.body with
      | .law _ => true
      | .deal _ => false
  | .sign seat id =>
    id == p.id && match p.body with
      | .deal d => d.signers.all fun j => p.signed.contains j || j == seat
      | .law _ => false
  | _ => endsTurn s e && (nextStage s).rolls && s'.currentSeat == some p.by_

/-- III(d), `ProposalsKept`. Each part has its own name, so a failure says which part broke. -/
def claimProposalsKept (s s' : State G) (e : Event) : List String :=
  let isNew (q : OpenProposal) : Bool :=
    match e with
    | .propose seat body =>
      textOf body == textOf q.body && q.id == s.nextProposalId && q.by_ == seat &&
        q.votes.isEmpty && q.signed.isEmpty
    | _ => false
  let before (q : OpenProposal) := s.openProposals.filter fun p => p.id == q.id
  let same (a b : OpenProposal) : Bool := textOf a == textOf b
  claim "III(d): a proposal's id, proposer and body never change"
    (s'.openProposals.all fun q => isNew q || (before q).any fun p =>
      p.by_ == q.by_ && textOf p.body == textOf q.body) ++
  claim "III(d): a proposal's votes are exactly what the event says"
    (s'.openProposals.all fun q => isNew q || (before q).any fun p =>
      q.votes == (proposalAfter e p).votes) ++
  claim "III(d): a proposal's signatures are exactly what the event says"
    (s'.openProposals.all fun q => isNew q || (before q).any fun p =>
      q.signed == (proposalAfter e p).signed) ++
  (if s'.phase == .ended then
    claim "III(d): the end of the game closes every proposal" s'.openProposals.isEmpty
   else
    claim "III(d): a proposal stays open unless something closes it"
      (s.openProposals.all fun p =>
        proposalCloses s s' e p || s'.openProposals.any (same (proposalAfter e p))) ++
    claim "III(d): a proposal that closes is gone"
      (s.openProposals.all fun p =>
        !proposalCloses s s' e p || !s'.openProposals.any (·.id == p.id)))

/-- III(e): any seat in the game that has not voted can vote yes or no. -/
def claimVotesAccepted (s : State G) : List String :=
  if s.phase != .actions then [] else
  claim "III(e): an ordinary vote, yes or no, is accepted" <|
    s.openProposals.all fun p =>
      match p.body with
      | .deal _ => true
      | .law _ =>
        s.turnOrder.all fun seat =>
          (p.votes.map (·.1)).contains seat || !decide (s.actionsThisTurn seat < maxActionsPerTurn) ||
            [true, false].all fun yes => (step G s (.vote seat p.id yes)).toOption.isSome

/-- III(c): a seat that is not in the game cannot vote on an open law. -/
def claimOutsiderCannotVote (s : State G) : List String :=
  claim "III(c): a seat not in the game cannot vote" <|
    s.openProposals.all fun p => (step G s (.vote 999 p.id true)).toOption.isNone

/-- V, `OffersKept`. -/
def claimOffersKept (s s' : State G) (e : Event) : List String :=
  claim "V: a step never alters an offer, and a new offer's maker is its sender" <|
    s'.offers.all fun o =>
      s.offers.contains o ||
        match e with
        | .move p (.offer to give get) => o == ⟨s.nextOfferId, p, to, give, get⟩
        | _ => false

/-- `DealCloses`, as a test. -/
def dealCloses (s : State G) (e : Event) (d : ActiveDeal) : Bool :=
  endsTurn s e && s.isLastTurn && s.closingDeals.contains d

/-- VI(a), `DealsKept`. -/
def claimDealsKept (s s' : State G) (e : Event) : List String :=
  let isNew (x : ActiveDeal) : Bool :=
    match e with
    | .sign seat id =>
      match s.openProposal? id with
      | some p =>
        match p.body with
        | .deal d =>
          d.signers.contains seat &&
          (d.signers.all fun j => p.signed.contains j || j == seat) &&
          x == { id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
                 startRound := s.round, builtBefore := s.builtThisRound.length }
        | .law _ => false
      | none => false
    | _ => false
  let before (x : ActiveDeal) := s.deals.filter fun d => d.id == x.id
  claim "VI(a): a deal's id, terms, start and earlier builds never change"
    (s'.deals.all fun x => isNew x || (before x).any fun d =>
      d.deal == x.deal && d.startRound == x.startRound && d.builtBefore == x.builtBefore) ++
  claim "VI(a): no step extends a deal"
    (s'.deals.all fun x => isNew x || (before x).any fun d => decide (x.lastRound ≤ d.lastRound)) ++
  claim "VI(a): a deal after a step is new or exactly what the event says"
    (s'.deals.all fun x => isNew x || s.deals.any fun d => x == dealAfter s e d) ++
  (if s'.phase == .ended then
    claim "VI(a): the end of the game closes every deal" s'.deals.isEmpty
   else
    claim "VI(a): a deal keeps running, with its exact last round, unless it is due to close"
      (s.deals.all fun d => dealCloses s e d || s'.deals.contains (dealAfter s e d)) ++
    claim "VI(a): a deal that closes is gone"
      (s.deals.all fun d => !dealCloses s e d || !s'.deals.any (·.id == d.id)))

/-- IV(c), `BuildsRecorded`. -/
def claimBuildsRecorded (s s' : State G) (e : Event) : List String :=
  let isBuild : Option (Seat × PieceKind) :=
    match e with
    | .move p (.place k _) => if s.phase == .actions then some (p, k) else none
    | _ => none
  let isNewRound := endsTurn s e && nextStage s == .newRound
  claim "IV(c): a build adds itself, a new round empties the list, and nothing else changes it" <|
    match isBuild with
    | some x => s'.builtThisRound == s.builtThisRound ++ [x]
    | none => if isNewRound then s'.builtThisRound.isEmpty else s'.builtThisRound == s.builtThisRound

/-- VIII: the dice roll exactly when a turn ends and an action turn comes next. -/
def claimRollNotSkipped (s s' : State G) (e : Event) : List String :=
  claim "VIII: the dice roll exactly when a turn ends and an action turn comes next"
    ((endsTurn s e && (nextStage s).rolls) == (s'.rollsMade == s.rollsMade + 1))

/-- IX(d), `TurnMovedOn`. -/
def claimTurnMovedOn (s s' : State G) (e : Event) : List String :=
  if !endsTurn s e then [] else
  claim "IX(d): a turn end adds one turn" (s'.turnsTaken == s.turnsTaken + 1) ++
  claim "IX(d): a turn end moves to the stage nextStage names"
    (match nextStage s with
     | .setupTurn i => s'.phase == .setup && s'.turnIndex == i && s'.round == s.round
     | .firstRound => s'.phase == .actions && s'.turnIndex == 0 && s'.round == s.round
     | .sameRound i => s'.phase == .actions && s'.turnIndex == i && s'.round == s.round
     | .newRound => s'.phase == .actions && s'.turnIndex == 0 && s'.round == s.round + 1
     | .gameOver => s'.phase == .ended)

/-! ### Every field, on every step

These are tests only. No theorem states them. They check what each event does to every field of the
state that the theorems leave free. -/

/-- The parts of a game that actions and turn changes write to. -/
structure Business where
  pieces : List Piece
  laws : List (Nat × Law)
  openProposals : List OpenProposal
  nextProposalId : Nat
  deals : List ActiveDeal
  dealsStarted : Nat
  offers : List Offer
  nextOfferId : Nat
  builtThisRound : List (Seat × PieceKind)

def businessOf (s : State G) : Business :=
  { pieces := s.pieces, laws := s.laws, openProposals := s.openProposals
    nextProposalId := s.nextProposalId, deals := s.deals, dealsStarted := s.dealsStarted
    offers := s.offers, nextOfferId := s.nextOfferId, builtThisRound := s.builtThisRound }

/-- The names of the fields where two records differ. -/
def businessDiff (a b : Business) : List String :=
  (if a.pieces == b.pieces then [] else ["pieces"]) ++
  (if textOf a.laws == textOf b.laws then [] else ["laws"]) ++
  (if textOf a.openProposals == textOf b.openProposals then [] else ["openProposals"]) ++
  (if a.nextProposalId == b.nextProposalId then [] else ["nextProposalId"]) ++
  (if a.deals == b.deals then [] else ["deals"]) ++
  (if a.dealsStarted == b.dealsStarted then [] else ["dealsStarted"]) ++
  (if a.offers == b.offers then [] else ["offers"]) ++
  (if a.nextOfferId == b.nextOfferId then [] else ["nextOfferId"]) ++
  (if a.builtThisRound == b.builtThisRound then [] else ["builtThisRound"])

/-- What each action changes, if no seat has reached the target. Anything not listed stays. -/
def afterAction (s : State G) : Event → Business
  | .move p (.place k loc) =>
    { businessOf s with
      pieces := s.placedPieces p k loc
      builtThisRound :=
        if s.phase == .actions then s.builtThisRound ++ [(p, k)] else s.builtThisRound }
  | .move p (.offer to give get) =>
    { businessOf s with
      offers := s.offers ++ [⟨s.nextOfferId, p, to, give, get⟩]
      nextOfferId := s.nextOfferId + 1 }
  | .move _ (.accept id) | .move _ (.cancel id) =>
    { businessOf s with offers := s.offers.filter (·.id != id) }
  | .propose seat body =>
    { businessOf s with
      openProposals := s.openProposals ++
        [{ id := s.nextProposalId, by_ := seat, body := body, votes := [], signed := [] }]
      nextProposalId := s.nextProposalId + 1 }
  | .vote seat id yes =>
    match s.openProposal? id with
    | some p =>
      match p.body with
      | .law L =>
        if isDecidingVote s p seat yes then
          { businessOf s with
            openProposals := s.openProposals.filter (·.id != id)
            laws := if (lawProblems G s L).isEmpty then enact s.laws id L else s.laws }
        else
          { businessOf s with
            openProposals := s.openProposals.map fun q =>
              if q.id == id then q.withVote seat yes else q }
      | .deal _ => businessOf s
    | none => businessOf s
  | .sign seat id =>
    match s.openProposal? id with
    | some p =>
      match p.body with
      | .deal d =>
        if d.signers.all (p.signed ++ [seat]).contains then
          { businessOf s with
            openProposals := s.openProposals.filter (·.id != id)
            deals := s.deals ++
              [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
                 startRound := s.round, builtBefore := s.builtThisRound.length }]
            dealsStarted := s.dealsStarted + 1 }
        else
          { businessOf s with
            openProposals := s.openProposals.map fun q =>
              if q.id == id then { q with signed := p.signed ++ [seat] } else q }
      | .law _ => businessOf s
    | none => businessOf s
  | .exit _ id =>
    { businessOf s with
      deals := s.deals.map fun d =>
        if d.id == id then { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
        else d }
  | _ => businessOf s

/-- The seat that sent this event. -/
def senderOf : Event → Option Seat
  | .move p _ | .propose p _ | .vote p _ _ | .sign p _ | .exit p _ => some p
  | .forceEndTurn => none

/-- An action, field by field. -/
def fieldsAfterAction (s s' : State G) (e : Event) : List String :=
  if endsTurn s e then [] else
  let seats := 999 :: s.turnOrder
  let looks := match e with
    | .move .. | .vote .. => true
    | _ => false
  let won := looks && !(seatsAtTarget s').isEmpty
  claim "fields: the sender is in the game and under its limit"
    (match senderOf e with
     | some p => s.turnOrder.contains p && decide (s.actionsThisTurn p < maxActionsPerTurn)
     | none => false) ++
  claim "fields: only the sender's action count grows"
    (match senderOf e with
     | some p => seats.all fun q =>
       s'.actionsThisTurn q == if q == p then s.actionsThisTurn q + 1 else s.actionsThisTurn q
     | none => false) ++
  claim "fields: an action adds one event" (s'.eventsApplied == s.eventsApplied + 1) ++
  claim "fields: an action keeps the seats" (s'.turnOrder == s.turnOrder) ++
  claim "fields: an action keeps the clock"
    (s'.turnsTaken == s.turnsTaken && s'.turnIndex == s.turnIndex && s'.round == s.round &&
      s'.rollsMade == s.rollsMade && s'.lastRoll == s.lastRoll) ++
  claim "fields: in setup, the only action is placing a piece"
    (s.phase != .setup || match e with
      | .move _ (.place _ _) => true
      | _ => false) ++
  (if won then
    claim "fields: a win ends the game and names the winner"
      (s'.phase == .ended && s'.winner == bestSeat s' s'.turnOrder) ++
    (businessDiff (businessOf s')
      { afterAction s e with deals := [], offers := [], openProposals := [] }).map
        ("fields: after a win, " ++ ·)
   else
    claim "fields: with no win, the phase and winner stay"
      (s'.phase == s.phase && s'.winner == s.winner) ++
    (businessDiff (businessOf s') (afterAction s e)).map ("fields: after an action, " ++ ·))

/-- A turn change, field by field. -/
def fieldsAfterTurn (s s' : State G) (e : Event) : List String :=
  if !endsTurn s e then [] else
  let keep := businessOf s
  let cleared := { keep with offers := [] }
  let expireFor (i : Nat) : List OpenProposal :=
    s.openProposals.filter fun p => some p.by_ != s.turnOrder[i]?
  let expected : Business := match nextStage s with
    | .setupTurn _ => cleared
    | .firstRound => { cleared with openProposals := expireFor 0 }
    | .sameRound i => { cleared with openProposals := expireFor i }
    | .newRound =>
      { cleared with
        openProposals := expireFor 0
        deals := s.deals.filter fun d => decide (s.round < d.lastRound)
        builtThisRound := [] }
    | .gameOver => { cleared with openProposals := [], deals := [] }
  let roll := rollAt G s.seed s.rollsMade
  claim "fields: a turn change adds one event" (s'.eventsApplied == s.eventsApplied + 1) ++
  claim "fields: a turn change keeps the seats" (s'.turnOrder == s.turnOrder) ++
  claim "fields: a turn change resets every action count"
    ((999 :: s.turnOrder).all fun q => s'.actionsThisTurn q == 0) ++
  claim "fields: the roll is written down exactly when one is made"
    (if (nextStage s).rolls then s'.rollsMade == s.rollsMade + 1 && s'.lastRoll == some roll
     else s'.rollsMade == s.rollsMade && s'.lastRoll == s.lastRoll) ++
  claim "fields: an action turn comes next exactly when the dice roll"
    ((nextStage s).rolls == (s'.phase == .actions)) ++
  claim "fields: the round stays at the end of the game"
    (nextStage s != .gameOver || (s'.round == s.round && s'.turnIndex == s.turnIndex)) ++
  claim "fields: the winner changes only at the end of the game"
    (if nextStage s == .gameOver then s'.winner == bestSeat s s.turnOrder
     else s'.winner == s.winner) ++
  (businessDiff (businessOf s') expected).map ("fields: after a turn change, " ++ ·)

/-- Every claim about one accepted step. -/
def stepClaims (s s' : State G) (e : Event) : List String :=
  claimI s' ++ claimJournalPrefix s s' ++ claimIIIa s s' e ++ claimIIIb s' ++ claimIIIc s' ++
  claimDealsFunded s' ++ claimVId s' ++ claimIVb s s' e ++
  claimV s s' e ++ claimVIb s' ++ claimVIc s s' ++ claimVIII s s' ++ claimIXLive s' ++
  claimIXBounds s' ++ claimXTurn s s' e ++ claimXVote s s' e ++ claimWinner s' ++
  claimTrades s s' e ++ claimLimits s' ++ claimOtherEvents s s' e ++ claimProposals s' ++
  claimDealsStart s' ++ claimProposalsKept s s' e ++ claimVotesAccepted s' ++
  claimOutsiderCannotVote s' ++ claimWhoCanTrade s' ++
  claimOffersKept s s' e ++ claimDealsKept s s' e ++ claimBuildsRecorded s s' e ++
  claimRollNotSkipped s s' e ++ claimTurnMovedOn s s' e ++
  fieldsAfterAction s s' e ++ fieldsAfterTurn s s' e

/-- Every possible build or setup placement, for every seat. -/
def buildClaims (s : State G) : List String :=
  (999 :: s.turnOrder).flatMap fun p =>
    s.rules.pieces.flatMap fun d => (allLocs G).flatMap fun loc =>
      claimVII s p d.name loc ++ claimSetup s p d.name loc ++ claimWhoCanBuild s p d.name loc

/-- Run a list of events, checking every claim after every step. -/
def traceFailures (G : GameDef) (seats : Nat) (seed : UInt64) (events : List Event) : List String :=
  (events.foldl
    (fun (acc : Option (State G) × List String) e =>
      match acc.1 with
      | none => acc
      | some s =>
        match step G s e with
        | .ok s' =>
          (some s', acc.2 ++ stepClaims s s' e ++ buildClaims s' ++
            claimSeedForm s' seed (testNonces seed))
        | .error m => (none, acc.2 ++ ["rejected: " ++ m]))
    (some (testStart G seats seed), [])).2

end Claims

#guard traceFailures tinySettlers 2 42 settlersGameEvents == []
#guard traceFailures tinySpace 3 7 spaceGameEvents == []

/-! ## Part 3: tests of single rules -/

/-! ### Setup -/

def settlers2 (events : List Event) : Option (State tinySettlers) := play tinySettlers 2 42 events
def space3 (events : List Event) : Option (State tinySpace) := play tinySpace 3 7 events

-- A setup placement is free and must be the next piece on the list.
#guard after (settlers2 [placeAt 0 "settlement" 0]) fun s => s.journal.isEmpty && s.pointsOf 0 == 1
#guard rejects (settlers2 []) (placeOn 0 "road" 0 1)
#guard rejects (settlers2 []) (placeAt 0 "city" 0)
#guard rejects (settlers2 []) (placeAt 1 "settlement" 0)
#guard rejects (settlers2 []) (placeAt 0 "settlement" 10)
-- A spot next to a piece is not free, and a link must touch the seat's own piece.
#guard rejects (settlers2 [placeAt 0 "settlement" 0, placeOn 0 "road" 0 1, endT 0]) (placeAt 1 "settlement" 1)
#guard rejects (settlers2 [placeAt 0 "settlement" 0]) (placeOn 0 "road" 2 3)
-- Only placing and ending the turn are possible in setup.
#guard rejects (settlers2 []) (.move 0 (.bankTrade "grain" "brick"))
#guard rejects (settlers2 []) (.move 0 (.offer none [("grain", 1)] [("brick", 1)]))
#guard rejects (settlers2 []) (.propose 0 (.law cheapCities))
#guard rejects (settlers2 []) (.vote 0 0 true)
#guard rejects (settlers2 []) (.exit 0 0)
-- The setup order is a snake, and a skipped turn places nothing.
#guard after (settlers2 [endT 0, endT 1]) fun s => s.currentSeat == some 1 && s.pieces.isEmpty
#guard after (settlers2 [endT 0, endT 1, endT 1]) fun s => s.currentSeat == some 0
#guard after (settlers2 [endT 0, endT 1, endT 1, endT 0]) fun s =>
  s.phase == .actions && s.currentSeat == some 0 && s.round == 1 && s.rollsMade == 1
-- The timer can skip setup turns too.
#guard after (settlers2 [.forceEndTurn, .forceEndTurn, .forceEndTurn, .forceEndTurn]) fun s =>
  s.phase == .actions && s.turnsTaken == 4 && s.eventsApplied == 4
-- The wrong seat cannot end a turn.
#guard rejects (settlers2 []) (endT 1)

/-! ### Who can do what, and with what -/

def settlersRound2 : List Event := settlersSetup ++ [endT 0, endT 1]

-- Seat 1 is not current, so it cannot build or trade with the bank.
#guard rejects (settlers2 settlersRound2) (placeOn 1 "road" 3 4)
#guard rejects (settlers2 settlersRound2) (.move 1 (.bankTrade "timber" "grain"))
-- A seat not in the game cannot act.
#guard rejects (settlers2 settlersRound2) (placeOn 2 "road" 3 4)
#guard rejects (settlers2 settlersRound2) (.propose 2 (.law cheapCities))
#guard rejects (settlers2 settlersRound2) (.vote 2 0 true)
-- A seat that cannot pay cannot build, and seat 0 has only 1 grain.
#guard rejects (settlers2 settlersRound2) (placeOn 0 "road" 1 2)
#guard rejects (settlers2 settlersRound2) (placeAt 0 "city" 0)

/-! ### Trading -/

-- Seat 1 holds 4 timber at the start of its turn in round 1.
def seat1Turn : List Event := settlersSetup ++ [endT 0]

#guard after (settlers2 seat1Turn) fun s => seatBalance s 1 "timber" == 4
#guard after (settlers2 (seat1Turn ++ [.move 1 (.bankTrade "timber" "grain")])) fun s =>
  seatBalance s 1 "timber" == 0 && seatBalance s 1 "grain" == 1 && s.balance .bank "timber" == 24 &&
    s.total "grain" == 24
#guard rejects (settlers2 seat1Turn) (.move 1 (.bankTrade "grain" "timber"))
#guard rejects (settlers2 seat1Turn) (.move 1 (.bankTrade "timber" "timber"))
#guard rejects (settlers2 seat1Turn) (.move 1 (.bankTrade "timber" "gold"))

def offerToSeat0 : Event := .move 1 (.offer (some 0) [("timber", 1)] [("grain", 1)])

-- An offer needs goods the seat holds, a real seat, and real resources.
#guard accepts (settlers2 seat1Turn) offerToSeat0
#guard rejects (settlers2 seat1Turn) (.move 1 (.offer none [("timber", 5)] [("grain", 1)]))
#guard rejects (settlers2 seat1Turn) (.move 1 (.offer (some 1) [("timber", 1)] [("grain", 1)]))
#guard rejects (settlers2 seat1Turn) (.move 1 (.offer (some 9) [("timber", 1)] [("grain", 1)]))
#guard rejects (settlers2 seat1Turn) (.move 1 (.offer none [("gold", 1)] [("grain", 1)]))
#guard rejects (settlers2 seat1Turn) (.move 1 (.offer none [] [("grain", 1)]))
#guard rejects (settlers2 seat1Turn) (.move 0 (.offer none [("timber", 1)] [("grain", 1)]))

-- Seat 0 has no grain yet, so it cannot pay for the offer, and nothing moves.
#guard rejects (settlers2 (seat1Turn ++ [offerToSeat0])) (.move 0 (.accept 0))
-- Seat 1 cannot accept its own offer, and there is no offer 1.
#guard rejects (settlers2 (seat1Turn ++ [offerToSeat0])) (.move 1 (.accept 0))
#guard rejects (settlers2 (seat1Turn ++ [offerToSeat0])) (.move 0 (.accept 1))
-- Only the seat that made an offer can cancel it.
#guard rejects (settlers2 (seat1Turn ++ [offerToSeat0])) (.move 0 (.cancel 0))
#guard after (settlers2 (seat1Turn ++ [offerToSeat0, .move 1 (.cancel 0)])) fun s => s.offers.isEmpty
-- An offer ends with the turn.
#guard after (settlers2 (seat1Turn ++ [offerToSeat0, endT 1])) fun s => s.offers.isEmpty
-- A paid trade. In round 2, seat 0 has grain, and it accepts on seat 1's turn.
def seat1OfferRound2 : List Event := settlersRound2 ++ [endT 0, offerToSeat0]

#guard after (settlers2 (seat1OfferRound2 ++ [.move 0 (.accept 0)])) fun s =>
  seatBalance s 0 "timber" == 1 && seatBalance s 0 "grain" == 0 && s.offers.isEmpty &&
  s.journal.getLast? == some ⟨.player 0, .player 1, "grain", 1, .trade⟩

/-! ### Laws -/

def seat0HasGrain : List Event := settlersRound2

#guard after (settlers2 (seat0HasGrain ++ [.propose 0 (.law cheapCities)])) fun s =>
  seatBalance s 0 "grain" == 1 && s.balance .bank "grain" == 22 &&
  s.openProposals.length == 1 && s.laws.isEmpty
-- Proposing moves nothing, so a seat that holds nothing can propose.
#guard after (settlers2 settlersSetup) fun s =>
  (tinySettlers.resources.all fun r => seatBalance s 0 r.name == 0) && s.phase == .actions
#guard accepts (settlers2 settlersSetup) (.propose 0 (.law cheapCities))

def badLaw (clauses : List Clause) : Law := { title := "bad", clauses := clauses }

-- A law that cannot pass is rejected.
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw [])))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw [.repeal 7])))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw [.setBankRate 1])))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw [.setCost "castle" []])))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw [.setCost "road" [("gold", 1)]])))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw [.setCost "road" [("grain", 1), ("grain", 1)]])))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw
  [.newPiece { name := "road", cost := [], points := 1, placement := .link, yield := 0, limit := 1 }])))
-- A law bigger than the limit is rejected.
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw
  (List.replicate (maxLawSize + 1) (.setPoints "road" 0)))))
def selfTransfer (src dst : Party) : Law :=
  badLaw [.onRoundEnd [.forEach .yes [.transfer src dst (.lit "grain") (.lit 1)]]]

def buildTransfer (src dst : Party) : Law :=
  badLaw [.onBuild "road" [.forEach .yes [.transfer src dst (.lit "grain") (.lit 1)]]]

-- A transfer that names one party twice can never move anything, so it is rejected.
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (selfTransfer .each .each)))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (selfTransfer .bank .bank)))
-- No seat is the actor at a round's end, so these can never move anything either.
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (selfTransfer .each .actor)))
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (selfTransfer .actor .each)))
-- At a build, the actor exists. These two may turn out to be one seat, and `settle` drops that case.
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law (buildTransfer .each .actor)))
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law (buildTransfer .actor .each)))
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law (selfTransfer .each .treasury)))

def lawOpen : List Event := seat0HasGrain ++ [.propose 0 (.law cheapCities)]

-- One yes vote is not a majority of 2 seats, and the law stays open.
#guard after (settlers2 (lawOpen ++ [.vote 0 0 true])) fun s =>
  s.laws.isEmpty && s.openProposals.length == 1
-- A vote is final, whichever way it went.
#guard rejects (settlers2 (lawOpen ++ [.vote 0 0 true])) (.vote 0 0 true)
#guard rejects (settlers2 (lawOpen ++ [.vote 0 0 false])) (.vote 0 0 true)
-- The deciding vote can come from any seat, and it enacts the law.
#guard after (settlers2 (lawOpen ++ [.vote 1 0 true, .vote 0 0 true])) fun s =>
  s.laws.map (·.1) == [0] && s.openProposals.isEmpty && s.costOf "city" == [("grain", 2)]
-- A no vote never changes the rules.
#guard after (settlers2 (lawOpen ++ [.vote 1 0 false, .vote 0 0 true])) fun s =>
  s.laws.isEmpty && s.openProposals.length == 1
-- A vote on a closed proposal is rejected.
#guard rejects (settlers2 (lawOpen ++ [.vote 1 0 true, .vote 0 0 true])) (.vote 1 0 true)
-- A proposal expires when its proposer's next turn starts.
#guard after (settlers2 (lawOpen ++ [endT 0])) fun s => s.openProposals.length == 1
#guard after (settlers2 (lawOpen ++ [endT 0, endT 1])) fun s => s.openProposals.isEmpty
-- One seat can have at most two open proposals.
#guard rejects (settlers2 (seat1Turn ++
    [ .propose 1 (.deal { title := "a", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := [], terms := [] })
    , .propose 1 (.deal { title := "b", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := [], terms := [] }) ]))
  (.propose 1 (.deal { title := "c", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := [], terms := [] }))

/-! ### A law that went stale while open

Both seats propose a piece named `tower`. Once one passes, the other can no longer pass. Its
deciding vote is accepted, it leaves the open list, and it is not enacted. -/

def towerLaw (cost : Nat) : Law :=
  { title := "Towers"
    clauses := [.newPiece { name := "tower", cost := [("timber", cost)], points := 1
                            placement := .attach "settlement", yield := 0, limit := 1 }] }

-- In round 3, seat 0 has 1 grain and seat 1 has 2. Both pay a fee on seat 1's turn.
def twoTowers : List Event :=
  settlersRound2 ++ [endT 0, endT 1, endT 0, endT 1, .forceEndTurn] ++
  [ .propose 0 (.law (towerLaw 1)), .propose 1 (.law (towerLaw 2)) ]

#guard after (settlers2 twoTowers) fun s => s.openProposals.map (·.id) == [0, 1]
#guard after (settlers2 (twoTowers ++ [.vote 0 0 true, .vote 1 0 true])) fun s =>
  s.laws.map (·.1) == [0] && s.costOf "tower" == [("timber", 1)]
#guard after (settlers2 (twoTowers ++ [.vote 0 0 true, .vote 1 0 true, .vote 0 1 true, .vote 1 1 true])) fun s =>
  s.laws.map (·.1) == [0] && s.openProposals.isEmpty && s.costOf "tower" == [("timber", 1)]

/-! ### Repeal -/

def repealCheapCities : Law := { title := "Dear cities", clauses := [.repeal 0] }

/-- Pass cheap cities in round 2, then repeal it in round 3. A repeal undoes its rule changes. -/
def repealGame : List Event :=
  lawOpen ++ [.vote 0 0 true, .vote 1 0 true, endT 0, endT 1, endT 0,
    .propose 1 (.law repealCheapCities), .vote 0 1 true, .vote 1 1 true]

#guard after (settlers2 repealGame) fun s =>
  s.laws.map (·.1) == [1] && s.costOf "city" == [("grain", 3)]
#guard traceFailures tinySettlers 2 42 repealGame == []
-- A law that is gone cannot be repealed again.
#guard rejects (settlers2 repealGame) (.propose 1 (.law repealCheapCities))

/-! ### What laws do -/

/-- Each harvest pays half of what it collected to the treasury, rounding down. -/
def harvestTax : Law :=
  { title := "Harvest tax"
    clauses := [.onHarvest [.transfer .actor .treasury .harvested (.div .harvestedAmount 2)]] }

/-- At each round's end, each seat pays the treasury 1 grain. -/
def rentLaw : Law :=
  { title := "Rent"
    clauses := [.onRoundEnd [.forEach .yes [.transfer .each .treasury (.lit "grain") (.lit 1)]]] }

/-- Each road pays the treasury 1 brick from its builder. -/
def roadToll : Law :=
  { title := "Road toll"
    clauses := [.onBuild "road" [.transfer .actor .treasury (.lit "brick") (.lit 1)]] }

-- Rent asks each seat for 1 grain.
def rentGame : List Event :=
  settlersRound2 ++ [.propose 0 (.law rentLaw), .vote 0 0 true, .vote 1 0 true, endT 0, endT 1]

#guard after (settlers2 rentGame) fun s =>
  s.balance .treasury "grain" == 2 && seatBalance s 0 "grain" == 0 && seatBalance s 1 "grain" == 0
#guard traceFailures tinySettlers 2 42 rentGame == []

def tollGame : List Event :=
  settlersRound2 ++ [.propose 0 (.law roadToll), .vote 0 0 true, .vote 1 0 true, endT 0, endT 1,
    endT 0, placeOn 1 "road" 3 4]

#guard after (settlers2 tollGame) fun s =>
  s.balance .treasury "brick" == 1 && seatBalance s 1 "brick" == 0 && s.countOf 1 "road" == 3
#guard traceFailures tinySettlers 2 42 tollGame == []

def taxGame : List Event :=
  settlersRound2 ++ [.propose 0 (.law harvestTax), .vote 0 0 true, .vote 1 0 true, endT 0]

-- Seat 1's turn in round 2 rolled 3. Each settlement collects 1, and half of 1 rounds down to 0.
#guard after (settlers2 taxGame) fun s => s.balance .treasury "brick" == 0
#guard traceFailures tinySettlers 2 42 taxGame == []

/-- Each harvest pays the treasury 1 of what it collected. -/
def flatTax : Law :=
  { title := "Flat tax", clauses := [.onHarvest [.transfer .actor .treasury .harvested (.lit 1)]] }

-- The same roll with a flat tax. Each of the two settlements on brick pays its 1 brick back.
#guard after (settlers2 (settlersRound2 ++
    [.propose 0 (.law flatTax), .vote 0 0 true, .vote 1 0 true, endT 0])) fun s =>
  s.balance .treasury "brick" == 2 && seatBalance s 0 "brick" == 0 && seatBalance s 1 "brick" == 0 &&
  s.journal.getLast?.map (·.reason) == some .lawEffect

/-- Everyone pays the builder of a road 1 grain. -/
def everyonePaysBuilder : Law :=
  { title := "Road gift"
    clauses := [.onBuild "road" [.forEach .yes [.transfer .each .actor (.lit "grain") (.lit 1)]]] }

/-- The law passes in round 2, and the game moves on until seat 0 holds grain again. -/
def giftGame : List Event :=
  settlersRound2 ++ [.propose 0 (.law everyonePaysBuilder), .vote 0 0 true, .vote 1 0 true,
    endT 0, endT 1, endT 0, endT 1, endT 0]

-- Seat 1 is the builder, it pays itself nothing, and seat 0 pays it.
#guard after (settlers2 (giftGame ++ [endT 1, endT 0])) fun s =>
  s.currentSeat == some 1 && seatBalance s 0 "grain" > 0
#guard after (settlers2 (giftGame ++ [endT 1, endT 0])) fun s =>
  match step tinySettlers s (placeOn 1 "road" 3 4) with
  | .ok s2 =>
    let lawPart := (newEntries s s2).filter (·.reason == .lawEffect)
    lawPart == [⟨.player 0, .player 1, "grain", 1, .lawEffect⟩] &&
      seatBalance s2 0 "grain" + 1 == seatBalance s 0 "grain" &&
      seatBalance s2 1 "grain" == seatBalance s 1 "grain" + 1
  | .error _ => false
#guard traceFailures tinySettlers 2 42 (giftGame ++ [endT 1, endT 0, placeOn 1 "road" 3 4]) == []

-- `settle` drops self-transfers first, so they do not count toward an account's demand.
#guard after (settlers2 seat1Turn) fun s =>
  settle s [⟨.player 1, .player 1, "timber", 100, .lawEffect⟩,
            ⟨.player 1, .treasury, "timber", 4, .lawEffect⟩] ==
    [⟨.player 1, .treasury, "timber", 4, .lawEffect⟩]
-- Requests over the balance still shrink, so nothing can overdraw.
#guard after (settlers2 seat1Turn) fun s =>
  settle s [⟨.player 1, .treasury, "timber", 6, .lawEffect⟩,
            ⟨.player 1, .bank, "timber", 6, .lawEffect⟩] ==
    [⟨.player 1, .treasury, "timber", 2, .lawEffect⟩, ⟨.player 1, .bank, "timber", 2, .lawEffect⟩]

/-! ### Upgrades -/

-- Seat 1's upgrade in the full game replaces each settlement.
#guard after settlersGame fun s =>
  s.countOf 1 "settlement" == 0 && s.countOf 1 "city" == 2 &&
  s.pieces.contains ⟨1, "city", .spot 2⟩ && !s.pieces.contains ⟨1, "settlement", .spot 2⟩
-- A city must go on the seat's own settlement.
def seat1WithGrain : List Event :=
  settlersRound2 ++ [endT 0, endT 1, endT 0, endT 1, endT 0, endT 1, endT 0]

#guard after (settlers2 seat1WithGrain) fun s => s.currentSeat == some 1
#guard rejects (settlers2 seat1WithGrain) (placeAt 1 "city" 0)
#guard rejects (settlers2 seat1WithGrain) (placeAt 1 "city" 3)
-- `builtThisRound` records the build.
#guard after (settlers2 tollGame) fun s => s.builtThisRound == [(1, "road")]
#guard after (settlers2 (tollGame ++ [endT 1])) fun s => s.builtThisRound.isEmpty

/-! ### Deals -/

/-- Seat 1 pays seat 0 one timber each round for 2 rounds, with 3 timber in deposit. -/
def timberDeal : Deal :=
  { title := "Timber for peace"
    signers := [1, 0]
    rounds := 2
    exitNotice := 0
    deposits := [(1, "timber", 3)]
    terms := [.everyRound [{ src := 1, dst := .seat 0, res := "timber", amount := 1 }]] }

def dealProposed : List Event := seat1Turn ++ [.propose 1 (.deal timberDeal)]

-- A proposal moves nothing. Neither does the first signature.
#guard after (settlers2 dealProposed) fun s => seatBalance s 1 "timber" == 4 && s.deals.isEmpty
#guard after (settlers2 (dealProposed ++ [.sign 0 0])) fun s =>
  seatBalance s 1 "timber" == 4 && s.deals.isEmpty && s.dealsStarted == 0
-- Laws are voted on and deals are signed. A seat signs once, and only signers sign.
#guard rejects (settlers2 dealProposed) (.vote 0 0 true)
#guard rejects (settlers2 (dealProposed ++ [.sign 0 0])) (.sign 0 0)
#guard rejects (settlers2 lawOpen) (.sign 0 0)
def thirdSeatDeal : Deal := { timberDeal with signers := [1, 2] }
#guard rejects (settlers2 seat1Turn) (.propose 1 (.deal thirdSeatDeal))

def dealStarted : List Event := dealProposed ++ [.sign 0 0, .sign 1 0]

-- The last signature moves the deposit and starts the deal.
#guard after (settlers2 dealStarted) fun s =>
  seatBalance s 1 "timber" == 1 && s.balance (.deposit 0 1) "timber" == 3 &&
  s.deals.map (·.id) == [0] && s.dealsStarted == 1 && s.openProposals.isEmpty &&
  s.deals.map (·.lastRound) == [2] &&
  s.journal.getLast? == some ⟨.player 1, .deposit 0 1, "timber", 3, .setDeposit⟩
-- It pays at this round's end, and again at the next, then it closes and refunds what is left.
#guard after (settlers2 (dealStarted ++ [endT 1])) fun s =>
  seatBalance s 0 "timber" == 1 && s.balance (.deposit 0 1) "timber" == 2 && s.deals.length == 1
#guard after (settlers2 (dealStarted ++ [endT 1, endT 0])) fun s => s.deals.length == 1
#guard after (settlers2 (dealStarted ++ [endT 1, endT 0, endT 1])) fun s =>
  seatBalance s 0 "timber" == 2 && s.balance (.deposit 0 1) "timber" == 0 && s.deals.isEmpty
#guard traceFailures tinySettlers 2 42 (dealStarted ++ [endT 1, endT 0, endT 1]) == []
-- Notice with no notice period ends the deal at this round's end, and refunds the rest.
#guard after (settlers2 (dealStarted ++ [.exit 0 0])) fun s => s.deals.map (·.lastRound) == [1]
#guard after (settlers2 (dealStarted ++ [.exit 0 0, endT 1])) fun s =>
  s.deals.isEmpty && seatBalance s 0 "timber" == 1 && s.balance (.deposit 0 1) "timber" == 0 &&
  (s.journal.map (·.reason)).contains .refund
-- Only a signer can give notice, and only for a running deal.
#guard rejects (settlers2 dealStarted) (.exit 2 0)
#guard rejects (settlers2 dealStarted) (.exit 0 1)
-- A deposit too small for the deal is rejected when it is proposed.
#guard rejects (settlers2 seat1Turn)
  (.propose 1 (.deal { timberDeal with deposits := [(1, "timber", 1)] }))
-- A deposit the signer cannot pay rejects the last signature only, and nothing moves.
#guard after (settlers2 (seat1Turn ++
    [.propose 1 (.deal { timberDeal with deposits := [(1, "timber", 9)] }), .sign 0 0])) fun s =>
  (step tinySettlers s (.sign 1 0)).toOption.isNone
-- Other limits on deals.
#guard rejects (settlers2 seat1Turn) (.propose 1 (.deal { timberDeal with rounds := 0 }))
#guard rejects (settlers2 seat1Turn) (.propose 1 (.deal { timberDeal with signers := [1, 1] }))
#guard rejects (settlers2 seat1Turn) (.propose 1 (.deal { timberDeal with signers := [1] }))
#guard rejects (settlers2 seat1Turn) (.propose 1 (.deal { timberDeal with deposits := [(0, "timber", 2), (1, "timber", 2)], signers := [1, 5] }))
#guard rejects (settlers2 seat1Turn)
  (.propose 1 (.deal { timberDeal with
    terms := [.everyRound [{ src := 1, dst := .seat 9, res := "timber", amount := 1 }]] }))
#guard rejects (settlers2 seat1Turn) (.propose 1 (.deal { timberDeal with signers := [0, 2] }))

/-- A deal with a term that fires when seat 1 builds a road. -/
def roadDeal : Deal :=
  { title := "Road money"
    signers := [1, 0]
    rounds := 1
    exitNotice := 0
    deposits := [(1, "timber", 1)]
    terms := [.onBuild 1 "road" [{ src := 1, dst := .treasury, res := "timber", amount := 1 }]] }

def seat1RichTurn : List Event := settlersRound2 ++ [endT 0]

def roadDealStarted : List Event :=
  seat1RichTurn ++ [.propose 1 (.deal roadDeal), .sign 0 0, .sign 1 0]

-- The term fires when the seat built that kind this round.
#guard after (settlers2 (roadDealStarted ++ [placeOn 1 "road" 3 4, endT 1])) fun s =>
  s.balance .treasury "timber" == 1 && s.deals.isEmpty
-- And it does not fire otherwise. The deposit goes back.
#guard after (settlers2 (roadDealStarted ++ [endT 1])) fun s =>
  s.balance .treasury "timber" == 0 && s.balance (.deposit 0 1) "timber" == 0 &&
  seatBalance s 1 "timber" == 4

-- A build before the deal started does not count, in the deal's first round.
#guard after (settlers2 (seat1RichTurn ++
    [placeOn 1 "road" 3 4, .propose 1 (.deal roadDeal), .sign 0 0, .sign 1 0, endT 1])) fun s =>
  s.balance .treasury "timber" == 0 && (s.journal.filter (·.reason == .dealPayment)).isEmpty
/-- `roadDeal`, running for two rounds. -/
def roadDeal2 : Deal := { roadDeal with rounds := 2, deposits := [(1, "timber", 2)] }

/-- Seat 1 builds a road, then the deal starts, then the round ends. -/
def buildThenDeal : List Event :=
  seat1RichTurn ++ [placeOn 1 "road" 3 4, .propose 1 (.deal roadDeal2), .sign 0 0, .sign 1 0, endT 1]

-- Nothing is paid in the first round, because the build came first.
#guard after (settlers2 buildThenDeal) fun s =>
  s.balance .treasury "timber" == 0 && s.deals.map (·.startRound) == [2] &&
  s.deals.map (·.builtBefore) == [1] && s.builtThisRound.isEmpty
-- In the deal's second round, a build pays.
#guard after (settlers2 (buildThenDeal ++ [endT 0, placeOn 1 "road" 1 2, endT 1])) fun s =>
  s.balance .treasury "timber" == 1 && s.deals.isEmpty && s.balance (.deposit 0 1) "timber" == 0
-- In the deal's second round, no build means no payment, and the deposit goes back.
#guard after (settlers2 (buildThenDeal ++ [endT 0, endT 1])) fun s =>
  s.balance .treasury "timber" == 0 && s.deals.isEmpty && s.balance (.deposit 0 1) "timber" == 0
-- The same rules hold for a deal that starts in a later round of the game.
def laterTurn : List Event := seat1RichTurn ++ [endT 1, endT 0]

#guard after (settlers2 (laterTurn ++
    [placeOn 1 "road" 3 4, .propose 1 (.deal roadDeal), .sign 0 0, .sign 1 0, endT 1])) fun s =>
  s.round == 4 && s.balance .treasury "timber" == 0 &&
  (s.journal.filter (·.reason == .dealPayment)).isEmpty
#guard after (settlers2 (laterTurn ++
    [.propose 1 (.deal roadDeal), .sign 0 0, .sign 1 0, placeOn 1 "road" 3 4, endT 1])) fun s =>
  s.round == 4 && s.balance .treasury "timber" == 1
#guard traceFailures tinySettlers 2 42 (buildThenDeal ++ [endT 0, placeOn 1 "road" 1 2, endT 1]) == []

/-- A deal that stops seat 1 building a road near spot 3. -/
def noRoadDeal : Deal :=
  { title := "Keep out", signers := [1, 0], rounds := 1, exitNotice := 0, deposits := []
    terms := [.noBuild 1 "road" [4]] }

#guard after (settlers2 (seat1RichTurn ++ [.propose 1 (.deal noRoadDeal), .sign 0 0, .sign 1 0])) fun s =>
  (step tinySettlers s (placeOn 1 "road" 3 4)).toOption.isNone
#guard accepts (settlers2 seat1RichTurn) (placeOn 1 "road" 3 4)

/-- A deal that stops seats 0 and 1 trading. -/
def noTradeDeal : Deal :=
  { title := "Embargo", signers := [1, 0], rounds := 1, exitNotice := 0, deposits := []
    terms := [.noTrade 0 1] }

#guard after (settlers2 (seat1RichTurn ++ [offerToSeat0, .propose 1 (.deal noTradeDeal), .sign 0 0, .sign 1 0])) fun s =>
  (step tinySettlers s (.move 0 (.accept 0))).toOption.isNone &&
  (step tinySettlers s offerToSeat0).toOption.isNone

-- A win refunds every running deal at once. These refunds are the only entries after the build.
def winWithDeal : List Event :=
  settlersSetup ++
  [ endT 0, endT 1
  , .propose 0 (.law cheapCities), .vote 0 0 true, .vote 1 0 true
  , endT 0, endT 1
  , endT 0
  , placeAt 1 "city" 2
  , .propose 1 (.deal { timberDeal with rounds := 3, deposits := [(1, "timber", 3)] })
  , .sign 0 1, .sign 1 1
  , endT 1
  , endT 0
  , placeAt 1 "city" 4 ]

#guard after (settlers2 winWithDeal) fun s =>
  s.phase == .ended && s.winner == some 1 && s.deals.isEmpty &&
  s.balance (.deposit 0 1) "timber" == 0 && s.journal.getLast?.map (·.reason) == some .refund
#guard traceFailures tinySettlers 2 42 winWithDeal == []

/-! ### Limits on deals -/

-- With a notice period, notice ends the deal that many rounds later, and never extends it.
#guard after (settlers2 (seat1Turn ++
    [ .propose 1 (.deal { timberDeal with rounds := 3, exitNotice := 1 }), .sign 0 0, .sign 1 0
    , .exit 1 0 ])) fun s => s.deals.map (·.lastRound) == [2]
#guard after (settlers2 (seat1Turn ++
    [ .propose 1 (.deal { timberDeal with rounds := 1, exitNotice := 5, deposits := [(1, "timber", 1)] })
    , .sign 0 0, .sign 1 0, .exit 1 0 ])) fun s => s.deals.map (·.lastRound) == [1]

/-- A deal that moves nothing and ends at this round's end. -/
def emptyDeal (rounds : Nat) : Deal :=
  { title := "Pact", signers := [0, 1], rounds := rounds, exitNotice := 0, deposits := [], terms := [] }

/-- Start one deal, using proposal number `n`. -/
def startEmptyDeal (rounds n : Nat) : List Event :=
  [.propose 0 (.deal (emptyDeal rounds)), .sign 0 n, .sign 1 n]

/-- Start `count` deals with proposal numbers from `first`. -/
def startEmptyDeals (rounds first count : Nat) : List Event :=
  (List.range count).flatMap fun i => startEmptyDeal rounds (first + i)

def afterSetupForced : List Event := List.replicate 4 .forceEndTurn

-- Eight deals can run at once. The last signature of a ninth is rejected.
#guard after (settlers2 (afterSetupForced ++ startEmptyDeals 2 0 maxActiveDeals)) fun s =>
  s.deals.map (·.id) == List.range maxActiveDeals
#guard rejects (settlers2 (afterSetupForced ++ startEmptyDeals 2 0 maxActiveDeals ++
    [.propose 0 (.deal (emptyDeal 2)), .sign 0 8])) (.sign 1 8)

/-- One round: eight one-round deals on seat 0's turn, then the round ends and they close. -/
def eightDealsARound (round : Nat) : List Event :=
  startEmptyDeals 1 (round * maxActiveDeals) maxActiveDeals ++ [.forceEndTurn, .forceEndTurn]

-- A game can start 64 deals. Ids are below 64, so the last signature of the 65th is rejected.
def sixtyFourDeals : List Event :=
  afterSetupForced ++ (List.range 8).flatMap eightDealsARound

#guard after (settlers2 sixtyFourDeals) fun s =>
  s.dealsStarted == maxDealsPerGame && s.deals.isEmpty && s.round == 9
#guard rejects (settlers2 (sixtyFourDeals ++ [.propose 0 (.deal (emptyDeal 1)), .sign 0 64])) (.sign 1 64)

/-! ### The order of a round's end -/

/-- Rent is in force, and a deal pays seat 0 one timber at the same round's end. -/
def rentAndDeal : List Event :=
  rentGame.dropLast.dropLast ++ [endT 0, .propose 1 (.deal timberDeal), .sign 0 1, .sign 1 1, endT 1]

-- The deal pays before the laws react.
#guard after (settlers2 rentAndDeal) fun s =>
  let reasons := s.journal.map (·.reason)
  let afterFee := reasons.dropWhile (· != .dealPayment)
  afterFee.head? == some .dealPayment && afterFee.contains .lawEffect
#guard traceFailures tinySettlers 2 42 rentAndDeal == []

/-- At the round's end the bank pays each seat 1 brick. Each harvest then takes all of the brick
the harvesting seat holds, so a harvest that did not see the round's end would take too little. -/
def brickSweep : Law :=
  { title := "Brick sweep"
    clauses :=
      [ .onRoundEnd [.forEach .yes [.transfer .bank .each (.lit "brick") (.lit 1)]]
      , .onHarvest [.transfer .actor .treasury (.lit "brick") (.holding .actor (.lit "brick"))] ] }

/-- Round 2 ends with the dividend, and round 3 starts with a roll of 3, which pays brick. -/
def sweepGame : List Event :=
  settlersRound2 ++ [.propose 0 (.law brickSweep), .vote 0 0 true, .vote 1 0 true, endT 0, endT 1]

#guard after (settlers2 sweepGame) fun s =>
  seatBalance s 0 "brick" == 0 && seatBalance s 1 "brick" == 0 && s.balance .treasury "brick" == 6
#guard traceFailures tinySettlers 2 42 sweepGame == []

/-! ### The action cap and forced turn ends -/

def twentyCancels : List Event :=
  (List.range maxActionsPerTurn).flatMap fun i =>
    if i % 2 == 0 then [offerToSeat0] else [.move 1 (.cancel (i / 2))]

#guard after (settlers2 (seat1Turn ++ twentyCancels)) fun s =>
  s.actionsThisTurn 1 == maxActionsPerTurn
-- The next action is rejected, but the turn can still end.
#guard rejects (settlers2 (seat1Turn ++ twentyCancels)) offerToSeat0
#guard rejects (settlers2 (seat1Turn ++ twentyCancels)) (.exit 1 0)
#guard accepts (settlers2 (seat1Turn ++ twentyCancels)) (endT 1)
#guard accepts (settlers2 (seat1Turn ++ twentyCancels)) .forceEndTurn
-- The count resets on the next turn, and seat 0's count did not move.
#guard after (settlers2 (seat1Turn ++ twentyCancels ++ [endT 1])) fun s =>
  s.actionsThisTurn 1 == 0 && s.actionsThisTurn 0 == 0
-- The turn counter and the event counter follow each event.
#guard after (settlers2 (seat1Turn ++ [offerToSeat0, .forceEndTurn])) fun s =>
  s.turnsTaken == 6 && s.eventsApplied == 13

/-! ### The end of the game -/

/-- Every turn of a game with no action, through the last round. -/
def timedOut (G : GameDef) (seats : Nat) : List Event :=
  List.replicate (maxTurns G seats) .forceEndTurn

def timedOutSettlers : Option (State tinySettlers) := settlers2 (timedOut tinySettlers 2)

-- If nobody places anything, the rounds run out, and the tie goes to the first seat.
#guard after timedOutSettlers fun s =>
  s.phase == .ended && s.winner == some 0 && s.turnsTaken == maxTurns tinySettlers 2 &&
  s.round == tinySettlers.rounds
-- Nothing happens after the end.
#guard rejects timedOutSettlers .forceEndTurn
#guard rejects timedOutSettlers (endT 0)
#guard rejects timedOutSettlers (placeAt 0 "settlement" 0)
#guard rejects timedOutSettlers (.vote 0 0 true)
#guard rejects timedOutSettlers (.propose 0 (.law cheapCities))
#guard rejects timedOutSettlers (.sign 0 0)
#guard rejects timedOutSettlers (.exit 0 0)
#guard rejects settlersGame (.move 0 (.place "road" (.link (1, 2))))
#guard traceFailures tinySettlers 2 42 (timedOut tinySettlers 2) == []
#guard traceFailures tinySpace 3 7 (timedOut tinySpace 3) == []

-- If the rounds run out, the most points wins, not the first seat.
#guard after (settlers2 (settlersSetup ++
    List.replicate (tinySettlers.rounds * 2) .forceEndTurn)) fun s =>
  s.phase == .ended && s.winner == some 1
-- A deal still running at the end pays for its last round and then refunds the rest. It starts
-- in round 9 for 3 rounds, so it pays twice and 1 timber comes back.
def dealAtEnd : List Event :=
  settlersSetup ++ List.replicate 17 .forceEndTurn ++
  [ .propose 1 (.deal { timberDeal with rounds := 3 }), .sign 0 0, .sign 1 0
  , .forceEndTurn, .forceEndTurn, .forceEndTurn ]

#guard after (settlers2 dealAtEnd) fun s =>
  s.phase == .ended && s.round == 10 && s.deals.isEmpty && s.balance (.deposit 0 1) "timber" == 0 &&
  (s.journal.filter (·.reason == .dealPayment)).length == 2 &&
  s.journal.getLast? == some ⟨.deposit 0 1, .player 1, "timber", 1, .refund⟩
#guard traceFailures tinySettlers 2 42 dealAtEnd == []

-- A tie for points goes to the seat earlier in turn order, whatever its number is.
def reversedStart (G : GameDef) : State G :=
  { testStart G 3 7 with turnOrder := [2, 1, 0] }

#guard after ((List.replicate (maxTurns tinySpace 3) Event.forceEndTurn).foldlM (step tinySpace)
    (reversedStart tinySpace) |>.toOption) fun s =>
  s.phase == .ended && s.winner == some 2

/-! ### A short bank -/

/-- One grain in the whole game, with two seats on the same region. -/
def shortBank : GameDef :=
  { tinySettlers with
    resources := [⟨"grain", 1⟩, ⟨"timber", 24⟩, ⟨"brick", 24⟩]
    map := { tinySettlers.map with regions := [⟨"grain", 1, [0, 2]⟩, ⟨"grain", 2, [0, 2]⟩, ⟨"grain", 3, [0, 2]⟩] } }

example : shortBank.Valid := by decide

def shortBankGame : List Event :=
  [ placeAt 0 "settlement" 0, endT 0, placeAt 1 "settlement" 2, endT 1, endT 1, endT 0 ]

-- Each seat asks for 1 of the 1 grain. Each share rounds down to 0, and nothing moves.
#guard after (play shortBank 2 42 shortBankGame) fun s =>
  s.journal.isEmpty && s.balance .bank "grain" == 1
#guard traceFailures shortBank 2 42 shortBankGame == []

/-- One grain left after the seats are paid twice, with demand of 2 each on the next roll. -/
def shortBank2 : GameDef :=
  { shortBank with resources := [⟨"grain", 3⟩, ⟨"timber", 24⟩, ⟨"brick", 24⟩] }

-- The first roll pays 1 and 1. The second asks for 1 and 1 with 1 left, so each share is 0.
#guard after (play shortBank2 2 42 shortBankGame) fun s => s.balance .bank "grain" == 1
#guard after (play shortBank2 2 42 (shortBankGame ++ [endT 0])) fun s =>
  s.balance .bank "grain" == 1 && seatBalance s 1 "grain" == 1
#guard traceFailures shortBank2 2 42 (shortBankGame ++ [endT 0]) == []

/-! ### The dice and the seed -/

#guard after settlersGame fun s =>
  s.seed == combineSeed 42 [25283273] && s.seedCommitment == commitmentOf 42 &&
  s.lastRoll == some (rollAt tinySettlers s.seed (s.rollsMade - 1))
-- These values come from Python's `hashlib`.
#guard commitmentOf 42 == "a6bb133cb1e3638ad7b8a3ff0539668e9e56f9b850ef1b2a810f5422eaa6c323"
#guard combineSeed 42 [25283273] == 4098413131932950764
#guard combineSeed 42 [] == 12014217582344364938
-- The fingerprint does not depend on the nonces, and the game's seed does.
#guard (testStart tinySettlers 2 42).seedCommitment == (initialState tinySettlers 2 42 []).seedCommitment
#guard combineSeed 42 [1] != combineSeed 42 [2]
#guard combineSeed 42 [1, 2] != combineSeed 42 [2, 1]
#guard combineSeed 1 [2] != combineSeed 2 [1]
#guard commitmentOf 0 != commitmentOf 1

/-- A long list of dice, starting at roll `first`. -/
def rollsFrom (seed : UInt64) (first : Nat) : List Nat :=
  (List.range 60).map fun k => rollAt tinySettlers seed (first + k)

-- Before the change, seed `s + 1000` gave the rolls of seed `s` shifted by one.
#guard rollsFrom 42 1 != rollsFrom 1042 0
#guard rollsFrom 42 0 != rollsFrom 1042 0

/-! ### The preview -/

/-- A law the preview must include: the bank pays each seat 1 brick at the round's end. -/
def dividend : Law :=
  { title := "Dividend"
    clauses := [.onRoundEnd [.forEach .yes [.transfer .bank .each (.lit "brick") (.lit 1)]]] }

-- Seat 1 ends round 2, so the preview includes the dividend and the next harvest.
def dividendVotes : List Event :=
  seat1RichTurn ++ [.propose 1 (.law dividend), .vote 0 0 true]

#guard after (settlers2 dividendVotes) fun s =>
  match step tinySettlers s (.vote 1 0 true) with
  | .ok s1 =>
    match step tinySettlers s1 (endT 1) with
    | .ok s2 =>
      let preview := predictNextTurn tinySettlers (s.withLaw 0 dividend) (s2.lastRoll.getD 0)
      newEntries s1 s2 == preview &&
        preview.take 2 ==
          [⟨.bank, .player 0, "brick", 1, .lawEffect⟩, ⟨.bank, .player 1, "brick", 1, .lawEffect⟩]
    | .error _ => false
  | .error _ => false
#guard traceFailures tinySettlers 2 42 (dividendVotes ++ [.vote 1 0 true, endT 1]) == []
-- At the end of the game there is no roll, so a preview has no harvest for any roll.
#guard after (settlers2 (List.replicate (maxTurns tinySettlers 2 - 1) .forceEndTurn)) fun s =>
  predictNextTurn tinySettlers s 1 == predictNextTurn tinySettlers s 2
-- A game over has nothing to preview.
#guard after settlersGame fun s => predictNextTurn tinySettlers s 1 == []

/-! ### Legal moves -/

#guard after (settlers2 []) fun s =>
  (legalMoves tinySettlers s 0).contains (.place "settlement" (.spot 0)) &&
  (legalMoves tinySettlers s 0).contains .endTurn &&
  !(legalMoves tinySettlers s 0).contains (.place "road" (.link (0, 1))) &&
  (legalMoves tinySettlers s 1).isEmpty
#guard after settlersGame fun s => (legalMoves tinySettlers s 0).isEmpty

/-! ## Part 4: renaming seats, and random games

Commandment II says that renaming every seat changes nothing but the names. `view` writes out
everything in a state that can be compared. -/

section Renaming

/-- Everything in a state that the test compares. Law bodies are compared as text. -/
structure View where
  turnOrder : List Seat
  phase : Phase
  round : Nat
  turnIndex : Nat
  turnsTaken : Nat
  rollsMade : Nat
  lastRoll : Option Nat
  seed : UInt64
  commitment : String
  balances : List Nat
  journal : List Entry
  pieces : List Piece
  laws : List String
  proposals : List String
  nextProposalId : Nat
  deals : List ActiveDeal
  dealsStarted : Nat
  offers : List Offer
  nextOfferId : Nat
  built : List (Seat × PieceKind)
  actions : List Nat
  eventsApplied : Nat
  winner : Option Seat
  deriving DecidableEq

/-- Write out a state. Accounts and action counts are read in that state's own order. -/
def view {G : GameDef} (s : State G) : View where
  turnOrder := s.turnOrder
  phase := s.phase
  round := s.round
  turnIndex := s.turnIndex
  turnsTaken := s.turnsTaken
  rollsMade := s.rollsMade
  lastRoll := s.lastRoll
  seed := s.seed
  commitment := s.seedCommitment
  balances := s.accounts.flatMap fun a => (resNames G).map (s.balance a)
  journal := s.journal
  pieces := s.pieces
  laws := s.laws.map fun x => toString (repr x)
  proposals := s.openProposals.map fun p => toString (repr p)
  nextProposalId := s.nextProposalId
  deals := s.deals
  dealsStarted := s.dealsStarted
  offers := s.offers
  nextOfferId := s.nextOfferId
  built := s.builtThisRound
  actions := s.turnOrder.map s.actionsThisTurn
  eventsApplied := s.eventsApplied
  winner := s.winner

def swapSeat (a b x : Seat) : Seat := if x = a then b else if x = b then a else x

theorem swapSeat_twice (a b x : Seat) : swapSeat a b (swapSeat a b x) = x := by
  unfold swapSeat
  split <;> rename_i h1
  · subst h1
    split <;> rename_i h2
    · subst h2; rfl
    · simp
  · split <;> rename_i h2
    · subst h2; simp
    · simp

/-- Swap two seat numbers. -/
def swapRenaming (a b : Seat) : Renaming where
  to := swapSeat a b
  back := swapSeat a b
  back_to := swapSeat_twice a b
  to_back := swapSeat_twice a b

/-- Rename by `τ`, then by `σ`. -/
def composeRenaming (σ τ : Renaming) : Renaming where
  to := σ.to ∘ τ.to
  back := τ.back ∘ σ.back
  back_to x := by simp [σ.back_to, τ.back_to]
  to_back x := by simp [σ.to_back, τ.to_back]

/-- Swaps two seats. -/
def swap01 : Renaming := swapRenaming 0 1

/-- Makes big, out-of-order seat numbers, so that order and size of numbers would show. -/
def bigNames : Renaming :=
  composeRenaming (swapRenaming 0 100) (composeRenaming (swapRenaming 1 7) (swapRenaming 2 55))

/-- Play the same events under a renaming, and compare every state with the renamed original. -/
def renamingFailures (G : GameDef) (σ : Renaming) (seats : Nat) (seed : UInt64) (events : List Event) :
    List String :=
  let start := testStart G seats seed
  (events.foldl
    (fun (acc : State G × State G × Nat × List String) e =>
      let (s, sr, i, fails) := acc
      match step G s e, step G sr (σ.event e) with
      | .ok s', .ok sr' =>
        (s', sr', i + 1,
          if view (σ.state s') == view sr' then fails else fails ++ [s!"event {i}: states differ"])
      | .error _, .error _ => (s, sr, i + 1, fails)
      | _, _ => (s, sr, i + 1, fails ++ [s!"event {i}: one was accepted and the other rejected"]))
    (start, σ.state start, 0, [])).2.2.2

#guard renamingFailures tinySettlers swap01 2 42 settlersGameEvents == []
#guard renamingFailures tinySettlers bigNames 2 42 settlersGameEvents == []
#guard renamingFailures tinySpace bigNames 3 7 spaceGameEvents == []
#guard renamingFailures tinySettlers bigNames 2 42 winWithDeal == []
#guard renamingFailures tinySettlers bigNames 2 42 repealGame == []
#guard renamingFailures tinySettlers bigNames 2 42 (buildThenDeal ++ [endT 0, placeOn 1 "road" 1 2, endT 1]) == []
#guard renamingFailures tinySettlers bigNames 2 42 (dealStarted ++ [.exit 0 0, endT 1]) == []
#guard renamingFailures tinySettlers bigNames 2 42 (timedOut tinySettlers 2) == []
-- A test of the test: the same game without renaming the events is a different game.
#guard (play tinySettlers 2 42 settlersGameEvents).isSome &&
  (settlersGameEvents.foldlM (step tinySettlers) (swap01.state (testStart tinySettlers 2 42))).toOption.isNone

end Renaming

/-! ### Random games

A small generator drives whole games. It picks from legal moves, proposals from a fixed pool,
votes, signatures, notices and some events that should be rejected. It checks every claim after
every accepted event, and it runs a renamed copy of the game next to the real one. -/

section Random

variable {G : GameDef}

/-- The next number in a random sequence. -/
def nextRandom (x : UInt64) : UInt64 := scramble x

def pick {α : Type} (x : UInt64) (xs : List α) : Option α :=
  xs[x.toNat % xs.length]?

/-- A deal this seat can fund now: it pays another seat from what it holds, with a remainder when
it holds enough. -/
def fundedDeal (G : GameDef) (s : State G) (a b : Seat) (x : UInt64) : Option Deal :=
  let held := (G.resources.map (·.name)).filter fun r => decide (0 < seatBalance s a r)
  match pick x held with
  | none => none
  | some r =>
    let amount := seatBalance s a r
    let rounds := (x.toNat % 2) + 1
    if amount < rounds then
      some { title := "one round", signers := [a, b], rounds := 1, exitNotice := 0
             deposits := [(a, r, 1)]
             terms := [.everyRound [{ src := a, dst := .seat b, res := r, amount := 1 }]] }
    else
      some { title := "paid", signers := [a, b], rounds := rounds, exitNotice := x.toNat % 3
             deposits := [(a, r, amount)]
             terms := [.everyRound [{ src := a, dst := .seat b, res := r, amount := 1 }]] }

/-- Pick one event for this state, using a stream of random numbers. -/
def randomEvent (G : GameDef) (s : State G) (x : UInt64) : Event :=
  let x1 := nextRandom x
  let x2 := nextRandom x1
  let x3 := nextRandom x2
  let seat := (pick x1 s.turnOrder).getD 0
  let other := (pick x2 (s.turnOrder.filter (· != seat))).getD 0
  let cur := s.currentSeat.getD 0
  let resources := G.resources.map (·.name)
  let r0 := (pick x1 resources).getD ""
  let r1 := (pick x2 resources).getD ""
  let isDeal (p : OpenProposal) : Bool := match p.body with
    | .deal _ => true
    | .law _ => false
  let openLawId := (pick x1 ((s.openProposals.filter (!isDeal ·)).map (·.id))).getD 0
  let openDeal := pick x1 (s.openProposals.filter isDeal)
  let dealId := (pick x1 (s.deals.map (·.id))).getD 0
  let voted : List Seat := match s.openProposal? openLawId with
    | some (p : OpenProposal) => p.votes.map (·.1)
    | none => []
  let voter := (pick x2 (s.turnOrder.filter fun q => !voted.contains q)).getD seat
  let legal := (legalMoves G s cur).filter (· != .endTurn)
  -- With nothing useful to do, try a deal, or else send an event that is rejected.
  let fallback : Event :=
    match fundedDeal G s seat other x3 with
    | some d => .propose seat (.deal d)
    | none => .exit 999 999
  match x.toNat % 40 with
  | 0 | 37 => endT cur
  | 1 => .forceEndTurn
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
      match pick x1 legal with
      | some m => .move cur m
      | none => fallback
  | 10 | 11 | 12 =>
      match pick x1 (lawPool G s) with
      | some L => .propose seat (.law L)
      | none => fallback
  | 13 | 14 =>
      match pick x1 (dealPool G seat other (x3.toNat % 3)) with
      | some d => .propose seat (.deal d)
      | none => fallback
  | 15 | 16 | 17 | 18 | 19 | 20 =>
      match fundedDeal G s seat other x2 with
      | some d => .propose seat (.deal d)
      | none => .exit 999 999
  | 21 | 22 | 23 | 24 | 25 => .vote voter openLawId (x2.toNat % 8 != 0)
  | 26 | 27 | 28 | 29 | 30 | 31 | 32 =>
      match openDeal with
      | some p =>
        let signed := p.signed
        let signers : List Seat := match p.body with
          | .deal d => d.signers
          | .law _ => []
        .sign ((pick x2 (signers.filter fun q => !signed.contains q)).getD seat) p.id
      | none => fallback
  | 33 => .exit seat dealId
  | 34 => .move cur (.offer (if x2.toNat % 2 == 0 then none else some other) [(r0, 1)] [(r1, 1)])
  | 35 | 36 =>
      match s.offers.head? with
      | some o => .move seat (.accept o.id)
      | none => .move seat (.bankTrade r0 r1)
  | _ =>
      match x1.toNat % 4 with
      | 0 => .vote 999 openLawId true
      | 1 => .move 999 .endTurn
      | 2 => .exit other 999
      | _ => .move seat (.place "not a piece" (.spot 0))

/-- A larger map, so that random games last and use deals, laws and refunds. -/
def bigLand : GameDef :=
  { tinySettlers with
    name := "Big Land"
    map :=
      { spotCount := 12
        links := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10),
                  (10, 11), (11, 0)]
        regions := [⟨"grain", 1, [0, 3, 6, 9]⟩, ⟨"timber", 2, [1, 4, 7, 10]⟩, ⟨"brick", 3, [2, 5, 8, 11]⟩] }
    targetPoints := 12
    rounds := 12
    resources := [⟨"grain", 40⟩, ⟨"timber", 40⟩, ⟨"brick", 40⟩] }

example : bigLand.Valid := by decide

/-- The result of a random game. -/
structure RandomResult (G : GameDef) where
  fails : List String
  accepted : Nat
  final : State G

/-- Play `fuel` random events, checking every claim and a renamed copy after each accepted one. -/
def randomGame (G : GameDef) (σ : Renaming) (seats : Nat) (seed : UInt64) (fuel : Nat) :
    RandomResult G :=
  let start := initialState G seats seed [seed + 1]
  let rec go : Nat → State G → State G → UInt64 → Nat → List String → RandomResult G
    | 0, s, _, _, n, fails => ⟨fails, n, s⟩
    | k + 1, s, sr, x, n, fails =>
      let e := randomEvent G s x
      let x' := nextRandom (nextRandom (nextRandom (nextRandom x)))
      match step G s e, step G sr (σ.event e) with
      | .ok s', .ok sr' =>
        let renamed := if view (σ.state s') == view sr' then [] else ["II: states differ"]
        go k s' sr' x' (n + 1)
          (fails ++ renamed ++ stepClaims s s' e ++ buildClaims s' ++ claimSeedForm s' seed [seed + 1])
      | .error _, .error _ => go k s sr x' n fails
      | _, _ => go k s sr x' n (fails ++ ["II: one was accepted and the other rejected"])
  go fuel start (σ.state start) (seed * 31 + 17) 0 []

#guard (randomGame bigLand bigNames 4 1 150).fails == []
#guard (randomGame bigLand swap01 3 2 150).fails == []
#guard (randomGame tinySettlers bigNames 2 3 120).fails == []
#guard (randomGame tinySpace bigNames 3 4 120).fails == []

end Random

/-! ## New checks of the spec's words -/

-- A deal rejects a deposit from a non-signer. A no-trade term needs a signer first, and may name
-- any other seat in the game second.
#guard rejects (settlers2 seat1Turn)
  (.propose 1 (.deal { timberDeal with deposits := [(1, "timber", 3), (0, "grain", 0)], signers := [1, 3] }))
#guard rejects (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0
                       deposits := [(2, "alloy", 0)], terms := [] }))
#guard accepts (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
                       terms := [.noTrade 0 2] }))
#guard rejects (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
                       terms := [.noTrade 2 0] }))
#guard rejects (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
                       terms := [.noTrade 0 9] }))
#guard rejects (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
                       terms := [.noTrade 0 0] }))
#guard rejects (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
                       terms := [.noBuild 2 "lane" [0]] }))
#guard accepts (play tinySpace 3 7 spaceSetup)
  (.propose 0 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
                       terms := [.noTrade 0 1] }))

/-- A state with a running deal whose terms name a seat that did not sign. No engine path makes
this, so it tests the words directly: a deal binds only its signers. -/
def nonSignerTerms : State tinySpace :=
  { testStart tinySpace 3 7 with
    deals := [{ id := 0, lastRound := 5, startRound := 1, builtBefore := 0
                deal := { title := "x", signers := [0, 1], rounds := 5, exitNotice := 0, deposits := []
                          terms := [.noBuild 2 "lane" [0], .noTrade 2 0, .noBuild 0 "lane" [0], .noTrade 1 0] } }] }

#guard !nonSignerTerms.blockedByDeal 2 "lane" (.spot 0)
#guard nonSignerTerms.blockedByDeal 0 "lane" (.spot 0)
#guard !nonSignerTerms.tradeBlocked 2 0
#guard !nonSignerTerms.tradeBlocked 0 2
#guard nonSignerTerms.tradeBlocked 0 1
#guard nonSignerTerms.tradeBlocked 1 0

-- A law's title has no meaning: the same clauses with another title do the same.
#guard after (settlers2 (seat0HasGrain ++ [.propose 0 (.law { cheapCities with title := "Free castles" }),
    .vote 0 0 true, .vote 1 0 true])) fun s => s.costOf "city" == [("grain", 2)]
#guard Law.size cheapCities == 1
#guard Law.size rentLaw == 5
-- An upgrade removes one piece, and all others stay in order.
#guard after settlersGame fun s =>
  s.pieces.map (fun x => (x.owner, x.kind)) ==
    [(0, "settlement"), (0, "road"), (1, "road"), (1, "road"), (0, "settlement"), (0, "road"),
     (1, "city"), (1, "city")]

/-! ## Each event's entries, on concrete games -/

-- A bank trade and an accepted offer make exactly their entries, and the claims hold on them.
#guard after (settlers2 seat1Turn) fun s =>
  match step tinySettlers s (.move 1 (.bankTrade "timber" "grain")) with
  | .ok s2 => newEntries s s2 == s.bankTradeEntries 1 "timber" "grain"
  | .error _ => false
#guard traceFailures tinySettlers 2 42 (seat1Turn ++ [.move 1 (.bankTrade "timber" "grain")]) == []
#guard traceFailures tinySettlers 2 42 (seat1OfferRound2 ++ [.move 0 (.accept 0)]) == []

-- A proposed deal, a signature that is not the last, and an exit make no entries.
#guard after (settlers2 (dealProposed ++ [.sign 0 0])) fun s =>
  s.journal.getLast?.map (·.reason) != some .setDeposit
#guard after (settlers2 dealStarted) fun s =>
  match step tinySettlers s (.exit 0 0) with
  | .ok s2 => (newEntries s s2).isEmpty
  | .error _ => false
-- The last signature makes exactly the deal's deposits.
#guard depositEntries 3 timberDeal == [⟨.player 1, .deposit 3 1, "timber", 3, .setDeposit⟩]
-- A vote that does not end the game makes no entries.
#guard after (settlers2 lawOpen) fun s =>
  match step tinySettlers s (.vote 0 0 true) with
  | .ok s2 => (newEntries s s2).isEmpty
  | .error _ => false
-- A vote that ends the game makes only refunds. Here a law makes settlements worth enough to win.
def bigSettlements : Law := { title := "Big", clauses := [.setPoints "settlement" 4] }

#guard after (settlers2 (settlersRound2 ++ [.propose 0 (.law bigSettlements), endT 0,
    .propose 1 (.deal timberDeal), .sign 0 1, .sign 1 1, .vote 0 0 true])) fun s =>
  match step tinySettlers s (.vote 1 0 true) with
  | .ok s2 =>
    s2.phase == .ended && !(newEntries s s2).isEmpty &&
    (newEntries s s2).all (·.reason == .refund) &&
    newEntries s s2 == s.deals.flatMap s.refundEntries
  | .error _ => false

/-! ## Deals and laws cannot be switched off -/

#guard after (settlers2 seat1Turn) fun s =>
  (dealProblems s timberDeal).isEmpty && (step tinySettlers s (.propose 1 (.deal timberDeal))).toOption.isSome
-- A seat that does not sign a deal cannot propose it, even if the deal is fine.
#guard after (play tinySpace 3 7 spaceSetup) fun s =>
  (step tinySpace s (.propose 2 (.deal { title := "x", signers := [0, 1], rounds := 1, exitNotice := 0
                                         deposits := [], terms := [] }))).toOption.isNone
#guard after (settlers2 seat0HasGrain) fun s =>
  (lawProblems tinySettlers s cheapCities).isEmpty &&
  (step tinySettlers s (.propose 0 (.law cheapCities))).toOption.isSome

/-! ## Prices cannot list a resource twice

A price that lists a resource twice could pass `affords` and still fail to post. `GameDef.bundleOk`
now rejects it, so such a game is not valid, and no law can bring it back. -/

def doublePrice : GameDef :=
  { tinySettlers with
    pieces := tinySettlers.pieces.map fun p =>
      if p.name == "road" then { p with cost := [("timber", 1), ("timber", 1)] } else p }

theorem doublePrice_invalid : ¬ doublePrice.Valid := by decide

/-! ## Every seat can always place its setup pieces

This search uses the real engine. It tries every legal setup of Tiny Settlers with two seats, and
at each point it requires a legal placement of the next setup piece. A Python copy of the placement
rules searched the same setup and Tiny Space with three seats, whose search is too big to run in
every build. Tiny Space is checked here on many random setups instead. -/

section SetupSearch

variable {G : GameDef}

/-- Legal placements of this seat's next setup piece. -/
def setupOptions (s : State G) (p : Seat) : List Move :=
  (legalMoves G s p).filter (· != .endTurn)

/-- Search all ways to finish `pieces` more placements, then the rest of setup. Returns the count
of setups finished, or `none` if a seat could not place its next piece. -/
def setupSearch : Nat → State G → Option Nat
  | 0, _ => some 1
  | k + 1, s =>
    match s.currentSeat with
    | none => none
    | some p =>
      if s.actionsThisTurn p < G.setupPieces.length then
        let options := setupOptions s p
        if options.isEmpty then none
        else
          options.foldl
            (fun acc m =>
              match acc, step G s (.move p m) with
              | some n, .ok s' =>
                match setupSearch k s' with
                | some c => some (n + c)
                | none => none
              | _, _ => none)
            (some 0)
      else
        match step G s (.move p .endTurn) with
        | .ok s' => setupSearch k s'
        | .error _ => none

/-- Random setups: each seat picks a random legal placement. True if none got stuck. -/
def randomSetupOk (G : GameDef) (seats : Nat) (seed : UInt64) : Bool :=
  let rec go : Nat → State G → UInt64 → Bool
    | 0, _, _ => true
    | k + 1, s, x =>
      match s.currentSeat with
      | none => false
      | some p =>
        if s.actionsThisTurn p < G.setupPieces.length then
          match pick x (setupOptions s p) with
          | none => false
          | some m =>
            match step G s (.move p m) with
            | .ok s' => go k s' (nextRandom x)
            | .error _ => false
        else
          match step G s (.move p .endTurn) with
          | .ok s' => go k s' (nextRandom x)
          | .error _ => false
  go (2 * seats * (G.setupPieces.length + 1)) (initialState G seats seed [seed + 1]) (seed * 31 + 7)

end SetupSearch

-- Four settlements and four roads, then the turn ends. Every path gets through, 12 steps long.
#guard (setupSearch 12 (testStart tinySettlers 2 42)).isSome
#guard (List.range 200).all fun i => randomSetupOk tinySpace 3 (UInt64.ofNat i)

/-! ## No law can stall the game

A `forEach` inside a `forEach` multiplies the entries by the number of seats each time. `Law.size`
does not see this, so `lawProblems` also limits the entries a law can plan. -/

/-- `depth` `forEach` clauses, one inside another, around one transfer. -/
def nestedEach : Nat → Effect
  | 0 => .transfer .each .treasury (.lit "grain") (.lit 1)
  | n + 1 => .forEach .yes [nestedEach n]

def deepLaw (depth : Nat) : Law := badLaw [.onRoundEnd [nestedEach depth]]

/-- One `forEach` with this many transfers. -/
def wideLaw (transfers : Nat) : Law :=
  badLaw [.onRoundEnd [.forEach .yes (List.replicate transfers (nestedEach 0))]]

def sixSeats : State tinySettlers := testStart tinySettlers 6 42

-- The law that used to hang the server is small enough, and it would plan about a billion entries.
#guard (deepLaw 30).size == 63
#guard (deepLaw 30).size ≤ maxLawSize
#guard (deepLaw 30).plannedEntries 2 == 2 ^ 30
-- It is now rejected, for these three reasons: it is too big alone, the total is too big, and so is what
-- the laws would read.
#guard after (settlers2 seat0HasGrain) fun s =>
  lawProblems tinySettlers s (deepLaw 30) ==
    ["this law could make too many payments at once",
     "the laws in force could make too many payments at once",
     "the laws in force would read too many numbers at once"]
#guard rejects (settlers2 seat0HasGrain) (.propose 0 (.law (deepLaw 30)))
-- Sensible laws still pass, in the smallest and the largest game.
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law (deepLaw 1)))
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law (deepLaw 2)))
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law rentLaw))
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law dividend))
#guard accepts (settlers2 seat0HasGrain) (.propose 0 (.law brickSweep))
#guard (lawProblems tinySettlers sixSeats rentLaw).isEmpty
#guard (lawProblems tinySettlers sixSeats (deepLaw 2)).isEmpty
-- The limit, at 6 seats. 21 transfers per seat pass, and 22 do not.
#guard (wideLaw 21).plannedEntries 6 == 126
#guard (lawProblems tinySettlers sixSeats (wideLaw 21)).isEmpty
#guard (wideLaw 22).plannedEntries 6 == 132
#guard !(lawProblems tinySettlers sixSeats (wideLaw 22)).isEmpty
-- Three levels pass at 2 seats and fail at 6, because the cost depends on the seats.
#guard after (settlers2 seat0HasGrain) fun s => (lawProblems tinySettlers s (deepLaw 3)).isEmpty
#guard !(lawProblems tinySettlers sixSeats (deepLaw 3)).isEmpty
-- A law at the limit plays through a round's end, and the claims hold.
#guard traceFailures tinySettlers 2 42
  (settlersRound2 ++ [.propose 0 (.law (deepLaw 7)), .vote 0 0 true, .vote 1 0 true, endT 0, endT 1]) == []
#guard after (settlers2 (settlersRound2 ++ [.propose 0 (.law (deepLaw 7)), .vote 0 0 true, .vote 1 0 true]))
  fun s => (deepLaw 7).plannedEntries 2 == 128 && s.laws.length == 1

/-! ## Laws that would do nothing -/

def goodTower : PieceDef :=
  { name := "tower", cost := [("timber", 1)], points := 1, placement := .attach "settlement"
    yield := 0, limit := 1 }

def lawRejected (clauses : List Clause) : Bool :=
  rejects (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw clauses)))

def lawAccepted (clauses : List Clause) : Bool :=
  accepts (settlers2 seat0HasGrain) (.propose 0 (.law (badLaw clauses)))

def payTreasury (amount : Expr) : Effect := .transfer .actor .treasury (.lit "grain") amount

-- Division by zero is rejected wherever it appears, and other division still passes.
#guard lawRejected [.onHarvest [payTreasury (.div (.lit 4) 0)]]
#guard lawRejected [.onHarvest [payTreasury (.add (.lit 1) (.div .harvestedAmount 0))]]
#guard lawRejected [.onHarvest [.when (.lt (.div (.lit 4) 0) (.lit 1)) [payTreasury (.lit 1)]]]
#guard lawRejected [.onRoundEnd [.forEach (.not (.eq (.div (.lit 4) 0) (.lit 1))) [nestedEach 0]]]
#guard lawAccepted [.onHarvest [payTreasury (.div .harvestedAmount 2)]]
-- A clause that sets a piece's cost or points must come after the clause that makes the piece.
#guard lawRejected [.setCost "tower" [("grain", 1)], .newPiece goodTower]
#guard lawRejected [.setPoints "tower" 3, .newPiece goodTower]
#guard lawAccepted [.newPiece goodTower, .setCost "tower" [("grain", 1)]]
#guard lawAccepted [.newPiece goodTower, .setPoints "tower" 3]
-- A rule with no effects is rejected.
#guard lawRejected [.onHarvest []]
#guard lawRejected [.onRoundEnd []]
#guard lawRejected [.onBuild "road" []]
#guard lawRejected [.onRoundEnd [.forEach .yes []]]
#guard lawRejected [.onRoundEnd [.when .yes []]]
-- A transfer can name only who and what exists where it runs.
#guard lawRejected [.onRoundEnd [.transfer .actor .treasury (.lit "grain") (.lit 1)]]
#guard lawRejected [.onHarvest [.transfer .each .treasury (.lit "grain") (.lit 1)]]
#guard lawRejected [.onBuild "road" [.transfer .actor .treasury .harvested (.lit 1)]]
#guard lawAccepted [.onHarvest [.transfer .actor .treasury .harvested (.lit 1)]]
-- A clause that a later clause replaces is rejected. So is a repeated repeal.
#guard lawRejected [.setBankRate 2, .setBankRate 3]
#guard lawRejected [.setCost "road" [], .setCost "road" [("grain", 1)]]
#guard lawRejected [.setPoints "road" 1, .setPoints "road" 2]
#guard lawAccepted [.setCost "road" [], .setPoints "road" 1, .setBankRate 2]
#guard lawRejected [.newPiece { goodTower with limit := 0 }]
#guard lawRejected [.newPiece { goodTower with placement := .attach "tower" }]
#guard lawRejected [.newPiece { goodTower with placement := .upgrade "tower" }]

-- A piece that could never be built is rejected. `upgrade` and `attach` need a spot, and a road is on
-- a link.
def flagOn (p : Placement) : PieceDef :=
  { name := "flag", cost := [], points := 1, placement := p, yield := 0, limit := 1 }

#guard lawRejected [.newPiece (flagOn (.attach "road"))]
#guard lawRejected [.newPiece (flagOn (.upgrade "road"))]
-- The same through a chain, a loop, or a target that can never be built.
#guard lawRejected [.newPiece (flagOn (.attach "road")),
  .newPiece { flagOn (.attach "flag") with name := "pole" }]
#guard lawRejected [.newPiece (flagOn (.attach "pole")),
  .newPiece { flagOn (.attach "flag") with name := "pole" }]
#guard lawRejected [.newPiece { flagOn .spot with limit := 0 },
  .newPiece { flagOn (.attach "flag") with name := "pole" }]
-- Pieces that can stand on a spot still work as targets, directly or through a chain.
#guard lawAccepted [.newPiece (flagOn (.attach "settlement"))]
#guard lawAccepted [.newPiece (flagOn (.upgrade "settlement"))]
#guard lawAccepted [.newPiece (flagOn (.attach "city"))]
#guard lawAccepted [.newPiece (flagOn (.attach "settlement")),
  .newPiece { flagOn (.attach "flag") with name := "pole" }]
#guard lawAccepted [.newPiece (flagOn .spot)]
#guard lawAccepted [.newPiece (flagOn .link)]
-- A law cannot set a price on a piece that its own repeal removes, or use it in a rule.
def towerInForce : State tinySettlers :=
  { testStart tinySettlers 2 42 with laws := [(5, badLaw [.newPiece goodTower])] }

#guard (lawProblems tinySettlers towerInForce (badLaw [.setCost "tower" []])).isEmpty
#guard !(lawProblems tinySettlers towerInForce (badLaw [.repeal 5, .setCost "tower" []])).isEmpty
#guard !(lawProblems tinySettlers towerInForce (badLaw [.setCost "tower" [], .repeal 5])).isEmpty
#guard !(lawProblems tinySettlers towerInForce
  (badLaw [.repeal 5, .onBuild "tower" [payTreasury (.lit 1)]])).isEmpty
#guard !(lawProblems tinySettlers towerInForce (badLaw [.repeal 5, .repeal 5])).isEmpty
#guard (lawProblems tinySettlers towerInForce (badLaw [.repeal 5])).isEmpty
#guard !(lawProblems tinySettlers towerInForce
  (badLaw [.repeal 5, .newPiece (flagOn (.attach "tower"))])).isEmpty
#guard (lawProblems tinySettlers towerInForce (badLaw [.newPiece (flagOn (.attach "tower"))])).isEmpty

-- A shortfall can round down to nobody being paid, and a repealed piece stays, worth 0.
#guard after (play shortBank 2 42 shortBankGame) fun s =>
  (settle s [⟨.bank, .player 0, "grain", 1, .harvest⟩, ⟨.bank, .player 1, "grain", 1, .harvest⟩]).isEmpty
#guard
  let s : State tinySettlers := { towerInForce with pieces := [⟨0, "tower", .spot 0⟩] }
  s.pointsOf 0 == 1 && ({ s with laws := [] } : State tinySettlers).pointsOf 0 == 0

/-! ## Laws that react to the roll -/

/-- Tiny Sevens, with a seed whose rolls start 7, 7, 3. -/
def sevens2 (events : List Event) : Option (State tinySevens) :=
  (replay tinySevens 2 42 [3] events).toOption

/-- The next turn change, from the state after these events. -/
def nextTurn (events : List Event) : Option (State tinySevens × State tinySevens) :=
  match sevens2 events with
  | none => none
  | some s =>
    match step tinySevens s .forceEndTurn with
    | .ok s' => some (s, s')
    | .error _ => none

def forced (n : Nat) : List Event := List.replicate n .forceEndTurn

#guard after (sevens2 []) fun s => (List.range 3).map (rollAt tinySevens s.seed) == [7, 7, 3]
-- A law fires on a 7, a roll that no hex on this map pays. The actor is the seat whose turn starts.
#guard (nextTurn (forced 3)).any fun (s, s') =>
  s'.lastRoll == some 7 && s'.currentSeat == some 0 && s.nextRoller == some 0 &&
  newEntries s s' ==
    [⟨.bank, .player 0, "timber", 1, .lawEffect⟩, ⟨.bank, .player 0, "grain", 1, .lawEffect⟩,
     ⟨.bank, .player 1, "grain", 1, .lawEffect⟩]
#guard (nextTurn (forced 4)).any fun (s, s') =>
  s'.lastRoll == some 7 && s'.currentSeat == some 1 && s.nextRoller == some 1 &&
  (newEntries s s').head? == some ⟨.bank, .player 1, "timber", 1, .lawEffect⟩
-- The third roll is a 3, so the law moves nothing. The turn wraps round to seat 0.
#guard (nextTurn (forced 5)).any fun (s, s') =>
  s'.lastRoll == some 3 && s.nextRoller == some 0 && (newEntries s s').isEmpty
-- During setup no roll comes next, so there is no roller.
#guard after (sevens2 (forced 1)) fun s => s.nextRoller == none
-- At the end of the last round there is no roll, so no roll law fires.
#guard after (sevens2 (forced (maxTurns tinySevens 2 - 1))) fun s =>
  s.nextRoller == none && (nextStage s).rolls == false &&
  predictNextTurn tinySevens s 7 == s.entriesBeforeRoll
-- The law fires through the whole game, and every claim holds at every step.
#guard traceFailures tinySevens 2 42 (forced (maxTurns tinySevens 2)) == []

/-- Seat 0 has a settlement on the brick hex, which pays on a 3. The first two rolls are 7. -/
def sevensWithBrick : List Event :=
  [placeAt 0 "settlement" 0, placeOn 0 "road" 0 1, endT 0] ++ forced 4

/-- A tithe on harvest and a law that empties the treasury to the seat whose turn starts. -/
def orderLaws : List (Nat × Law) :=
  [ (0, { title := "tithe", clauses := [.onHarvest [.transfer .actor .treasury .harvested (.lit 1)]] })
  , (1, { title := "sweep", clauses := [.onRoll
      [.transfer .treasury .actor (.lit "brick") (.holding .treasury (.lit "brick"))]] }) ]

-- The order within a roll: the bank pays, the laws react to that payment, then the roll law runs. The
-- roll law sees the treasury after the tithe. Planned earlier, it would see an empty treasury.
#guard after (sevens2 sevensWithBrick) fun s =>
  let t : State tinySevens := { s with laws := orderLaws }
  rollEntries t 3 ==
    [⟨.bank, .player 0, "brick", 1, .harvest⟩,
     ⟨.player 0, .treasury, "brick", 1, .lawEffect⟩,
     ⟨.treasury, .player 0, "brick", 1, .lawEffect⟩] &&
  rollEntries t 3 == harvestEntries t 3 ++ [⟨.treasury, .player 0, "brick", 1, .lawEffect⟩]
-- With no roll law, the entries are the harvest alone.
#guard after (sevens2 sevensWithBrick) fun s =>
  let t : State tinySevens := { s with laws := [] }
  rollEntries t 3 == harvestEntries t 3 && rollEntries t 3 == [⟨.bank, .player 0, "brick", 1, .harvest⟩]
-- Rolls that no hex pays still run the law, and a game with no roll law writes nothing on them.
#guard after (sevens2 sevensWithBrick) fun s =>
  rollEntries ({ s with laws := [] } : State tinySevens) 7 == [] && !(rollEntries s 7).isEmpty

/-- The 7 penalty: a seat holding more than 7 in total pays half of each resource to the bank. -/
def sevenPenalty : Law :=
  { title := "Seven penalty"
    clauses := [.onRoll [.forEach
      (.and (.eq .rolled (.lit 7))
        (.lt (.lit 7) (.add (.add (.holding .each (.lit "grain")) (.holding .each (.lit "timber")))
          (.holding .each (.lit "brick")))))
      [ .transfer .each .bank (.lit "grain") (.div (.holding .each (.lit "grain")) 2)
      , .transfer .each .bank (.lit "timber") (.div (.holding .each (.lit "timber")) 2)
      , .transfer .each .bank (.lit "brick") (.div (.holding .each (.lit "brick")) 2) ]]] }

/-- Seat 0 holds 5 grain and 4 timber. Seat 1 holds 7 grain. -/
def penaltyGame : Option (State tinySevens) :=
  (sevens2 (forced 3)).map fun s =>
    ({ s with laws := [(0, sevenPenalty)] } : State tinySevens).afterPosting
      [⟨.bank, .player 0, "grain", 5, .harvest⟩, ⟨.bank, .player 0, "timber", 4, .harvest⟩,
       ⟨.bank, .player 1, "grain", 7, .harvest⟩]

-- On a 7, only the seat over 7 pays, half of each resource, rounded down. Nobody pays on an 8.
#guard after penaltyGame fun s =>
  rollEntries s 7 == [⟨.player 0, .bank, "grain", 2, .lawEffect⟩, ⟨.player 0, .bank, "timber", 2, .lawEffect⟩] &&
  rollEntries s 8 == []
#guard (lawProblems tinySettlers sixSeats sevenPenalty).isEmpty

-- `rolled` is the total shown, and 0 outside a roll, as `harvestedAmount` is.
#guard after (settlers2 []) fun s =>
  Expr.rolled.eval s (Trigger.roll 1 9).env == 9 &&
  Expr.rolled.eval s (Trigger.roundEnd).env == 0 &&
  Expr.rolled.eval s (Trigger.build 0 "road").env == 0 &&
  Expr.rolled.eval s (Trigger.harvest 0 "grain" 2).env == 0
-- `harvestedAmount` is 0 on a roll trigger, and an `actor` exists there.
#guard after (settlers2 []) fun s =>
  Expr.harvestedAmount.eval s (Trigger.roll 1 9).env == 0 &&
  (Party.actor.account (Trigger.roll 1 9).env) == some (.player 1)

-- The checks treat a roll clause as they treat a harvest clause.
#guard lawAccepted [.onRoll [.transfer .actor .treasury (.lit "grain") (.lit 1)]]
#guard lawAccepted [.onRoll [.when (.eq .rolled (.lit 7)) [.transfer .bank .treasury (.lit "grain") .rolled]]]
#guard lawAccepted [.onRoll [.forEach (.eq .rolled (.lit 2)) [.transfer .each .treasury (.lit "grain") (.lit 1)]]]
#guard lawRejected [.onRoll []]
#guard lawRejected [.onRoll [.when .yes []]]
#guard lawRejected [.onRoll [.forEach .yes []]]
#guard lawRejected [.onRoll [.transfer .each .treasury (.lit "grain") (.lit 1)]]
#guard lawRejected [.onRoll [.transfer .actor .treasury .harvested (.lit 1)]]
#guard lawRejected [.onRoll [.transfer .bank .bank (.lit "grain") (.lit 1)]]
#guard lawRejected [.onRoll [payTreasury (.div .rolled 0)]]
#guard lawRejected [.onRoll [.when (.lt (.div .rolled 0) (.lit 1)) [payTreasury (.lit 1)]]]
-- A number that names `rolled` outside a roll clause passes, and it is 0 there, as `harvestedAmount` is.
#guard lawAccepted [.onRoundEnd [.transfer .bank .treasury (.lit "grain") .rolled]]
#guard lawAccepted [.onHarvest [.transfer .actor .treasury .harvested .rolled]]
#guard lawAccepted [.onRoundEnd [.transfer .bank .treasury (.lit "grain") .harvestedAmount]]
-- Roll clauses count in both payment caps.
#guard (badLaw [.onRoll [nestedEach 0, .forEach .yes [nestedEach 0]]]).plannedEntries 6 == 7
#guard !(lawProblems tinySettlers sixSeats (badLaw [.onRoll [.forEach .yes (List.replicate 22 (nestedEach 0))]])).isEmpty
#guard (lawProblems tinySettlers sixSeats (badLaw [.onRoll [.forEach .yes (List.replicate 21 (nestedEach 0))]])).isEmpty
#guard plannedTotal [(0, badLaw [.onRoll [.forEach .yes [nestedEach 0]]])] 6 == 6
#guard (lawProblems tinySettlers
    { sixSeats with laws := [(0, badLaw [.onRoll [.forEach .yes (List.replicate 21 (nestedEach 0))]]),
                             (1, badLaw [.onRoll [.forEach .yes (List.replicate 21 (nestedEach 0))]])] }
    (badLaw [.onRoll [.forEach .yes (List.replicate 21 (nestedEach 0))]])) ==
  ["the laws in force could make too many payments at once"]
-- A roll law cannot change the roll: the dice are the same with and without one.
#guard after (sevens2 (forced 5)) fun s =>
  let bare := initialState { tinySevens with foundingLaws := [] } 2 42 [3]
  s.seed == bare.seed && (List.range 40).all fun k =>
    rollAt tinySevens s.seed k == rollAt { tinySevens with foundingLaws := [] } bare.seed k

/-! ## Game definitions that are rejected -/

def linksAre (links : List (Nat × Nat)) : GameDef :=
  { tinySettlers with map := { tinySettlers.map with links := links } }

def withPlacement (p : Placement) : GameDef :=
  { tinySettlers with
    pieces := tinySettlers.pieces ++
      [{ name := "extra", cost := [], points := 1, placement := p, yield := 0, limit := 1 }] }

theorem duplicate_link_invalid : ¬ (linksAre [(0, 1), (0, 1)]).Valid := by decide
theorem reversed_link_invalid : ¬ (linksAre [(0, 1), (1, 0)]).Valid := by decide
theorem upgrade_of_nothing_invalid : ¬ (withPlacement (.upgrade "castle")).Valid := by decide
theorem attach_to_nothing_invalid : ¬ (withPlacement (.attach "castle")).Valid := by decide
theorem upgrade_of_itself_invalid : ¬ (withPlacement (.upgrade "extra")).Valid := by decide
theorem attach_to_link_piece_invalid : ¬ (withPlacement (.attach "road")).Valid := by decide
theorem upgrade_of_link_piece_invalid : ¬ (withPlacement (.upgrade "road")).Valid := by decide
theorem link_piece_with_no_links_invalid : ¬ (linksAre []).Valid := by decide

/-- A game with these extra pieces. -/
def withPieces (extra : List PieceDef) : GameDef :=
  { tinySettlers with pieces := tinySettlers.pieces ++ extra }

def extraOn (name : String) (p : Placement) : PieceDef :=
  { name := name, cost := [], points := 1, placement := p, yield := 0, limit := 1 }

theorem chain_to_link_piece_invalid :
    ¬ (withPieces [extraOn "a" (.attach "road"), extraOn "b" (.attach "a")]).Valid := by decide
theorem placement_loop_invalid :
    ¬ (withPieces [extraOn "a" (.attach "b"), extraOn "b" (.attach "a")]).Valid := by decide
theorem limit_zero_piece_invalid :
    ¬ (withPieces [{ extraOn "a" .spot with limit := 0 }]).Valid := by decide
theorem target_with_limit_zero_invalid :
    ¬ (withPieces [{ extraOn "a" .spot with limit := 0 }, extraOn "b" (.attach "a")]).Valid := by decide

example : (withPieces [extraOn "a" (.attach "city"), extraOn "b" (.attach "a")]).Valid := by decide

-- `canStandOnSpot` on its own: a target with a limit of 0 cannot stand anywhere. Whole games and laws
-- already reject such a piece, so only this direct test sees the helper's own check.
#guard canStandOnSpot [extraOn "a" .spot] 1 "a"
#guard !canStandOnSpot [{ extraOn "a" .spot with limit := 0 }] 1 "a"

example : (linksAre [(0, 1), (1, 2)]).Valid := by decide
example : (withPlacement (.upgrade "settlement")).Valid := by decide
example : (withPlacement (.attach "city")).Valid := by decide

/-! ## A new game needs seats and nonces -/

def replayRejected (seats : Nat) (nonces : List UInt64) : Bool :=
  ((replay tinySettlers seats 42 nonces [] : Except String (State tinySettlers)).toOption).isNone

#guard replayRejected 2 []
#guard replayRejected 1 [1]
#guard replayRejected 7 [1]
#guard replayRejected 0 [1]
#guard !replayRejected 2 [1]
#guard !replayRejected 6 [1]

/-! ## The small statements, on concrete steps -/

-- `nextStage`, through setup and a round.
#guard (settlers2 []).map nextStage == some (.setupTurn 1)
#guard (settlers2 [endT 0]).map nextStage == some (.setupTurn 1)
#guard (settlers2 [endT 0, endT 1]).map nextStage == some (.setupTurn 0)
#guard (settlers2 [endT 0, endT 1, endT 1]).map nextStage == some .firstRound
#guard (settlers2 [endT 0, endT 1, endT 1, endT 0]).map nextStage == some (.sameRound 1)
#guard (settlers2 [endT 0, endT 1, endT 1, endT 0, endT 0]).map nextStage == some .newRound
#guard (settlers2 (List.replicate (maxTurns tinySettlers 2 - 1) .forceEndTurn)).map nextStage ==
  some .gameOver

-- No seat has a veto: with 3 seats, one no vote does not stop two yes votes.
def spaceLawOpen : List Event := spaceSetup ++ [endT 0, endT 1, endT 2, .propose 0 (.deal alloyForOneRound),
  .sign 0 0, .sign 2 0, endT 0, .propose 1 (.law stationsWin)]

#guard after (space3 (spaceLawOpen ++ [.vote 0 1 false])) fun s =>
  s.openProposals.length == 1 && s.laws.isEmpty
#guard after (space3 (spaceLawOpen ++ [.vote 0 1 false, .vote 1 1 true])) fun s => s.laws.isEmpty
#guard after (space3 (spaceLawOpen ++ [.vote 0 1 false, .vote 1 1 true, .vote 2 1 true])) fun s =>
  s.laws.map (·.1) == [1]
#guard traceFailures tinySpace 3 7 (spaceLawOpen ++ [.vote 0 1 false, .vote 1 1 true, .vote 2 1 true]) == []

/-! ### Measures -/

-- Inside a measure, `each` is the seat being measured, and a surrounding `each` comes back after it.
def richGame : State tinySettlers :=
  { testStart tinySettlers 3 42 with
    phase := .actions
    round := 4
    books := fun a r => match a, r with
      | .player 0, "grain" => 5 | .player 1, "grain" => 9 | .player 2, "grain" => 9
      | .treasury, "timber" => 4 | _, _ => 0 }

def held0 : Expr := .holding .each (.lit "grain")
def evalRich (e : Expr) : Nat := e.eval richGame {}
#guard evalRich (.totalOver .yes held0) == 23
#guard evalRich (.mostOver .yes held0) == 9
#guard evalRich (.leastOver .yes held0) == 5
#guard evalRich (.totalOver (.lt (.lit 5) held0) (.lit 1)) == 2
#guard evalRich (.leastOver (.lt (.lit 5) held0) held0) == 9
#guard evalRich (.mostOver (.lt (.lit 100) held0) held0) == 0
#guard evalRich (.leastOver (.lt (.lit 100) held0) held0) == 0
#guard evalRich (.totalOver (.lt (.lit 100) held0) held0) == 0
#guard evalRich .round == 4
#guard evalRich (.divBy (.lit 23) (.holding .treasury (.lit "timber"))) == 5
#guard evalRich (.divBy (.lit 23) (.holding .treasury (.lit "grain"))) == 0
-- A measure inside a `forEach`: each seat is compared with the most, and a tie passes both.
#guard Effect.planAll richGame [.forEach (.eq held0 (.mostOver .yes held0))
    [.transfer .bank .each (.lit "timber") (.lit 1)]] {} ==
  [⟨.bank, .player 1, "timber", 1, .lawEffect⟩, ⟨.bank, .player 2, "timber", 1, .lawEffect⟩]
-- Size counts what is inside a measure, and the payment caps count what the law around it plans.
#guard (Expr.totalOver (.lt (.lit 1) (.lit 2)) (.add (.lit 1) (.lit 2))).size == 7
#guard (Expr.divBy (.lit 1) (.lit 2)).size == 3
#guard (Expr.totalOver .yes (.lit 2)).reads 6 == 13
#guard (Expr.totalOver .yes (.totalOver .yes (.lit 2))).reads 6 == 85
#guard (Cond.lt (.lit 1) (.totalOver .yes (.lit 2))).reads 6 == 15
-- A literal zero below a division is refused. A zero that the law computes gives 0.
#guard lawRejected [.onHarvest [payTreasury (.divBy (.lit 4) (.lit 0))]]
#guard lawRejected [.onHarvest [payTreasury (.totalOver .yes (.div (.lit 4) 0))]]
#guard lawRejected [.onHarvest [.when (.lt (.mostOver (.lt (.lit 1) (.div (.lit 4) 0)) (.lit 1)) (.lit 1)) [payTreasury (.lit 1)]]]
#guard lawAccepted [.onHarvest [payTreasury (.divBy (.lit 4) (.holding .treasury (.lit "grain")))]]
#guard lawAccepted [.onHarvest [payTreasury (.mostOver .yes (.points .each))]]
#guard lawAccepted [.onRoll [payTreasury .round]]

/-! ### Declarations -/

def declareSetup : List Event := settlersRound2

-- On your own turn, for a real resource, within the limit. No entries, and it counts as an action.
#guard after (settlers2 declareSetup) fun s => s.currentSeat == some 0 && s.phase == .actions
#guard accepts (settlers2 declareSetup) (.move 0 (.declare "grain" 5))
#guard accepts (settlers2 declareSetup) (.move 0 (.declare "grain" maxDeclared))
#guard rejects (settlers2 declareSetup) (.move 0 (.declare "grain" (maxDeclared + 1)))
#guard rejects (settlers2 declareSetup) (.move 0 (.declare "gold" 5))
#guard rejects (settlers2 declareSetup) (.move 1 (.declare "grain" 5))
#guard rejects (settlers2 declareSetup) (.move 7 (.declare "grain" 5))
#guard after (settlers2 (declareSetup ++ [.move 0 (.declare "grain" 5)])) fun s =>
  s.declared 0 "grain" == 5 && s.declared 0 "timber" == 0 && s.declared 1 "grain" == 0 &&
  s.actionsThisTurn 0 == 1
-- A later declaration replaces the first, and 0 clears it.
#guard after (settlers2 (declareSetup ++ [.move 0 (.declare "grain" 5), .move 0 (.declare "grain" 2)])) fun s =>
  s.declared 0 "grain" == 2
#guard after (settlers2 (declareSetup ++ [.move 0 (.declare "grain" 5), .move 0 (.declare "grain" 0)])) fun s =>
  s.declared 0 "grain" == 0
-- It stays through the round, and clears when the round ends.
#guard after (settlers2 (declareSetup ++ [.move 0 (.declare "grain" 5), endT 0])) fun s =>
  s.declared 0 "grain" == 5
#guard after (settlers2 (declareSetup ++ [.move 0 (.declare "grain" 5), endT 0, endT 1])) fun s =>
  s.declared 0 "grain" == 0
-- The claims hold on a game with declarations.
#guard traceFailures tinySettlers 2 42 (declareSetup ++ [.move 0 (.declare "grain" 5), .move 0 (.declare "timber" 1), endT 0, .forceEndTurn]) == []
-- At the action limit, a seat cannot declare.
#guard rejects (settlers2 (declareSetup ++ List.replicate maxActionsPerTurn (.move 0 (.declare "grain" 5)))) (.move 0 (.declare "grain" 5))
-- The treasury and the bank have no number, and neither does a missing seat.
#guard (Expr.declared .treasury (.lit "grain")).eval richGame {} == 0
#guard (Expr.declared .each (.lit "grain")).eval richGame {} == 0
#guard (Expr.declared .each (.lit "grain")).eval
  ({ richGame with declared := fun _ _ => 3 } : State tinySettlers) { each := some 1 } == 3
-- `legalMoves` does not list declarations, as it does not list offers.
#guard after (settlers2 declareSetup) fun s =>
  (legalMoves tinySettlers s 0).all fun | .declare .. => false | _ => true

/-! ### What a resource is worth -/

def worthState : State tinySettlers :=
  { testStart tinySettlers 2 42 with
    phase := .actions
    laws := [(0, { title := "w", clauses := [.setWorth "grain" 2] })]
    books := fun a r => match a, r with
      | .player 0, "grain" => 3 | .player 1, "timber" => 9 | .deposit 0 1, "grain" => 9 | _, _ => 0 }

#guard worthState.pointsOf 0 == 6
#guard worthState.tokenPointsOf 0 == 6
#guard worthState.builtPointsOf 0 == 0
#guard worthState.pointsOf 1 == 0
-- A later clause replaces an earlier one, and a repeal takes it away.
#guard ({ worthState with laws := worthState.laws ++ [(1, { title := "x", clauses := [.setWorth "grain" 5] })] } : State tinySettlers).pointsOf 0 == 15
#guard ({ worthState with laws := [] } : State tinySettlers).pointsOf 0 == 0
#guard lawAccepted [.setWorth "grain" 1]
#guard lawRejected [.setWorth "gold" 1]
#guard lawRejected [.setWorth "grain" 1, .setWorth "grain" 2]
-- The law's own vote looks for a winner: this law makes seat 0 win at once.
#guard after (settlers2 (settlersRound2 ++ [.propose 0 (.law { title := "w", clauses := [.setWorth "grain" 100] }), .vote 0 0 true, .vote 1 0 true]))
  fun s => s.phase == .ended && s.winner.isSome
-- The claims hold when the win comes from what a seat holds.
#guard traceFailures tinySettlers 2 42 (settlersRound2 ++ [.propose 0 (.law { title := "w", clauses := [.setWorth "grain" 100] }), .vote 0 0 true, .vote 1 0 true]) == []

/-! ### The total limit on planned payments -/

/-- `count` laws in force, each of one `forEach` with `transfers` transfers. -/
def simpleLaws (count transfers : Nat) : List (Nat × Law) :=
  (List.range count).map fun i => (i, wideLaw transfers)

def withLaws (seats : Nat) (laws : List (Nat × Law)) : State tinySettlers :=
  { testStart tinySettlers seats 42 with laws := laws, phase := .actions }

-- 42 simple laws fit at 6 seats. The 42nd passes with 41 in force.
#guard plannedTotal (simpleLaws 42 1) 6 == 252
#guard plannedTotal (simpleLaws 42 1) 6 ≤ maxPlannedTotal
#guard (lawProblems tinySettlers (withLaws 6 (simpleLaws 41 1)) (wideLaw 1)).isEmpty
-- The limit is exact. At 2 seats, a `forEach` with `k` transfers plans `2 * k` entries.
#guard (lawProblems tinySettlers (withLaws 2 (simpleLaws 1 64)) (wideLaw (maxPlannedTotal / 2 - 64))).length ≤ 1
#guard (lawProblems tinySettlers (withLaws 2 (simpleLaws 2 32 ++ [(9, wideLaw 32)])) (wideLaw 32)).isEmpty
#guard plannedTotal (simpleLaws 2 32 ++ [(9, wideLaw 32)] ++ [(0, wideLaw 32)]) 2 == maxPlannedTotal
#guard (lawProblems tinySettlers (withLaws 2 (simpleLaws 2 32 ++ [(9, wideLaw 32), (8, wideLaw 32)])) (wideLaw 1)) ==
  ["the laws in force could make too many payments at once"]
-- The cap on reads is exact too. A law that plans little can read a lot, inside a number.
def readingLaw (n : Nat) : Law :=
  badLaw [.onRoundEnd [.forEach .yes [.transfer .each .treasury (.lit "grain")
    ((List.range n).foldl (fun e _ => .add e (.lit 0)) (.lit 1))]]]
#guard (readingLaw 61).reads 6 == 751
#guard (lawProblems tinySettlers
    { sixSeats with laws := (List.range 9).map fun i => (i, readingLaw 61) } (readingLaw 61)).isEmpty
#guard (lawProblems tinySettlers
    { sixSeats with laws := (List.range 10).map fun i => (i, readingLaw 61) } (readingLaw 61)) ==
  ["the laws in force would read too many numbers at once"]
-- Nested `forEach`s with empty bodies plan nothing, but they count here, so they cannot stall a turn.
#guard (lawProblems tinySettlers sixSeats (badLaw [.onRoundEnd [nestedEach 0,
    (List.range 20).foldl (fun e _ => Effect.forEach .yes [e]) (Effect.forEach .yes [])]])).contains
  "the laws in force would read too many numbers at once"
-- A full budget still lets a law pass if it plans nothing, or if it repeals enough to fit.
#guard (lawProblems tinySettlers (withLaws 2 (simpleLaws 2 32 ++ [(9, wideLaw 32), (8, wideLaw 32)]))
  (badLaw [.setBankRate 2])).isEmpty
#guard (lawProblems tinySettlers (withLaws 2 (simpleLaws 2 32 ++ [(9, wideLaw 32), (8, wideLaw 32)]))
  (badLaw [.repeal 9, .onRoundEnd [nestedEach 1]])).isEmpty
-- The check runs again at the deciding vote: a law that no longer fits closes and is not enacted.
def fullBudgetVote : State tinySettlers :=
  { withLaws 2 (simpleLaws 2 32 ++ [(9, wideLaw 32), (8, wideLaw 32)]) with
    openProposals := [{ id := 20, by_ := 0, body := .law (wideLaw 1), votes := [(0, true)], signed := [] }]
    nextProposalId := 21 }

#guard
  match step tinySettlers fullBudgetVote (.vote 1 20 true) with
  | .ok s => s.laws.length == 4 && s.openProposals.isEmpty
  | .error _ => false

/-! ### Deals and proposals work both ways -/

/-- Two running deals, then seat 0 gives notice on the first. -/
def twoDealsExit : List Event := afterSetupForced ++ startEmptyDeals 3 0 2 ++ [.exit 0 0]

#guard after (settlers2 twoDealsExit) fun s => s.deals.map (·.lastRound) == [1, 3]
#guard traceFailures tinySettlers 2 42 twoDealsExit == []
-- A round's end closes only the deal that is due.
#guard after (settlers2 (twoDealsExit ++ [.forceEndTurn, .forceEndTurn])) fun s =>
  s.deals.map (·.id) == [1] && s.deals.map (·.lastRound) == [3]
#guard traceFailures tinySettlers 2 42 (twoDealsExit ++ [.forceEndTurn, .forceEndTurn]) == []
-- A turn end that is not the round's last closes no deal.
#guard after (settlers2 (twoDealsExit ++ [.forceEndTurn])) fun s => s.deals.length == 2
-- Other events leave a running deal and an open proposal alone.
#guard traceFailures tinySettlers 2 42 (dealStarted ++ [offerToSeat0]) == []
#guard traceFailures tinySettlers 2 42 (dealProposed ++ [offerToSeat0, .sign 0 0, .move 1 (.cancel 0)]) == []
-- A proposal by a seat that is not playing lasts only until that seat's turn starts.
#guard after (settlers2 (seat0HasGrain ++ [.propose 1 (.deal (emptyDeal 2))])) fun s =>
  s.openProposals.length == 1
#guard after (settlers2 (seat0HasGrain ++ [.propose 1 (.deal (emptyDeal 2)), endT 0])) fun s =>
  s.openProposals.isEmpty
#guard traceFailures tinySettlers 2 42 (seat0HasGrain ++ [.propose 1 (.deal (emptyDeal 2)), endT 0]) == []
-- A vote that does not decide is written down, and a yes after a no still decides.
#guard traceFailures tinySettlers 2 42 (lawOpen ++ [.vote 1 0 false]) == []

-- A seat not in the game cannot vote, even on an open law.
#guard rejects (settlers2 lawOpen) (.vote 2 0 true)
#guard rejects (settlers2 lawOpen) (.vote 2 0 false)

/-- Two offers are open. Taking back or accepting one must leave the other exactly as it was. -/
def twoOffers : List Event :=
  seat1OfferRound2 ++ [.move 1 (.offer none [("timber", 1)] [("grain", 1)])]

def secondOffer : Offer := ⟨1, 1, none, [("timber", 1)], [("grain", 1)]⟩

#guard after (settlers2 (twoOffers ++ [.move 1 (.cancel 0)])) fun s => s.offers == [secondOffer]
#guard after (settlers2 (twoOffers ++ [.move 0 (.accept 0)])) fun s => s.offers == [secondOffer]
#guard traceFailures tinySettlers 2 42 (twoOffers ++ [.move 1 (.cancel 0)]) == []
#guard traceFailures tinySettlers 2 42 (twoOffers ++ [.move 0 (.accept 0)]) == []
-- Offers end with the turn.
#guard traceFailures tinySettlers 2 42 (twoOffers ++ [endT 1]) == []

/-- A vote wins the game while a deal, an offer and another proposal are all open. -/
def winByVote : List Event :=
  settlersRound2 ++
  [ .propose 0 (.law bigSettlements), endT 0, offerToSeat0, .propose 0 (.deal (emptyDeal 2))
  , .propose 1 (.deal timberDeal), .sign 0 2, .sign 1 2, .vote 0 0 true, .vote 1 0 true ]

#guard after (settlers2 winByVote) fun s =>
  s.phase == .ended && s.winner.isSome && s.offers.isEmpty && s.openProposals.isEmpty &&
  s.deals.isEmpty && s.dealsStarted == 1
#guard traceFailures tinySettlers 2 42 winByVote == []

/-- The last turn of the game ends while a proposal is open. -/
def gameOverWithProposal : List Event :=
  List.replicate (maxTurns tinySettlers 2 - 1) .forceEndTurn ++
  [.propose 0 (.deal (emptyDeal 2)), .forceEndTurn]

#guard after (settlers2 gameOverWithProposal) fun s => s.phase == .ended && s.openProposals.isEmpty
#guard traceFailures tinySettlers 2 42 gameOverWithProposal == []

/-! ### Trades, setup and builds, on concrete games

Commandment VI states that an embargo stops a trade. These check the details of a `noTrade` term, that a bank trade or an
accepted offer moves nothing more than it says, and that setup moves no resources. -/

/-- Every seat holds 5 of everything, and so does the bank. -/
def fullBooks : Books := fun a _ =>
  match a with
  | .player _ | .bank => 5
  | _ => 0

/-- Tiny Space with 3 seats, on seat 0's action turn, with these offers and deals. -/
def tradeState (offers : List Offer) (deals : List ActiveDeal) : State tinySpace :=
  { testStart tinySpace 3 7 with phase := .actions, books := fullBooks, offers := offers, deals := deals }

def stepOk (s : State tinySpace) (e : Event) : Bool := (step tinySpace s e).toOption.isSome

/-- A running deal between seats 0 and 1, with one `noTrade` term. -/
def embargoOf (terms : List Term) : ActiveDeal :=
  { id := 0, lastRound := 5, startRound := 1, builtBefore := 0
    deal := { title := "Embargo", signers := [0, 1], rounds := 5, exitNotice := 0, deposits := [], terms := terms } }

def openOffer : Offer := ⟨0, 0, none, [("helium", 1)], [("alloy", 1)]⟩
def offerArgs : Move := .offer (some 1) [("helium", 1)] [("alloy", 1)]

-- With no deal, seats 1 and 2 can both accept, and seat 0 can offer to seat 1.
#guard stepOk (tradeState [openOffer] []) (.move 1 (.accept 0))
#guard stepOk (tradeState [openOffer] []) (.move 2 (.accept 0))
#guard stepOk (tradeState [] []) (.move 0 offerArgs)
-- A `noTrade` term stops both, in either order of the seats it names.
#guard !stepOk (tradeState [openOffer] [embargoOf [.noTrade 0 1]]) (.move 1 (.accept 0))
#guard !stepOk (tradeState [openOffer] [embargoOf [.noTrade 1 0]]) (.move 1 (.accept 0))
#guard !stepOk (tradeState [] [embargoOf [.noTrade 0 1]]) (.move 0 offerArgs)
#guard !stepOk (tradeState [] [embargoOf [.noTrade 1 0]]) (.move 0 offerArgs)
-- It stops only those two seats. Seat 2 can still accept, and seat 0 can still offer to seat 2.
#guard stepOk (tradeState [openOffer] [embargoOf [.noTrade 0 1]]) (.move 2 (.accept 0))
#guard stepOk (tradeState [] [embargoOf [.noTrade 0 1]]) (.move 0 (.offer (some 2) [("helium", 1)] [("alloy", 1)]))
-- An open offer to anyone can still be made, but the barred seat cannot take it.
#guard stepOk (tradeState [] [embargoOf [.noTrade 0 1]]) (.move 0 (.offer none [("helium", 1)] [("alloy", 1)]))
-- A deal with no such term stops nothing, and bank trades are never stopped.
#guard stepOk (tradeState [openOffer] [embargoOf []]) (.move 1 (.accept 0))
#guard stepOk (tradeState [] [embargoOf [.noTrade 0 1]]) (.move 0 (.bankTrade "helium" "alloy"))
-- The term ends with the deal. In the next round, the same two seats can trade again.
def embargoThenTrade : List Event :=
  seat1RichTurn ++ [.propose 1 (.deal noTradeDeal), .sign 0 0, .sign 1 0, endT 1, endT 0, offerToSeat0]

#guard after (settlers2 embargoThenTrade) fun s => s.deals.isEmpty && s.offers.length == 1
#guard traceFailures tinySettlers 2 42
  (seat1RichTurn ++ [offerToSeat0, .propose 1 (.deal noTradeDeal), .sign 0 0, .sign 1 0]) == []

-- Two signers promise not to trade with seat 2, who did not sign. Seat 3 signed nothing.
def graceEmbargo (lastRound : Nat) : ActiveDeal :=
  { embargoOf [.noTrade 0 2, .noTrade 1 2] with lastRound := lastRound }

/-- Tiny Space with 4 seats, on this seat's action turn, with these offers and that embargo. -/
def graceState (turn : Nat) (offers : List Offer) (deals : List ActiveDeal) : State tinySpace :=
  { testStart tinySpace 4 7 with
    phase := .actions, turnIndex := turn, books := fullBooks, offers := offers, deals := deals }

def offerBy (src : Seat) : Offer := ⟨0, src, none, [("helium", 1)], [("alloy", 1)]⟩
def offerMove (q : Seat) : Move := .offer (some q) [("helium", 1)] [("alloy", 1)]

-- Without the embargo, all these trades are fine.
#guard stepOk (graceState 0 [] []) (.move 0 (offerMove 2))
#guard stepOk (graceState 2 [] []) (.move 2 (offerMove 0))
#guard stepOk (graceState 0 [offerBy 0] []) (.move 2 (.accept 0))
#guard stepOk (graceState 0 [offerBy 2] []) (.move 0 (.accept 0))
-- With it, each signer and seat 2 cannot trade, in either direction.
#guard !stepOk (graceState 0 [] [graceEmbargo 5]) (.move 0 (offerMove 2))
#guard !stepOk (graceState 1 [] [graceEmbargo 5]) (.move 1 (offerMove 2))
#guard !stepOk (graceState 2 [] [graceEmbargo 5]) (.move 2 (offerMove 0))
#guard !stepOk (graceState 2 [] [graceEmbargo 5]) (.move 2 (offerMove 1))
#guard !stepOk (graceState 0 [offerBy 0] [graceEmbargo 5]) (.move 2 (.accept 0))
#guard !stepOk (graceState 0 [offerBy 1] [graceEmbargo 5]) (.move 2 (.accept 0))
#guard !stepOk (graceState 0 [offerBy 2] [graceEmbargo 5]) (.move 0 (.accept 0))
#guard !stepOk (graceState 0 [offerBy 2] [graceEmbargo 5]) (.move 1 (.accept 0))
-- Seat 2 can still trade with seat 3, who promised nothing, in either direction.
#guard stepOk (graceState 2 [] [graceEmbargo 5]) (.move 2 (offerMove 3))
#guard stepOk (graceState 3 [] [graceEmbargo 5]) (.move 3 (offerMove 2))
#guard stepOk (graceState 0 [offerBy 3] [graceEmbargo 5]) (.move 2 (.accept 0))
#guard stepOk (graceState 0 [offerBy 2] [graceEmbargo 5]) (.move 3 (.accept 0))
-- The two signers can still trade with each other and with seat 3.
#guard stepOk (graceState 0 [] [graceEmbargo 5]) (.move 0 (offerMove 1))
#guard stepOk (graceState 0 [] [graceEmbargo 5]) (.move 0 (offerMove 3))
-- When the term's deal ends at a round's end, the signer and seat 2 can trade again.
#guard match step tinySpace (graceState 3 [] [graceEmbargo 1]) .forceEndTurn with
  | .ok s => s.deals.isEmpty && !s.tradeBlocked 0 2 && (step tinySpace s (.move 0 (offerMove 2))).toOption.isSome
  | .error _ => false
-- A deal that runs on keeps the embargo after the round's end.
#guard match step tinySpace (graceState 3 [] [graceEmbargo 2]) .forceEndTurn with
  | .ok s => s.tradeBlocked 0 2 && (step tinySpace s (.move 0 (offerMove 2))).toOption.isNone
  | .error _ => false
-- The same, through real events: seats 0 and 1 sign a deal that names seat 2, and seat 2 is blocked.
def graceDeal : Deal :=
  { title := "Embargo on seat 2", signers := [0, 1], rounds := 1, exitNotice := 0, deposits := []
    terms := [.noTrade 0 2, .noTrade 1 2] }

#guard after (play tinySpace 3 7 (spaceSetup ++ [.propose 0 (.deal graceDeal), .sign 0 0, .sign 1 0]))
  fun s => s.deals.length == 1 && s.tradeBlocked 0 2 && s.tradeBlocked 2 1 && !s.tradeBlocked 0 1

-- Only the seat an offer is for can accept it, and never its maker.
def offerToSeat2 : Offer := { openOffer with to := some 2 }

#guard stepOk (tradeState [offerToSeat2] []) (.move 2 (.accept 0))
#guard !stepOk (tradeState [offerToSeat2] []) (.move 1 (.accept 0))
#guard !stepOk (tradeState [offerToSeat2] []) (.move 0 (.accept 0))
#guard !stepOk (tradeState [openOffer] []) (.move 0 (.accept 0))
-- Accepting moves exactly the offered bundles, and nobody else's holdings.
#guard
  match step tinySpace (tradeState [openOffer] []) (.move 2 (.accept 0)) with
  | .ok s =>
    s.journal == [⟨.player 0, .player 2, "helium", 1, .trade⟩, ⟨.player 2, .player 0, "alloy", 1, .trade⟩] &&
    s.balance (.player 0) "helium" == 4 && s.balance (.player 0) "alloy" == 6 &&
    s.balance (.player 2) "helium" == 6 && s.balance (.player 2) "alloy" == 4 &&
    s.balance (.player 1) "helium" == 5 && s.balance (.player 1) "alloy" == 5 && s.offers.isEmpty
  | .error _ => false
-- A seat that cannot pay its side cannot accept.
#guard !stepOk (tradeState [{ openOffer with get := [("alloy", 6)] }] []) (.move 1 (.accept 0))

-- A bank trade charges exactly the rate for 1, at the rate now in force, on the seat's own turn.
#guard tinySpace.bankRate == 3
#guard
  match step tinySpace (tradeState [] []) (.move 0 (.bankTrade "helium" "alloy")) with
  | .ok s =>
    s.journal == [⟨.player 0, .bank, "helium", 3, .trade⟩, ⟨.bank, .player 0, "alloy", 1, .trade⟩] &&
    s.balance (.player 0) "helium" == 2 && s.balance (.player 0) "alloy" == 6 &&
    s.balance .bank "helium" == 8 && s.balance .bank "alloy" == 4
  | .error _ => false
#guard
  match step tinySpace { tradeState [] [] with laws := [(0, badLaw [.setBankRate 2])] }
      (.move 0 (.bankTrade "helium" "alloy")) with
  | .ok s => s.journal == [⟨.player 0, .bank, "helium", 2, .trade⟩, ⟨.bank, .player 0, "alloy", 1, .trade⟩]
  | .error _ => false
#guard !stepOk (tradeState [] []) (.move 1 (.bankTrade "helium" "alloy"))
-- The seat must hold the rate, and the bank must hold the 1.
#guard !stepOk { tradeState [] [] with books := fun a _ => if a == .bank then 5 else 2 }
  (.move 0 (.bankTrade "helium" "alloy"))
#guard !stepOk { tradeState [] [] with books := fun a _ => if a == .bank then 0 else 5 }
  (.move 0 (.bankTrade "helium" "alloy"))

-- A seat that cannot pay cannot build, though the placement is legal and it is its turn.
def lanePieces : List Piece := [⟨0, "outpost", .spot 0⟩]

#guard stepOk { tradeState [] [] with pieces := lanePieces } (placeOn 0 "lane" 0 1)
#guard !stepOk { tradeState [] [] with pieces := lanePieces, books := fun a _ => if a == .bank then 5 else 0 }
  (placeOn 0 "lane" 0 1)
-- A build off-turn is rejected, though the seat can pay and the placement is legal.
#guard !stepOk { tradeState [] [] with pieces := [⟨1, "outpost", .spot 0⟩] } (placeOn 1 "lane" 0 1)
#guard stepOk { tradeState [] [] with pieces := [⟨1, "outpost", .spot 0⟩], turnIndex := 1 } (placeOn 1 "lane" 0 1)
-- The same in setup: the current seat can place, and no other seat can.
#guard accepts (settlers2 []) (placeAt 0 "settlement" 0)
#guard rejects (settlers2 []) (placeAt 1 "settlement" 0)
#guard rejects (settlers2 [placeAt 0 "settlement" 0, placeOn 0 "road" 0 1, endT 0]) (placeAt 0 "settlement" 2)
-- Setup moves no resources, for any placement of a whole setup.
#guard after (settlers2 settlersFullSetup.dropLast) fun s =>
  s.phase == .setup && s.pieces.length == 8 && s.journal.isEmpty && s.balance .bank "grain" == 24 && s.balance .bank "timber" == 24 &&
    s.balance .bank "brick" == 24
-- A setup piece must be the next one on the list, in order, and the list ends.
#guard rejects (settlers2 [placeAt 0 "settlement" 0, placeOn 0 "road" 0 1]) (placeOn 0 "road" 1 2)
#guard rejects (settlers2 [placeAt 0 "settlement" 0]) (placeAt 0 "settlement" 5)
-- A setup piece obeys the piece's limit.
def oneSettlement : GameDef :=
  { tinySettlers with
    pieces := tinySettlers.pieces.map fun d => if d.name == "settlement" then { d with limit := 1 } else d }

#guard rejects (play oneSettlement 2 42 [placeAt 0 "settlement" 0, endT 0, endT 1, endT 1]) (placeAt 0 "settlement" 5)
#guard accepts (play tinySettlers 2 42 [placeAt 0 "settlement" 0, endT 0, endT 1, endT 1]) (placeAt 0 "settlement" 5)

-- A real flag goes through the whole path: it can be built on a settlement, and not on a road.
#guard
  let s : State tinySpace :=
    { tradeState [] [] with
      laws := [(0, badLaw [.newPiece { flagOn (.attach "outpost") with cost := [] }])]
      pieces := [⟨0, "outpost", .spot 0⟩, ⟨0, "lane", .link (0, 1)⟩] }
  stepOk s (.move 0 (.place "flag" (.spot 0))) && !stepOk s (.move 0 (.place "flag" (.link (0, 1))))

-- VI(a) as now written gives the old clause, `roundsLeft d ≤ rounds`, so nothing was weakened.
example (G : GameDef) (s : State G) (d : ActiveDeal) (h1 : d.startRound ≤ s.round)
    (h2 : d.lastRound + 1 ≤ d.startRound + d.deal.rounds) : s.roundsLeft d ≤ d.deal.rounds := by
  unfold State.roundsLeft
  omega

/-! ## Founding laws -/

def founded2 (events : List Event) : Option (State tinyFounded) :=
  (replay tinyFounded 2 42 [25283273] events).toOption

/-- A law that repeals the founding law, which has id 0. -/
def repealFounding : Law := { title := "Dear cities", clauses := [.repeal 0] }

-- A new game starts with the founding law in force, and proposal ids start after it.
#guard after (founded2 []) fun s =>
  s.laws.map (·.1) == [0] && s.nextProposalId == 1 && s.costOf "city" == [("grain", 2)]
-- A game with no founding laws starts as before.
#guard after (settlers2 []) fun s =>
  s.laws.isEmpty && s.nextProposalId == 0 && s.costOf "city" == [("grain", 3)]
-- It takes effect from round 1.
#guard after (founded2 (settlersFullSetup ++ [endT 0])) fun s =>
  s.phase == .actions && s.round == 1 && s.costOf "city" == [("grain", 2)]

-- `lawProblems` sees it: a repeal of it is valid here, and is not valid in a game without it.
#guard after (founded2 []) fun s => (lawProblems tinyFounded s repealFounding).isEmpty
#guard after (settlers2 []) fun s => !(lawProblems tinySettlers s repealFounding).isEmpty

/-- Round 1, then seat 0 has grain, and it proposes the repeal in round 2. Both seats vote yes. -/
def repealEvents : List Event :=
  settlersFullSetup ++
  [ endT 0, endT 1
  , .propose 0 (.law repealFounding)
  , .vote 0 1 true, .vote 1 1 true ]

-- A majority can repeal it like any other law. The rules go back to the game's own.
#guard after (founded2 repealEvents) fun s =>
  s.laws.map (·.1) == [1] && s.costOf "city" == [("grain", 3)]

-- Replay works: the full game runs to the end, with the law in force, and replays the same.
#guard endedWithFoundingLaw (replay tinyFounded 2 42 [25283273] foundedGameEvents)
#guard after (founded2 foundedGameEvents) fun s => s.winner == some 1 && s.pointsOf 1 == 4

-- The claim checker passes on founded games, with the law kept and with it repealed.
#guard traceFailures tinyFounded 2 42 foundedGameEvents == []
#guard traceFailures tinyFounded 2 42 repealEvents == []

-- A later founding law can repeal an earlier one, in the same way as a later law.
def foundedThenRepealed : GameDef :=
  { tinyFounded with
    foundingLaws := tinyFounded.foundingLaws ++ [{ title := "Dear again", clauses := [.repeal 0] }] }

example : foundedThenRepealed.Valid := by decide +kernel
#guard foundedThenRepealed.startingLaws.map (·.1) == [1]

-- A founding law that repeals a law not in force is rejected, as it would be at a vote.
example : ¬ ({ tinySettlers with foundingLaws := [repealFounding] } : GameDef).Valid := by
  decide +kernel

-- A law over the payment limit only at some seat counts is caught at those counts.
#guard (tinySettlers.foundingOkFrom 2 [] 0 [tooManyPayments])
#guard !(tinySettlers.foundingOkFrom 6 [] 0 [tooManyPayments])

end Charter.EngineTests
