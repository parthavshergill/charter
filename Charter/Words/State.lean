import Charter.Words.Books
import Charter.Words.RuleLanguage
import Charter.Words.Deal

/-!
# The game state, events and the rules in force

There is no separate rule book in the state. The rules are always computed from the game
definition and the laws in force.
-/

namespace Charter

/-! ## The game state -/

/-- The three parts of a game. -/
inductive Phase where
  | setup | actions | ended
  deriving Repr, DecidableEq

/-- A place on the map. -/
inductive Loc where
  | spot (v : Nat)
  | link (l : Nat × Nat)
  deriving Repr, DecidableEq

/-- A piece on the board. -/
structure Piece where
  owner : Seat
  kind : PieceKind
  loc : Loc
  deriving Repr, DecidableEq

/-- An open offer: `src` gives `give` and gets `get`. If `to` is `none`, any seat can accept. -/
structure Offer where
  id : Nat
  src : Seat
  to : Option Seat
  give : Bundle
  get : Bundle
  deriving Repr, DecidableEq

/-- What a seat can put forward: a law to vote on, or a deal to sign. -/
inductive Proposal where
  | law (l : Law)
  | deal (d : Deal)
  deriving Repr

/-- A proposal that has not closed yet. -/
structure OpenProposal where
  id : Nat
  by_ : Seat
  body : Proposal
  /-- A vote is final, so each seat appears at most once. -/
  votes : List (Seat × Bool)
  signed : List Seat
  deriving Repr

/-- Everything about a game in play. -/
structure State (G : GameDef) where
  /-- Who plays, in turn order. This is stored, so that going first is a fact about the
  game and not about seat numbers. -/
  turnOrder : List Seat
  phase : Phase
  round : Nat
  turnIndex : Nat
  /-- Every turn so far, in setup and in play. -/
  turnsTaken : Nat
  /-- Rolls made so far. The next roll is number `rollsMade`. -/
  rollsMade : Nat
  lastRoll : Option Nat
  seed : UInt64
  seedCommitment : String
  books : Books
  journal : List Entry
  pieces : List Piece
  /-- Laws in force, oldest first, each with its id. -/
  laws : List (Nat × Law)
  openProposals : List OpenProposal
  nextProposalId : Nat
  deals : List ActiveDeal
  dealsStarted : Nat
  offers : List Offer
  nextOfferId : Nat
  builtThisRound : List (Seat × PieceKind)
  actionsThisTurn : Seat → Nat
  /-- Each seat's public number for each resource. It clears when the round ends. -/
  declared : Seat → Res → Nat
  /-- Every event accepted so far. -/
  eventsApplied : Nat
  winner : Option Seat

/-! ## Events -/

/-- What a seat can do on the board. -/
inductive Move where
  | place (kind : PieceKind) (loc : Loc)
  | bankTrade (give get : Res)
  | offer (to : Option Seat) (give get : Bundle)
  | accept (offerId : Nat)
  | cancel (offerId : Nat)
  /-- On your own turn, set your public number for this resource. It moves nothing. -/
  | declare (r : Res) (n : Nat)
  | endTurn
  deriving Repr, DecidableEq

/-- The only ways a game can change. -/
inductive Event where
  | move (seat : Seat) (m : Move)
  | propose (seat : Seat) (p : Proposal)
  | vote (seat : Seat) (proposalId : Nat) (yes : Bool)
  | sign (seat : Seat) (proposalId : Nat)
  | exit (seat : Seat) (dealId : Nat)
  /-- Sent by the server's turn timer. Ends the current turn for a player who is away. -/
  | forceEndTurn
  deriving Repr

namespace State
variable {G : GameDef}

/-- How much of `r` this account holds. -/
def balance (s : State G) (a : Account) (r : Res) : Nat := s.books a r

/-- Every account a game can have. -/
def accounts (s : State G) : List Account :=
  [.bank, .treasury] ++ s.turnOrder.map .player ++
    (List.range maxDealsPerGame).flatMap fun k => s.turnOrder.map (.deposit k)

/-- The amount of `r` across all accounts. -/
def total (s : State G) (r : Res) : Nat :=
  (s.accounts.map fun a => s.balance a r).sum

/-- The seat whose turn it is. -/
def currentSeat (s : State G) : Option Seat := s.turnOrder[s.turnIndex]?

/-- It is `p`'s turn. -/
def isTurnOf (s : State G) (p : Seat) : Bool := s.currentSeat == some p

/-- This turn is the last of the round. -/
def isLastTurn (s : State G) : Bool :=
  s.phase == .actions && s.turnIndex + 1 == s.turnOrder.length

/-- `p` holds at least this bundle. -/
def affords (s : State G) (p : Seat) (b : Bundle) : Bool :=
  b.all fun x => decide (x.2 ≤ s.balance (.player p) x.1)

end State

/-! ## The rules in force

There is no separate rule book in the state. The rules are always computed from the game
definition and the laws in force.
-/

/-- The rules that laws can change. -/
structure Rules where
  pieces : List PieceDef
  bankRate : Nat
  /-- What a unit of a resource is worth in points. A resource not listed is worth 0. -/
  worth : List (Res × Nat)
  deriving Repr

/-- The piece of this kind, if the rules have one. -/
def Rules.piece? (R : Rules) (k : PieceKind) : Option PieceDef := R.pieces.find? (·.name == k)

/-- How one clause changes the rules. -/
def Clause.applyTo : Clause → Rules → Rules
  | .setCost k b, R =>
      { R with pieces := R.pieces.map fun p => if p.name == k then { p with cost := b } else p }
  | .setPoints k n, R =>
      { R with pieces := R.pieces.map fun p => if p.name == k then { p with points := n } else p }
  | .setBankRate n, R => { R with bankRate := n }
  | .setWorth r n, R => { R with worth := R.worth.filter (·.1 != r) ++ [(r, n)] }
  | .newPiece p, R => { R with pieces := R.pieces ++ [p] }
  | _, R => R

/-- How a whole law changes the rules: each clause in order. -/
def Law.applyTo (L : Law) (R : Rules) : Rules := L.clauses.foldl (fun R c => c.applyTo R) R

/-- The rules: the game's starting rules, then each law in force, oldest first. -/
def rulesFrom (G : GameDef) (laws : List (Nat × Law)) : Rules :=
  laws.foldl (fun R x => x.2.applyTo R) { pieces := G.pieces, bankRate := G.bankRate, worth := [] }

/-- The ids of the laws this law repeals. -/
def Law.repeals (L : Law) : List Nat :=
  L.clauses.filterMap fun
    | .repeal n => some n
    | _ => none

/-- The laws in force after law `id` passes: repeals take effect, and it joins the list, unless it is a law
of only `now` clauses. -/
def enact (laws : List (Nat × Law)) (id : Nat) (L : Law) : List (Nat × Law) :=
  (laws.filter fun x => !L.repeals.contains x.1) ++ if L.isDecree then [] else [(id, L)]

/-- The laws in force after these laws pass in order, with ids counting up from `id`. -/
def enactAll : List (Nat × Law) → Nat → List Law → List (Nat × Law)
  | laws, _, [] => laws
  | laws, id, L :: Ls => enactAll (enact laws id L) (id + 1) Ls

/-- The laws in force when a game starts: the founding laws, with ids 0, 1, 2 and so on. -/
def GameDef.startingLaws (G : GameDef) : List (Nat × Law) := enactAll [] 0 G.foundingLaws

namespace State
variable {G : GameDef}

/-- The rules in force now. -/
def rules (s : State G) : Rules := rulesFrom G s.laws

/-- What this piece costs now. -/
def costOf (s : State G) (k : PieceKind) : Bundle :=
  ((s.rules.piece? k).map (·.cost)).getD []

/-- How many pieces of this kind `p` has on the board. -/
def countOf (s : State G) (p : Seat) (k : PieceKind) : Nat :=
  (s.pieces.filter fun x => x.owner == p && x.kind == k).length

/-- The points from what a seat has built. A piece whose law was repealed is worth 0. -/
def builtPointsOf (s : State G) (p : Seat) : Nat :=
  ((s.pieces.filter (·.owner == p)).map fun x =>
    ((s.rules.piece? x.kind).map (·.points)).getD 0).sum

/-- The points from what a seat holds that a law says is worth something. Only a seat's own account
counts, so a deposit does not. -/
def tokenPointsOf (s : State G) (p : Seat) : Nat :=
  (s.rules.worth.map fun x => x.2 * s.balance (.player p) x.1).sum

/-- A seat's points: what it has built, and what it holds that counts. -/
def pointsOf (s : State G) (p : Seat) : Nat := s.builtPointsOf p + s.tokenPointsOf p

/-- A law in force ends the game. -/
def lawEnds (s : State G) : Bool := s.laws.any fun x => x.2.clauses.any Clause.isEndGame

/-- `s` with entries posted to its books. Used to say what a later entry could see. -/
def afterPosting (s : State G) (es : List Entry) : State G :=
  { s with books := (s.books.postAll es).getD s.books }

end State

/-! ## Votes -/

/-- How many yes votes this proposal has. -/
def OpenProposal.yesCount (p : OpenProposal) : Nat := (p.votes.filter (·.2)).length

/-- More than half of all seats said yes. -/
def OpenProposal.hasMajority (p : OpenProposal) (seats : Nat) : Prop := p.yesCount * 2 > seats

/-- This proposal with one more vote at the end. -/
def OpenProposal.withVote (p : OpenProposal) (seat : Seat) (yes : Bool) : OpenProposal :=
  { p with votes := p.votes ++ [(seat, yes)] }

/-- The open proposal with this id, if there is one. -/
def State.openProposal? {G : GameDef} (s : State G) (id : Nat) : Option OpenProposal :=
  s.openProposals.find? (·.id == id)

end Charter
