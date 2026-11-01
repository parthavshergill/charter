import Charter.Words.State

/-!
# Renaming players

Commandment II says the engine treats renamed seats alike. These definitions say what renaming means.
-/

namespace Charter

/-- A way to rename every seat, with no two seats given the same name. -/
structure Renaming where
  to : Seat → Seat
  back : Seat → Seat
  back_to : ∀ x, back (to x) = x
  to_back : ∀ x, to (back x) = x

namespace Renaming
variable (σ : Renaming)

/-- The same account, with its seat renamed. -/
def account : Account → Account
  | .player i => .player (σ.to i)
  | .deposit k i => .deposit k (σ.to i)
  | a => a

/-- The same entry, with its accounts renamed. -/
def entry (e : Entry) : Entry := { e with src := σ.account e.src, dst := σ.account e.dst }

/-- The same payee, renamed. -/
def payee : Payee → Payee
  | .seat x => .seat (σ.to x)
  | .treasury => .treasury

/-- The same payment, renamed. -/
def pay (p : Pay) : Pay := { p with src := σ.to p.src, dst := σ.payee p.dst }

/-- The same term, renamed. -/
def term : Term → Term
  | .everyRound ps => .everyRound (ps.map σ.pay)
  | .onBuild s k ps => .onBuild (σ.to s) k (ps.map σ.pay)
  | .noBuild s k spots => .noBuild (σ.to s) k spots
  | .noTrade a b => .noTrade (σ.to a) (σ.to b)

/-- The same deal, renamed. -/
def deal (d : Deal) : Deal :=
  { d with
    signers := d.signers.map σ.to
    deposits := d.deposits.map fun x => (σ.to x.1, x.2)
    terms := d.terms.map σ.term }

/-- Laws have no seats in them, so renaming leaves a law unchanged. -/
def proposal : Proposal → Proposal
  | .law l => .law l
  | .deal d => .deal (σ.deal d)

/-- The same open proposal, renamed. -/
def openProposal (p : OpenProposal) : OpenProposal :=
  { p with
    by_ := σ.to p.by_
    body := σ.proposal p.body
    votes := p.votes.map fun x => (σ.to x.1, x.2)
    signed := p.signed.map σ.to }

/-- The same running deal, renamed. -/
def activeDeal (d : ActiveDeal) : ActiveDeal := { d with deal := σ.deal d.deal }

/-- The same offer, renamed. -/
def offer (o : Offer) : Offer := { o with src := σ.to o.src, to := o.to.map σ.to }

/-- The same piece, with its owner renamed. -/
def piece (x : Piece) : Piece := { x with owner := σ.to x.owner }

/-- The same move, renamed. Only an offer names a seat. -/
def move : Move → Move
  | .offer to give get => .offer (to.map σ.to) give get
  | m => m

/-- The same event, renamed. -/
def event : Event → Event
  | .move p m => .move (σ.to p) (σ.move m)
  | .propose p x => .propose (σ.to p) (σ.proposal x)
  | .vote p i y => .vote (σ.to p) i y
  | .sign p i => .sign (σ.to p) i
  | .exit p i => .exit (σ.to p) i
  | .forceEndTurn => .forceEndTurn

/-- The same game with every seat renamed, including who goes first. -/
def state {G : GameDef} (s : State G) : State G :=
  { s with
    turnOrder := s.turnOrder.map σ.to
    books := fun a r => s.books (Renaming.account ⟨σ.back, σ.to, σ.to_back, σ.back_to⟩ a) r
    journal := s.journal.map σ.entry
    pieces := s.pieces.map σ.piece
    openProposals := s.openProposals.map σ.openProposal
    deals := s.deals.map σ.activeDeal
    offers := s.offers.map σ.offer
    builtThisRound := s.builtThisRound.map fun x => (σ.to x.1, x.2)
    actionsThisTurn := fun p => s.actionsThisTurn (σ.back p)
    winner := s.winner.map σ.to }

end Renaming

end Charter
