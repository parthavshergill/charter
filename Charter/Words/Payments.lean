import Charter.Words.LawEffects

/-!
# What deals owe, and what trades and fees move

At a round's end, deals pay first. Then laws react. Then the deals that close refund what is left.
-/

namespace Charter

namespace State
variable {G : GameDef}

/-- Rounds left to pay, counting the current one. -/
def roundsLeft (s : State G) (d : ActiveDeal) : Nat := d.lastRound + 1 - s.round

/-- The most signer `i` can still owe in `r`, whatever players do. -/
def worstCase (s : State G) (d : ActiveDeal) (i : Seat) (r : Res) : Nat :=
  s.roundsLeft d * d.deal.owedPerRound i r

/-- The account a payment goes to. -/
def _root_.Charter.Payee.account : Payee → Account
  | .seat x => .player x
  | .treasury => .treasury

/-- The entries for these payments, each from the payer's deposit in deal `id`. -/
def payEntries (id : Nat) (pays : List Pay) : List Entry :=
  pays.map fun p =>
    { src := .deposit id p.src, dst := p.dst.account
      res := p.res, amount := p.amount, reason := .dealPayment }

/-- The builds of this round that a deal can see: only those made after it started. -/
def buildsSeenBy (s : State G) (d : ActiveDeal) : List (Seat × PieceKind) :=
  if s.round == d.startRound then s.builtThisRound.drop d.builtBefore else s.builtThisRound

/-- The payments deals make at this round's end, in order. -/
def duePayments (s : State G) : List Entry :=
  s.deals.flatMap fun d =>
    d.deal.terms.flatMap fun
      | .everyRound ps => payEntries d.id ps
      | .onBuild x k ps => if (s.buildsSeenBy d).contains (x, k) then payEntries d.id ps else []
      | _ => []

/-- Everything unspent in a deal's deposits goes back to its signers. Empty refunds are left out. -/
def refundEntries (s : State G) (d : ActiveDeal) : List Entry :=
  d.deal.signers.flatMap fun i =>
    G.resources.filterMap fun r =>
      let held := s.balance (.deposit d.id i) r.name
      if held = 0 then none
      else some { src := .deposit d.id i, dst := .player i, res := r.name
                  amount := held, reason := .refund }

/-- The deals that close at this round's end. In the last round, all of them close. -/
def closingDeals (s : State G) : List ActiveDeal :=
  if G.rounds ≤ s.round then s.deals
  else s.deals.filter fun d => decide (d.lastRound ≤ s.round)

/-- What the laws do at this round's end, after the deals have paid. -/
def roundEndLawEntries (s : State G) : List Entry :=
  lawEntries (s.afterPosting s.duePayments) .roundEnd

/-- A round's end, in order: deals pay, then laws react, then the deals that close refund. -/
def roundEndEntries (s : State G) : List Entry :=
  let paid := s.duePayments ++ s.roundEndLawEntries
  paid ++ s.closingDeals.flatMap (s.afterPosting paid).refundEntries

/-- The entries of a turn change that come before the roll. Only a round's end has any. -/
def entriesBeforeRoll (s : State G) : List Entry :=
  if s.isLastTurn then s.roundEndEntries else []

end State

/-! ## Trades and fees -/

/-- Entries that move a whole bundle from one account to another, in the bundle's order. -/
def bundleEntries (src dst : Account) (b : Bundle) (reason : Reason) : List Entry :=
  b.map fun x => { src := src, dst := dst, res := x.1, amount := x.2, reason := reason }

/-- What a law's proposer pays. -/
def lawFeeEntries (G : GameDef) (p : Seat) : List Entry :=
  bundleEntries (.player p) .bank G.lawFee .lawFee

/-- Seat `p` accepts offer `o`: the offer's maker pays `give`, and then `p` pays `get`. -/
def offerEntries (o : Offer) (p : Seat) : List Entry :=
  bundleEntries (.player o.src) (.player p) o.give .trade ++
  bundleEntries (.player p) (.player o.src) o.get .trade

namespace State
variable {G : GameDef}

/-- A trade with the bank: `bankRate` of one resource for 1 of another. -/
def bankTradeEntries (s : State G) (p : Seat) (give get : Res) : List Entry :=
  [ { src := .player p, dst := .bank, res := give, amount := s.rules.bankRate, reason := .trade }
  , { src := .bank, dst := .player p, res := get, amount := 1, reason := .trade } ]

/-- A running deal forbids these two seats to trade: one of them signed it and promised not to trade
with the other. The other seat need not have signed, and it can still trade with anyone else. -/
def tradeBlocked (s : State G) (a b : Seat) : Bool :=
  s.deals.any fun d =>
    d.deal.terms.any fun
      | .noTrade x y =>
          d.deal.signers.contains x && ((x == a && y == b) || (x == b && y == a))
      | _ => false

end State

end Charter
