import Charter.Words.GameDef

/-!
# Accounts and the journal

Every resource is always in exactly one account, and every change is written in the journal.
-/

namespace Charter

/-- A place that holds resources. -/
inductive Account where
  | bank
  | treasury
  | player (seat : Seat)
  /-- Money a signer has set aside for a deal. -/
  | deposit (deal : Nat) (seat : Seat)
  deriving Repr, DecidableEq

/-- Why resources moved. -/
inductive Reason where
  | cost | trade | harvest | lawFee | lawEffect | setDeposit | dealPayment | refund
  deriving Repr, DecidableEq

/-- One written movement of resources. -/
structure Entry where
  src : Account
  dst : Account
  res : Res
  amount : Nat
  reason : Reason
  deriving Repr, DecidableEq

/-- How much of each resource each account holds. -/
abbrev Books := Account → Res → Nat

/-- Post an entry in full, or fail. It never moves less than the entry says. -/
def Books.post (b : Books) (e : Entry) : Option Books :=
  if e.amount ≤ b e.src e.res ∧ e.src ≠ e.dst then
    some fun a r =>
      if r = e.res then
        if a = e.src then b a r - e.amount
        else if a = e.dst then b a r + e.amount
        else b a r
      else b a r
  else none

/-- Post entries in order. One failure fails the whole list. -/
def Books.postAll (b : Books) : List Entry → Option Books
  | [] => some b
  | e :: es => (b.post e).bind fun b' => Books.postAll b' es

/-- At the start, the bank holds all resources. -/
def genesisBooks (G : GameDef) : Books := fun a r =>
  match a with
  | .bank => G.stockOf r
  | _ => 0

end Charter
