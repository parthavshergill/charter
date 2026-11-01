import Charter.Words.Game

/-!
# What a deal is

A deal binds only those who sign it, so unlike a law it can name seats.
-/

namespace Charter

/-- Who a deal can pay. -/
inductive Payee where
  | seat (s : Seat)
  | treasury
  deriving Repr, DecidableEq

/-- One payment a deal promises. -/
structure Pay where
  src : Seat
  dst : Payee
  res : Res
  amount : Nat
  deriving Repr, DecidableEq

/-- One promise in a deal. -/
inductive Term where
  | everyRound (pays : List Pay)
  /-- Fires at most once per round, when seat `s` built kind `k` that round, after the deal
  started. A build made before the deal started does not count. -/
  | onBuild (s : Seat) (k : PieceKind) (pays : List Pay)
  | noBuild (s : Seat) (k : PieceKind) (spots : List Nat)
  /-- Signer `a` will not trade with seat `b`, in either direction. `b` need not sign. -/
  | noTrade (a b : Seat)
  deriving Repr, DecidableEq

/-- A deal: who signs, how long it runs, the notice to leave, the deposits and the promises. -/
structure Deal where
  title : String
  signers : List Seat
  rounds : Nat
  exitNotice : Nat
  deposits : List (Seat × Res × Nat)
  terms : List Term
  deriving Repr, DecidableEq

/-- The payments this term can make. A promise not to build or trade pays nothing. -/
def Term.pays : Term → List Pay
  | .everyRound ps => ps
  | .onBuild _ _ ps => ps
  | _ => []

/-- Every payment this deal can make. -/
def Deal.allPays (d : Deal) : List Pay := d.terms.flatMap Term.pays

/-- The most signer `i` can owe in `r` in one round. -/
def Deal.owedPerRound (d : Deal) (i : Seat) (r : Res) : Nat :=
  ((d.allPays.filter fun p => p.src == i && p.res == r).map (·.amount)).sum

/-- A running deal. It pays at the end of each round up to and including `lastRound`. -/
structure ActiveDeal where
  id : Nat
  deal : Deal
  lastRound : Nat
  /-- The round the deal started. -/
  startRound : Nat
  /-- How many builds were already in `builtThisRound` when the deal started. -/
  builtBefore : Nat
  deriving Repr, DecidableEq

end Charter
