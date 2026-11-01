import Charter.Words.State

/-!
# Which deals can run

A deal must cover the most it could ever pay. It binds only those who sign it. These checks run
when a deal is proposed and again when its last signature starts it.
-/

namespace Charter

/-- The total a deal puts in deposit for one signer and one resource. -/
def Deal.depositOf (d : Deal) (i : Seat) (r : Res) : Nat :=
  ((d.deposits.filter fun x => x.1 == i && x.2.1 == r).map (·.2.2)).sum

/-- The deposits cover every round's most expensive case, for every signer and resource. -/
def Deal.covered (d : Deal) (G : GameDef) : Bool :=
  d.signers.all fun i => G.resources.all fun r =>
    decide (d.rounds * d.owedPerRound i r.name ≤ d.depositOf i r.name)

/-- Why one term of a deal is not allowed. -/
def termProblems {G : GameDef} (s : State G) (d : Deal) : Term → List String
  | .everyRound _ => []
  | .onBuild x _ _ =>
      if s.turnOrder.contains x then [] else ["a build term names a seat not in this game"]
  | .noBuild x _ spots =>
      (if d.signers.contains x then [] else ["a no-build term must bind a signer"]) ++
      (if spots.all (fun v => decide (v < G.map.spotCount)) then []
       else ["a no-build term names a spot not on the map"])
  | .noTrade a b =>
      (if d.signers.contains a then [] else ["a no-trade term must bind a signer"]) ++
      (if s.turnOrder.contains b then [] else ["a no-trade term names a seat not in this game"]) ++
      (if a == b then ["a no-trade term must name two seats"] else [])

/-- Why one payment of a deal is not allowed. -/
def payProblems {G : GameDef} (s : State G) (d : Deal) (p : Pay) : List String :=
  (if d.signers.contains p.src then [] else ["only a signer can pay"]) ++
  (if G.isRes p.res then [] else ["a payment names a resource not in this game"]) ++
  (match p.dst with
   | .seat x => if s.turnOrder.contains x then [] else ["a payment goes to a seat not in this game"]
   | .treasury => [])

/-- Why a deal cannot run in this game. An empty list means it can. -/
def dealProblems {G : GameDef} (s : State G) (d : Deal) : List String :=
  (if 2 ≤ d.signers.length then [] else ["a deal needs at least two signers"]) ++
  (if decide d.signers.Nodup then [] else ["each signer can sign once"]) ++
  (if d.signers.all s.turnOrder.contains then [] else ["a signer is not in this game"]) ++
  (if 1 ≤ d.rounds then [] else ["a deal must run for at least one round"]) ++
  (if d.deposits.all (fun x => d.signers.contains x.1) then []
   else ["only a signer can put down a deposit"]) ++
  (if d.deposits.all (fun x => G.isRes x.2.1) then []
   else ["a deposit names a resource not in this game"]) ++
  d.allPays.flatMap (payProblems s d) ++
  d.terms.flatMap (termProblems s d) ++
  (if d.covered G then [] else ["the deposits do not cover what the deal could owe"])

/-- The entries that fund a new deal, each from the signer's own account. -/
def depositEntries (id : Nat) (d : Deal) : List Entry :=
  d.deposits.map fun x =>
    { src := .player x.1, dst := .deposit id x.1, res := x.2.1
      amount := x.2.2, reason := .setDeposit }

/-- A new deal can start: its id is free, and there is room for one more running deal. -/
def State.canStartDeal {G : GameDef} (s : State G) : Bool :=
  decide (s.dealsStarted < maxDealsPerGame) && decide (s.deals.length < maxActiveDeals)

end Charter
