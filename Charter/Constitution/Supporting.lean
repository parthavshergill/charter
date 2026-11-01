import Charter.Constitution

/-!
# Five supporting promises

These back up the ten commandments. An engine that rejects every event would keep most of the
promises about what cannot happen. So some of these show that events are really accepted. The others
close gaps that the commandments leave open.
-/

namespace Charter

/-- **A winner earned it.** Nobody has more points than the winner, and the winner reached the target,
the rounds really ran out, or a majority ended the game. A game ends only by one of those three routes, so
an ended game always has a winner. Points come from what a seat has built and from what it holds that a law says counts. After a move or a
vote, a seat at the target has ended the game. A turn change does not look: a seat that reaches the target
from a harvest, or by a law that gives it a piece, wins at the next move or vote by anyone.

Why it matters: the commandments say how a game runs, and this says that its result means something. -/
theorem the_winner_earned_it (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s) :
    (∀ w, s.winner = some w →
      s.phase = .ended ∧ w ∈ s.turnOrder ∧
      (∀ p ∈ s.turnOrder, s.pointsOf p ≤ s.pointsOf w) ∧
      (G.targetPoints ≤ s.pointsOf w ∨ s.turnsTaken = maxTurns G s.turnOrder.length ∨
        MajorityEndedTheGame s)) ∧
    (s.phase = .ended → s.winner.isSome = true) ∧
    (∀ e s', Engine.step G s e = .ok s' → LooksForWinner e →
      (∃ p ∈ s'.turnOrder, G.targetPoints ≤ s'.pointsOf p) → s'.phase = .ended) :=
  Proofs.the_winner_earned_it G hG s (hs.inv hG)

/-- **The limits hold.** The fixed limits hold in every game: laws in force and their size, open
proposals per seat, and running deals. Each law, and all the laws together, ask for a limited number
of payments on any one trigger. All the laws together read a limited number of numbers and tests.

Why it matters: no law can stall the game by making a turn too slow to run. -/
theorem limits_hold (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s) :
    s.laws.length ≤ maxLawsInForce ∧
    (∀ x ∈ s.laws, x.2.size ≤ maxLawSize) ∧
    (∀ seat, (s.openProposals.filter (·.by_ == seat)).length ≤ maxOpenPerSeat) ∧
    s.deals.length ≤ maxActiveDeals ∧
    (∀ x ∈ s.laws, x.2.plannedEntries s.turnOrder.length ≤ maxPlannedEntries) ∧
    plannedTotal s.laws s.turnOrder.length ≤ maxPlannedTotal ∧
    readsTotal s.laws s.turnOrder.length ≤ maxReadsTotal :=
  Proofs.limits_hold G hG s (hs.inv hG)

/-- **What most other events do.** With commandments VII and X, this and V's rule for accepted offers
cover every event except a bank trade and a setup placement. Commandment V limits what those take from
a seat. Only the tests check their entries in full.

An exit and a proposal make no entries. An offer or a cancelled offer makes none either, unless a seat
is at the target and the game ends, which makes only refunds. A signature makes no entries, unless it is the last, which makes exactly the deal's deposits.
A vote makes exactly what `VoteWritesExactly` says. Accepting needs an offer
that exists. A seat can end a turn only when it is the current seat. Only placing a piece, a turn change and passing a law change the
pieces, and commandment V says how. Only ending a turn moves the turn or the dice.

A declaration changes one number and adds to the sender's action count and the count of events. It
changes nothing else, unless a seat is at the target and the game ends. `DeclarationsKept` says how declared numbers can change in any step.

Why it matters: it rules out hidden side effects in the events the commandments do not list. -/
theorem every_other_event_is_exact (G : GameDef) (hG : G.Valid) (s s' : State G) (e : Event)
    (hs : Reachable G s) (h : Engine.step G s e = .ok s') :
    (∀ seat dealId, e = .exit seat dealId → newEntries s s' = []) ∧
    (∀ p to give get, e = .move p (.offer to give get) → NoEntriesUnlessEnded s s') ∧
    (∀ p id, e = .move p (.cancel id) → NoEntriesUnlessEnded s s') ∧
    (∀ seat d, e = .propose seat (.deal d) → newEntries s s' = []) ∧
    (∀ seat L, e = .propose seat (.law L) → newEntries s s' = []) ∧
    (∀ seat id, e = .sign seat id → ∃ p d,
      s.openProposal? id = some p ∧ p.body = .deal d ∧
      ((∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
        newEntries s s' = depositEntries s.dealsStarted d) ∧
      ((¬ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) → newEntries s s' = [])) ∧
    (∀ seat id yes, e = .vote seat id yes → VoteWritesExactly s s' e) ∧
    (∀ p id, e = .move p (.accept id) → ∃ o, s.offers.find? (·.id == id) = some o) ∧
    (∀ p, e = .move p .endTurn → EndsTurn s e) ∧
    (¬ EndsTurn s e → (∀ p k loc, e ≠ .move p (.place k loc)) → (∀ L, ¬ LawPasses s e L) →
      s'.pieces = s.pieces) ∧
    (¬ EndsTurn s e →
      s'.turnsTaken = s.turnsTaken ∧ s'.turnIndex = s.turnIndex ∧ s'.round = s.round ∧
      s'.rollsMade = s.rollsMade) ∧
    (∀ p r n, e = .move p (.declare r n) → NoEntriesUnlessEnded s s' ∧ s'.phase ≠ .ended →
      s' = { s with
        declared := fun q x => if q = p ∧ x = r then n else s.declared q x
        actionsThisTurn := fun q => if q = p then s.actionsThisTurn q + 1 else s.actionsThisTurn q
        eventsApplied := s.eventsApplied + 1 }) ∧
    DeclarationsKept s s' e :=
  Proofs.every_other_event_is_exact G hG s s' e (hs.inv hG) h

-- This proof needs neither `hG` nor `hs`. The statement keeps them, so it matches the others.
set_option linter.unusedVariables false in
/-- **Proposals cannot be switched off.** In the actions phase, a seat in the game that is under its
action limit and its limit of open proposals can propose a law exactly when the law passes
`lawProblems`. Proposing costs nothing, so no seat can be too poor to ask for a repeal. It can propose a
deal exactly when the deal passes
`dealProblems` and the seat is one of its signers. An accepted proposal goes on the end of the open
list.

Why it matters: without this, an engine that refused every proposal would keep commandment III. -/
theorem proposals_are_accepted (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s)
    (seat : Seat) (hPhase : s.phase = .actions) (hSeat : seat ∈ s.turnOrder)
    (hActs : s.actionsThisTurn seat < maxActionsPerTurn)
    (hOpen : (s.openProposals.filter (·.by_ == seat)).length < maxOpenPerSeat) :
    (∀ L, (∃ s', Engine.step G s (.propose seat (.law L)) = .ok s') ↔
      lawProblems G s L = []) ∧
    (∀ d, (∃ s', Engine.step G s (.propose seat (.deal d)) = .ok s') ↔
      dealProblems s d = [] ∧ seat ∈ d.signers) ∧
    (∀ body s', Engine.step G s (.propose seat body) = .ok s' →
      s'.openProposals = s.openProposals ++
        [{ id := s.nextProposalId, by_ := seat, body := body, votes := [], signed := [] }]) :=
  Proofs.proposals_are_accepted s seat hPhase hSeat hActs hOpen

-- This proof needs neither `hG` nor `hs`. The statement keeps them, so it matches the others.
set_option linter.unusedVariables false in
/-- **Deals cannot be switched off.** In the actions phase, a signer in the game, under its action
limit, who has not signed can sign. A signature that is not the last is written down and moves
nothing. The last signature starts exactly that deal, if the deal passes `dealProblems`, every signer
can pay its deposit, and the limits on deals allow it. The deal runs until its agreed last round.

Why it matters: without this, an engine that never started a deal would keep commandments IV and VI. -/
theorem deals_can_start (G : GameDef) (hG : G.Valid) (s : State G) (hs : Reachable G s)
    (seat id : Nat) (p : OpenProposal) (d : Deal) (hPhase : s.phase = .actions)
    (hSeat : seat ∈ s.turnOrder) (hActs : s.actionsThisTurn seat < maxActionsPerTurn)
    (hOpen : s.openProposal? id = some p) (hBody : p.body = .deal d)
    (hSigner : seat ∈ d.signers) (hNew : seat ∉ p.signed) :
    ((¬ ∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
      ∃ s' q, Engine.step G s (.sign seat id) = .ok s' ∧
        s'.deals = s.deals ∧ newEntries s s' = [] ∧
        s'.openProposal? id = some q ∧ q.body = p.body ∧ q.signed = p.signed ++ [seat]) ∧
    ((∀ j ∈ d.signers, j ∈ p.signed ∨ j = seat) →
      dealProblems s d = [] →
      (∀ i r, d.depositOf i r ≤ s.balance (.player i) r) →
      s.canStartDeal = true →
      ∃ s', Engine.step G s (.sign seat id) = .ok s' ∧
        s'.deals = s.deals ++
          [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
             startRound := s.round, builtBefore := s.builtThisRound.length }] ∧
        s'.dealsStarted = s.dealsStarted + 1 ∧
        newEntries s s' = depositEntries s.dealsStarted d ∧
        s'.openProposal? id = none) :=
  Proofs.deals_can_start s seat id p d hPhase hSeat hActs hOpen hBody hSigner hNew

end Charter
