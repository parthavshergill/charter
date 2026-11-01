import Charter.Engine.Basic

/-!
# Deals

A deal is proposed, signed by every signer, and then started by the last signature. That
signature moves every deposit, all together, from each signer's own account. `dealProblems` is in
the spec, in `Charter/Words/DealChecks.lean`. It is checked when a deal is proposed and again when it starts.
-/

namespace Charter.Engine

variable {G : GameDef}

/-- Start a deal: move all deposits, give it the next id, and close its proposal. -/
def startDeal (s : State G) (proposalId : Nat) (d : Deal) : Except String (State G) :=
  if !s.canStartDeal then .error "no more deals can start"
  else if !(dealProblems s d).isEmpty then .error "this deal can no longer run"
  else do
    let s1 ← record s (depositEntries s.dealsStarted d)
    pure { s1 with
      deals := s.deals ++
        [{ id := s.dealsStarted, deal := d, lastRound := s.round + d.rounds - 1
           startRound := s.round, builtBefore := s.builtThisRound.length }]
      dealsStarted := s.dealsStarted + 1
      openProposals := s.openProposals.filter (·.id != proposalId) }

/-- A signer signs a proposed deal. The last signature starts the deal. -/
def signBody (s : State G) (seat proposalId : Nat) : Except String (State G) :=
  if s.phase != .actions then .error "deals can be signed only in the actions phase"
  else
    match s.openProposal? proposalId with
    | none => .error "there is no such proposal"
    | some p =>
      match p.body with
      | .law _ => .error "a law is voted on, not signed"
      | .deal d =>
        if !d.signers.contains seat then .error "this seat is not a signer"
        else if p.signed.contains seat then .error "this seat has already signed"
        else
          let signed := p.signed ++ [seat]
          if d.signers.all signed.contains then startDeal s proposalId d
          else .ok { s with
            openProposals := s.openProposals.map fun q =>
              if q.id == proposalId then { q with signed := signed } else q }

/-- A signer gives notice. The deal then ends no later than the notice period allows. -/
def exitBody (s : State G) (seat dealId : Nat) : Except String (State G) :=
  if s.phase != .actions then .error "notice can be given only in the actions phase"
  else if s.deals.any (fun d => d.id == dealId && d.deal.signers.contains seat) then
    .ok { s with
      deals := s.deals.map fun d =>
        if d.id == dealId then
          { d with lastRound := Nat.min d.lastRound (s.round + d.deal.exitNotice) }
        else d }
  else .error "this seat is not a signer of a running deal with that id"

end Charter.Engine
