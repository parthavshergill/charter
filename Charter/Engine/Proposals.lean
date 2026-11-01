import Charter.Engine.Deals

/-!
# Proposals and votes

Anyone can propose during the actions phase, up to `maxOpenPerSeat` open proposals per seat. A
proposal stays open until its proposer's next turn starts. The vote that gives a law more than
half of all seats decides it: the law leaves the open list and passes if it is still valid.
-/

namespace Charter.Engine

variable {G : GameDef}

/-- Add a proposal to the open list with the next id. -/
def addProposal (s : State G) (seat : Seat) (body : Proposal) : State G :=
  { s with
    openProposals :=
      s.openProposals ++
        [{ id := s.nextProposalId, by_ := seat, body := body, votes := [], signed := [] }]
    nextProposalId := s.nextProposalId + 1 }

/-- Propose a law: it must be valid now. Proposing costs nothing. -/
def proposeLaw (s : State G) (seat : Seat) (L : Law) : Except String (State G) :=
  if !(lawProblems G s L).isEmpty then .error "this law cannot pass"
  else .ok (addProposal s seat (.law L))

/-- Propose a deal: it must be able to run, and the proposer must be a signer. -/
def proposeDeal (s : State G) (seat : Seat) (d : Deal) : Except String (State G) :=
  if !d.signers.contains seat then .error "only a signer can propose a deal"
  else if !(dealProblems s d).isEmpty then .error "this deal cannot run"
  else .ok (addProposal s seat (.deal d))

/-- Make a proposal in the actions phase. -/
def proposeBody (s : State G) (seat : Seat) (body : Proposal) : Except String (State G) :=
  if s.phase != .actions then .error "proposals can be made only in the actions phase"
  else if maxOpenPerSeat ≤ (s.openProposals.filter (·.by_ == seat)).length then
    .error "this seat has too many open proposals"
  else
    match body with
    | .law L => proposeLaw s seat L
    | .deal d => proposeDeal s seat d

/-- This vote is yes and gives the law more than half of all seats. -/
def isDecidingVote (s : State G) (p : OpenProposal) (seat : Seat) (yes : Bool) : Bool :=
  yes && decide ((p.withVote seat true).yesCount * 2 > s.turnOrder.length)

/-- The deciding vote: the law leaves the open list and passes if it is still valid. -/
def decideLaw (s : State G) (id : Nat) (L : Law) : State G :=
  let closed := s.openProposals.filter (·.id != id)
  if (lawProblems G s L).isEmpty then
    { s with openProposals := closed, laws := enact s.laws id L }
  else
    { s with openProposals := closed }

/-- Cast one final vote on an open law. -/
def voteBody (s : State G) (seat id : Nat) (yes : Bool) : Except String (State G) :=
  if s.phase != .actions then .error "votes can be cast only in the actions phase"
  else
    match s.openProposal? id with
    | none => .error "there is no such proposal"
    | some p =>
      match p.body with
      | .deal _ => .error "a deal is signed, not voted on"
      | .law L =>
        if (p.votes.map (·.1)).contains seat then .error "a vote is final"
        else if isDecidingVote s p seat yes then .ok (decideLaw s id L)
        else .ok { s with
          openProposals := s.openProposals.map fun q =>
            if q.id == id then q.withVote seat yes else q }

end Charter.Engine
