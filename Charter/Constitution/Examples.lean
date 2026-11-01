import Charter.Constitution
import Charter.Games.Tiny
import Charter.Proofs.Witness

/-!
# Examples

These show that the promises are not empty:

* Three full games really run to the end, on three different game definitions. One starts with a
  founding law.
* The conditions the theorems assume can be met. `tinySettlers_valid` gives a valid game, and the last
  example here gives a reachable state.
* The promises reject bad steps. Each `..._is_rejected` theorem shows a named part of a commandment
  saying no to a forged step. Next to most is an `example` of the honest step, which it allows.

The states in the rejection examples are small and built by hand. They are not reachable games. They
test what the words say, not what the engine does.
-/

namespace Charter

/-! ## Full games

An engine that rejects every event would keep most of the promises about what cannot happen. These
rule that out. -/

/-- A complete game of Tiny Settlers exists, in which a law passes, a deal starts and a seat wins. -/
theorem a_full_game_exists :
    ∃ events s, Engine.replay tinySettlers 2 42 [25283273] events = .ok s ∧
      s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws ≠ [] ∧ 1 ≤ s.dealsStarted :=
  Proofs.a_full_game_exists

/-- The same is true of Tiny Space, a game with a different structure. -/
theorem a_full_space_game_exists :
    ∃ events s, Engine.replay tinySpace 3 7 [23841] events = .ok s ∧
      s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws ≠ [] ∧ 1 ≤ s.dealsStarted :=
  Proofs.a_full_space_game_exists

/-- A game can start with a founding law. A complete game of Tiny Founded exists, in which a seat wins
and the founding law, with id 0, is still in force at the end. -/
theorem a_founded_game_exists :
    ∃ events s, Engine.replay tinyFounded 2 42 [25283273] events = .ok s ∧
      s.phase = .ended ∧ s.winner.isSome = true ∧ s.laws.map (·.1) = [0] :=
  Proofs.a_founded_game_exists

/-! ## The promises reject bad steps -/

/-- A game in the actions phase, with nothing open. -/
def sampleGame : State tinySettlers :=
  { initialState tinySettlers 2 42 [25283273] with phase := .actions }

/-- An open law in `sampleGame`, with these votes. -/
def sampleLaw (votes : List (Seat × Bool)) : OpenProposal :=
  { id := 0, by_ := 0, body := .law ⟨"Cheap trades", [.setBankRate 2]⟩, votes := votes, signed := [] }

/-- `sampleGame` with that law open. -/
def voteGame (votes : List (Seat × Bool)) : State tinySettlers :=
  { sampleGame with openProposals := [sampleLaw votes], nextProposalId := 1 }

/-- Seat 1 votes, but the step writes the vote down as seat 0's. III rejects this. -/
theorem forged_vote_is_rejected :
    ¬ ProposalsKept (voteGame []) (voteGame [(0, true)]) (.vote 1 0 true) := by
  intro h
  have := h.1 (sampleLaw [(0, true)]) (by simp [voteGame])
  simp [voteGame, sampleLaw, proposalAfter, OpenProposal.withVote] at this

/-- The honest step is allowed: seat 1 votes, and the vote is written down as seat 1's. -/
example : ProposalsKept (voteGame []) (voteGame [(1, true)]) (.vote 1 0 true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simp [voteGame] at hq
    subst hq
    simp [voteGame, sampleLaw, proposalAfter, OpenProposal.withVote]
  · intro p hp _
    simp [voteGame] at hp
    subst hp
    simp [ProposalCloses, EndsTurn, voteGame, sampleLaw, sampleGame, initialState, proposalAfter,
      OpenProposal.withVote, OpenProposal.hasMajority, OpenProposal.yesCount]
  · simp [voteGame, sampleGame, initialState]

/-- A bank trade cannot delete an open proposal. III rejects this. -/
theorem deleted_proposal_is_rejected :
    ¬ ProposalsKept (voteGame []) sampleGame (.move 0 (.bankTrade "grain" "brick")) := by
  intro h
  have := (h.2.1 (sampleLaw []) (by simp [voteGame]) (by simp [sampleGame, initialState])).2
    (by simp [ProposalCloses, EndsTurn])
  simp [sampleGame, initialState, proposalAfter] at this

/-- Seat 1's turn is the last of round 1, in a game with an open law from seat 0. -/
def expiryGame : State tinySettlers := { voteGame [] with turnIndex := 1 }

/-- The honest step is allowed: the proposal expires as its proposer's next turn starts. -/
example : ProposalsKept expiryGame { sampleGame with turnIndex := 0, round := 2 } .forceEndTurn := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sampleGame, initialState]
  · intro p hp _
    simp [expiryGame, voteGame] at hp
    subst hp
    have hCloses : ProposalCloses expiryGame { sampleGame with turnIndex := 0, round := 2 }
        .forceEndTurn (sampleLaw []) := by
      refine Or.inr (Or.inr ⟨trivial, ?_, ?_⟩)
      · decide
      · simp [State.currentSeat, sampleGame, initialState, sampleLaw]
    refine ⟨fun _ => ?_, fun hNot => absurd hCloses hNot⟩
    simp [sampleGame, initialState]
  · simp [sampleGame, initialState]

/-- An offer of 1 grain for 1 brick, made by seat `src`. -/
def sampleOffer (src : Seat) : Offer := ⟨0, src, none, [("grain", 1)], [("brick", 1)]⟩

/-- `sampleGame` with that offer open. -/
def offerGame (src : Seat) : State tinySettlers :=
  { sampleGame with offers := [sampleOffer src], nextOfferId := 1 }

/-- Seat 1 sends an offer, but the step writes it down as seat 0's. V rejects this. -/
theorem forged_offer_is_rejected :
    ¬ OffersKept sampleGame (offerGame 0)
      (.move 1 (.offer none [("grain", 1)] [("brick", 1)])) := by
  intro h
  have := h (sampleOffer 0) (by simp [offerGame])
  simp [sampleGame, initialState, sampleOffer] at this

/-- The honest step is allowed: seat 1 sends the offer, and it is written down as seat 1's. -/
example : OffersKept sampleGame (offerGame 1)
    (.move 1 (.offer none [("grain", 1)] [("brick", 1)])) := by
  intro o ho
  simp [offerGame] at ho
  subst ho
  simp [sampleGame, initialState, sampleOffer]

/-- A bank trade pays out one timber as well as the brick it should. V rejects this. -/
theorem minted_goods_are_rejected :
    ¬ MoneyLeavesBankOnlyFor sampleGame (.move 0 (.bankTrade "grain" "brick"))
      ⟨.bank, .player 0, "timber", 1, .trade⟩ := by
  intro h
  have := h (Or.inl rfl)
  simp [IsDicePayout, IsBankTradeAtPrice, AskedForByLaw, State.bankTradeEntries] at this

/-- The honest step is allowed: the bank pays out the 1 brick the trade asks for. -/
example : MoneyLeavesBankOnlyFor sampleGame (.move 0 (.bankTrade "grain" "brick"))
    ⟨.bank, .player 0, "brick", 1, .trade⟩ :=
  fun _ => Or.inr (Or.inl ⟨rfl, 0, "grain", "brick", rfl, by simp [State.bankTradeEntries]⟩)

/-- A deal agreed for 2 rounds from round 1, with this last round. -/
def sampleDeal (lastRound : Nat) : ActiveDeal :=
  { id := 0, lastRound := lastRound, startRound := 1, builtBefore := 0
    deal := { title := "Pact", signers := [0, 1], rounds := 2, exitNotice := 0
              deposits := [], terms := [] } }

/-- `sampleGame` with that deal running. -/
def dealGame (lastRound : Nat) : State tinySettlers :=
  { sampleGame with deals := [sampleDeal lastRound], dealsStarted := 1 }

/-- A deal agreed for 2 rounds from round 1 cannot last until round 3. VI rejects this. -/
theorem deal_past_its_term_is_rejected :
    ¬ ((sampleDeal 3).lastRound + 1 ≤ (sampleDeal 3).startRound + (sampleDeal 3).deal.rounds) := by
  decide

/-- A step cannot move a deal's last round later, not even by an exit. VI rejects this. -/
theorem extended_deal_is_rejected : ¬ DealsKept (dealGame 2) (dealGame 3) (.exit 0 0) := by
  intro h
  have := h.1 (sampleDeal 3) (by simp [dealGame])
  simp [dealGame, sampleDeal, sampleGame, initialState, dealAfter] at this

/-- The honest step is allowed: a signer's exit sets the last round exactly. -/
example : DealsKept (dealGame 2) (dealGame 1) (.exit 0 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp [dealGame] at hd
    subst hd
    simp [dealGame, sampleDeal, sampleGame, initialState, dealAfter]
  · intro d hd _
    simp [dealGame] at hd
    subst hd
    simp [dealGame, sampleDeal, sampleGame, initialState, dealAfter, DealCloses, EndsTurn]
  · simp [dealGame, sampleGame, initialState]

/-- A bank trade cannot shorten a deal. VI rejects this. -/
theorem shortened_deal_is_rejected :
    ¬ DealsKept (dealGame 2) (dealGame 1) (.move 0 (.bankTrade "grain" "brick")) := by
  intro h
  have := h.1 (sampleDeal 1) (by simp [dealGame])
  simp [dealGame, sampleDeal, dealAfter] at this

/-- `dealGame` on the last turn of round 1. -/
def lastTurnDealGame (lastRound : Nat) : State tinySettlers :=
  { dealGame lastRound with turnIndex := 1 }

/-- The round's end cannot drop a deal that still has a round to run. VI rejects this. -/
theorem dropped_deal_is_rejected :
    ¬ DealsKept (lastTurnDealGame 2) sampleGame .forceEndTurn := by
  intro h
  have := (h.2.1 (sampleDeal 2) (by simp [lastTurnDealGame, dealGame])
    (by simp [sampleGame, initialState])).2
    (by
      simp [DealCloses, EndsTurn, State.isLastTurn, State.closingDeals, lastTurnDealGame, dealGame,
        sampleGame, initialState, sampleDeal, tinySettlers])
  simp [sampleGame, initialState, dealAfter] at this

/-- The honest step is allowed: the deal is due to close at this round's end, so it goes. -/
example : DealsKept (lastTurnDealGame 1) sampleGame .forceEndTurn := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sampleGame, initialState]
  · intro d hd _
    simp [lastTurnDealGame, dealGame] at hd
    subst hd
    have hCloses : DealCloses (lastTurnDealGame 1) .forceEndTurn (sampleDeal 1) := by
      refine ⟨trivial, ?_, ?_⟩
      · decide
      · simp [State.closingDeals, lastTurnDealGame, dealGame, sampleGame, initialState, sampleDeal,
          tinySettlers]
    refine ⟨fun _ => ?_, fun hNot => absurd hCloses hNot⟩
    simp [sampleGame, initialState]
  · simp [sampleGame, initialState]

/-- A step cannot remove a seat from the game. III rejects this. -/
theorem removed_seat_is_rejected : ¬ SeatsStayFixed sampleGame { sampleGame with turnOrder := [1] } := by
  simp only [SeatsStayFixed, sampleGame, initialState]
  decide

/-- The honest step is allowed: the round moves on, and the seats stay. -/
example : SeatsStayFixed sampleGame { sampleGame with round := 2 } := rfl

/-- Seat 0 votes, but the step uses up seat 1's actions. III rejects this. -/
theorem silenced_seat_is_rejected :
    ¬ ActionsAreCountedExactly sampleGame
      { sampleGame with actionsThisTurn := fun q => if q = 1 then maxActionsPerTurn else 0 }
      (.vote 0 0 true) := by
  intro h
  obtain ⟨p, hp, hq⟩ := h.2 (by simp [EndsTurn])
  simp only [senderOf, Option.some.injEq] at hp
  subst hp
  have := hq 1
  simp [sampleGame, initialState, maxActionsPerTurn] at this

/-- The honest step is allowed: seat 0's vote counts against seat 0 alone. -/
example : ActionsAreCountedExactly sampleGame
    { sampleGame with actionsThisTurn := fun q => if q = 0 then 1 else 0 } (.vote 0 0 true) := by
  refine ⟨fun h => absurd h (by simp [EndsTurn]), fun _ => ⟨0, rfl, ?_⟩⟩
  intro q
  by_cases hq : q = 0 <;> simp [sampleGame, initialState, hq]

/-- A vote cannot put the game back into setup. III rejects this. -/
theorem changed_phase_is_rejected :
    ¬ PhaseChangesOnlyByTurnOrWin sampleGame { sampleGame with phase := .setup } (.vote 0 0 true) := by
  intro h
  rcases h (by simp [EndsTurn]) with h1 | ⟨h1, _⟩ <;> simp [sampleGame] at h1

/-- The honest step is allowed: a vote keeps the phase. -/
example : PhaseChangesOnlyByTurnOrWin sampleGame sampleGame (.vote 0 0 true) := fun _ => Or.inl rfl

/-- Two open proposals with one id, so a vote on one could land on the other. III rejects this. -/
theorem shared_proposal_id_is_rejected :
    ¬ ProposalIdsAreUnique
      ({ sampleGame with openProposals := [sampleLaw [], sampleLaw [(1, true)]] } : State tinySettlers) := by
  simp [ProposalIdsAreUnique, sampleLaw]

/-- The honest state is allowed: one open proposal, with its own id. -/
example : ProposalIdsAreUnique (voteGame []) := by
  simp [ProposalIdsAreUnique, voteGame]

/-- An open proposal of the deal in `sampleDeal`, with these signatures. -/
def dealProposal (signed : List Seat) : OpenProposal :=
  { id := 0, by_ := 0, body := .deal (sampleDeal 2).deal, votes := [], signed := signed }

/-- `sampleGame` with that deal proposed. -/
def signGame (signed : List Seat) : State tinySettlers :=
  { sampleGame with openProposals := [dealProposal signed], nextProposalId := 1 }

/-- Seat 0 signs first, but the deal starts without seat 1. VI rejects this. -/
theorem unsigned_deal_is_rejected :
    ¬ DealsKept (signGame []) { signGame [] with deals := [sampleDeal 2], dealsStarted := 1 }
      (.sign 0 0) := by
  intro h
  rcases h.1 (sampleDeal 2) (by simp) with ⟨seat, id, p, d, he, hp, hd, _, hall, _⟩ | ⟨d, hd, _⟩
  · injection he with h1 h2
    subst h1 h2
    simp [signGame, State.openProposal?, dealProposal] at hp
    subst hp
    simp at hd
    subst hd
    have := hall 1 (by simp [sampleDeal])
    simp at this
  · simp [signGame, sampleGame, initialState] at hd

/-- The honest step is allowed: seat 1 has signed, and seat 0's signature starts the deal. -/
example : DealsKept (signGame [1])
    { sampleGame with deals := [sampleDeal 2], dealsStarted := 1, nextProposalId := 1 } (.sign 0 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    simp at hd
    subst hd
    refine Or.inl ⟨0, 0, dealProposal [1], (sampleDeal 2).deal, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [State.openProposal?, signGame, dealProposal]
    · simp [sampleDeal]
    · simp [sampleDeal, dealProposal]
    · simp [signGame, sampleGame, initialState, sampleDeal]
  · intro d hd
    simp [signGame, sampleGame, initialState] at hd
  · simp [sampleGame, initialState]

/-- Seat 1 accepts an offer, and the step pays it a timber from the bank as well. V rejects this. -/
theorem padded_offer_is_rejected :
    ¬ AcceptedOffersAreExact (offerGame 0)
      { offerGame 0 with
        journal := offerEntries (sampleOffer 0) 1 ++ [⟨.bank, .player 1, "timber", 1, .trade⟩] }
      (.move 1 (.accept 0)) := by
  intro h
  have := (h 1 0 (sampleOffer 0) rfl (by simp [offerGame, sampleOffer])).2.2
  simp [newEntries, offerGame, sampleGame, initialState] at this

/-- The maker of an offer cannot accept it. V rejects this. -/
theorem own_offer_accepted_is_rejected :
    ¬ AcceptedOffersAreExact (offerGame 0) (offerGame 0) (.move 0 (.accept 0)) := by
  intro h
  exact (h 0 0 (sampleOffer 0) rfl (by simp [offerGame, sampleOffer])).1 rfl

/-- The honest step is allowed: seat 1 accepts, and exactly the offered goods move. -/
example : AcceptedOffersAreExact (offerGame 0)
    { offerGame 0 with journal := offerEntries (sampleOffer 0) 1 } (.move 1 (.accept 0)) := by
  intro p id o he ho
  injection he with h1 h2
  subst h1
  injection h2 with h2
  subst h2
  simp [offerGame, sampleOffer] at ho
  subst ho
  refine ⟨by simp, Or.inl rfl, ?_⟩
  simp [newEntries, offerGame, sampleGame, initialState]
  rfl

/-- A step that does not add to the count of events. IX rejects this. -/
theorem uncounted_event_is_rejected : ¬ EveryEventIsCounted sampleGame sampleGame := by
  simp [EveryEventIsCounted]

/-- The honest step is allowed: the count goes up by one. -/
example : EveryEventIsCounted sampleGame { sampleGame with eventsApplied := 1 } := rfl

/-- A vote from a seat that has used all its actions. IX rejects this. -/
theorem action_over_limit_is_rejected :
    ¬ ActionLimitIsEnforced
      ({ sampleGame with actionsThisTurn := fun _ => maxActionsPerTurn } : State tinySettlers)
      (.vote 0 0 true) := by
  intro h
  obtain ⟨p, _, hlt⟩ := h (by simp [EndsTurn])
  simp at hlt

/-- The honest step is allowed: the vote comes from a seat under its limit. -/
example : ActionLimitIsEnforced sampleGame (.vote 0 0 true) :=
  fun _ => ⟨0, rfl, by simp [sampleGame, initialState, maxActionsPerTurn]⟩

/-- `offerGame 0` with a trade block, or embargo: a running deal in which seat 0 promised not to trade
with seat 1. -/
def embargoGame : State tinySettlers :=
  { offerGame 0 with
    deals := [{ sampleDeal 2 with deal := { (sampleDeal 2).deal with terms := [.noTrade 0 1] } }]
    dealsStarted := 1 }

/-- Seat 1 accepts seat 0's offer across the embargo. VI rejects this. -/
theorem trade_across_embargo_is_rejected :
    ¬ BlockedTradesAreRejected embargoGame (.move 1 (.accept 0)) := by
  intro h
  have := h.1 1 0 (sampleOffer 0) rfl (by simp [embargoGame, offerGame, sampleOffer])
  simp [State.tradeBlocked, embargoGame, sampleOffer, sampleDeal] at this

/-- Seat 0 addresses an offer to seat 1 across the embargo. VI rejects this. -/
theorem offer_across_embargo_is_rejected :
    ¬ BlockedTradesAreRejected embargoGame (.move 0 (.offer (some 1) [("grain", 1)] [("brick", 1)])) := by
  intro h
  have := h.2 0 1 _ _ rfl
  simp [State.tradeBlocked, embargoGame, sampleDeal] at this

/-- The honest step is allowed: with no embargo, seat 1 can accept. -/
example : BlockedTradesAreRejected (offerGame 0) (.move 1 (.accept 0)) := by
  refine ⟨?_, ?_⟩
  · intro p id o _ _
    simp [State.tradeBlocked, offerGame, sampleGame, initialState]
  · intro p q give get he
    cases he

/-- The conditions the theorems assume can be met: this new game is reachable. -/
example : Reachable tinySettlers (initialState tinySettlers 2 42 [25283273]) :=
  .start 2 42 [25283273] (by decide) (by decide) (by simp)

end Charter
