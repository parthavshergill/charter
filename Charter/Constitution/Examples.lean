import Charter.Constitution
import Charter.Games.Tiny
import Charter.Proofs.Witness
import Charter.Proofs.Replay

/-!
# Examples

These show that the promises are not empty:

* Three full games really run to the end, on three different game definitions. One starts with a
  founding law.
* The conditions the theorems assume can be met. `tinySettlers_valid` gives a valid game, and the last
  example here gives a reachable state.
* A law can react to a roll. `a_seven_moves_money` plays a real game in which a 7 moves money, and laws
  over the payment limits are rejected.
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

/-! ## Laws that react to the roll -/

/-- The entries of the Lucky Seven law when the roll starts the turn of `actor`, in a game with no
pieces on the map. -/
def luckySevenEntries (actor : Seat) : List Entry :=
  [ ⟨.bank, .player actor, "timber", 1, .lawEffect⟩
  , ⟨.bank, .player 0, "grain", 1, .lawEffect⟩
  , ⟨.bank, .player 1, "grain", 1, .lawEffect⟩ ]

/-- A test of one roll: the next turn change shows a 7, starts the turn of `actor`, and makes exactly
the Lucky Seven entries. -/
def sevenPays (r : Except String (State tinySevens)) (actor : Seat) : Bool :=
  match r with
  | .error _ => false
  | .ok s =>
    match Engine.step tinySevens s .forceEndTurn with
    | .error _ => false
    | .ok s' =>
      s'.lastRoll == some 7 && s'.rollsMade == s.rollsMade + 1 && s.isLastTurn == false &&
        s'.currentSeat == some actor && newEntries s s' == luckySevenEntries actor

/-- A 7 really moves money, in a real game. Every seat skips setup. The first roll of this game is a
7, and it pays nobody from the map. The founding law still fires: the bank pays the seat whose turn
starts and every seat. So each hypothesis of `RollPaysExactly` is met on a 7. -/
theorem a_seven_moves_money :
    ∃ s s', Reachable tinySevens s ∧ Engine.step tinySevens s .forceEndTurn = .ok s' ∧
      EndsTurn s .forceEndTurn ∧ s'.rollsMade = s.rollsMade + 1 ∧ s.isLastTurn = false ∧
      s'.lastRoll = some 7 ∧ s'.currentSeat = some 0 ∧
      newEntries s s' = luckySevenEntries 0 ∧ newEntries s s' = rollEntries s 7 := by
  have hc : sevenPays (Engine.replay tinySevens 2 42 [3] (List.replicate 3 .forceEndTurn)) 0 = true := by
    decide +kernel
  cases hr : Engine.replay tinySevens 2 42 [3] (List.replicate 3 .forceEndTurn) with
  | error m =>
    rw [hr] at hc
    simp [sevenPays] at hc
  | ok s =>
    rw [hr] at hc
    cases hs : Engine.step tinySevens s .forceEndTurn with
    | error m => simp [sevenPays, hs] at hc
    | ok s' =>
      simp only [sevenPays, hs, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      have hreach : Reachable tinySevens s :=
        ((X_what_you_vote_on_is_what_runs tinySevens tinySevens_valid).1 s).mpr
          ⟨2, 42, [3], _, by decide, by decide, hr⟩
      have hroll := (X_what_you_vote_on_is_what_runs tinySevens tinySevens_valid).2.2.2.1
        s s' .forceEndTurn hreach hs trivial h2
      have hval : rollAt tinySevens s.seed s.rollsMade = 7 := by
        have h7 := VIII_nobody_controls_the_dice tinySevens tinySevens_valid s s' .forceEndTurn hreach hs
        rcases h7.2.2.2.1 with ⟨h8, _⟩ | ⟨_, h8⟩
        · omega
        · rw [h1] at h8
          exact (Option.some.inj h8).symm
      refine ⟨s, s', hreach, hs, trivial, h2, h3, h1, h4, h5, ?_⟩
      rw [hroll.1 h3, hval]

/-- The next roll of that game is also a 7, and the law acts for seat 1, whose turn it starts. -/
theorem the_actor_is_the_seat_whose_turn_starts :
    sevenPays (Engine.replay tinySevens 2 42 [3] (List.replicate 4 .forceEndTurn)) 1 = true := by
  decide +kernel

/-- The Lucky Seven game with the first roll about to come, and seat 1 next to play. -/
def sevenGame : State tinySevens :=
  { initialState tinySevens 2 42 [3] with phase := .actions }

/-- The roll about to come in `sevenGame`. -/
def sevenRoll : Nat := rollAt tinySevens sevenGame.seed sevenGame.rollsMade

/-- The honest entries: on a 7, the law pays exactly what it says. -/
example : rollEntries (sevenGame.afterPosting sevenGame.entriesBeforeRoll) sevenRoll =
    luckySevenEntries 1 := by
  decide +kernel

/-- On any other roll, the law moves nothing. -/
example : rollEntries sevenGame 8 = [] := by decide +kernel

/-- A roll that skips the law's payments. X rejects this: the entries of a roll must be exactly
`rollEntries`, and those are not empty. -/
theorem skipped_seven_is_rejected :
    ([] : List Entry) ≠ rollEntries (sevenGame.afterPosting sevenGame.entriesBeforeRoll) sevenRoll := by
  decide +kernel

/-- On a 7, a step takes 1 grain from seat 0 for seat 1, and no law asks for it. V rejects this. -/
theorem forged_seven_payment_is_rejected :
    ¬ MoneyLeavesSeatOnlyFor sevenGame sevenGame .forceEndTurn
      ⟨.player 0, .player 1, "grain", 1, .lawEffect⟩ := by
  intro h
  have hEnd : ⟨.player 0, .player 1, "grain", 1, .lawEffect⟩ ∉
      rollEntries (sevenGame.afterPosting sevenGame.entriesBeforeRoll) sevenRoll := by decide +kernel
  have hRound : ⟨.player 0, .player 1, "grain", 1, .lawEffect⟩ ∉
      sevenGame.roundEndLawEntries := by decide +kernel
  rcases h 0 rfl with ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨_, _, hf, _⟩ | ⟨_, h1⟩
  · cases hr
  · cases hr
  · cases hr
  · cases hf
  · rcases h1 with ⟨_, _, _, he, _⟩ | ⟨_, h2⟩
    · cases he
    · rcases h2 with h2 | h2
      · exact hRound h2
      · exact hEnd h2

/-- On a 7, the bank pays the timber to seat 0, but the law pays the seat whose turn starts, which is
seat 1. V rejects this. -/
theorem wrong_actor_is_rejected :
    ¬ MoneyLeavesBankOnlyFor sevenGame .forceEndTurn ⟨.bank, .player 0, "timber", 1, .lawEffect⟩ := by
  intro h
  have hEnd : ⟨.bank, .player 0, "timber", 1, .lawEffect⟩ ∉
      rollEntries (sevenGame.afterPosting sevenGame.entriesBeforeRoll) sevenRoll := by decide +kernel
  have hRound : ⟨.bank, .player 0, "timber", 1, .lawEffect⟩ ∉
      sevenGame.roundEndLawEntries := by decide +kernel
  rcases h (Or.inl rfl) with ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨_, h1⟩
  · cases hr
  · cases hr
  · rcases h1 with ⟨_, _, _, he, _⟩ | ⟨_, h2⟩
    · cases he
    · rcases h2 with h2 | h2
      · exact hRound h2
      · exact hEnd h2

/-- The honest entry is allowed: the bank pays seat 1, whose turn the roll starts. -/
example : MoneyLeavesBankOnlyFor sevenGame .forceEndTurn ⟨.bank, .player 1, "timber", 1, .lawEffect⟩ :=
  fun _ => Or.inr (Or.inr ⟨rfl, Or.inr ⟨trivial, Or.inr (by decide +kernel)⟩⟩)

/-- With no law that reacts to a roll, a roll is the harvest alone. So a saved game with no such law
replays as it always did. -/
theorem no_roll_law_means_harvest_alone {G : GameDef} (s : State G) (roll : Nat)
    (h : ∀ x ∈ s.laws, ∀ c ∈ x.2.clauses, ∀ b, c ≠ .onRoll b) :
    rollEntries s roll = harvestEntries s roll :=
  Proofs.rollEntries_no_roll_law s roll h

/-- A law that reacts to a roll, with this many transfers for each seat. -/
def wideRollLaw (transfers : Nat) : Law :=
  { title := "Wide"
    clauses := [.onRoll [.forEach .yes
      (List.replicate transfers (.transfer .each .treasury (.lit "grain") (.lit 1)))]] }

/-- A game of 6 seats, the most a game can have, with these laws in force. -/
def sixSeatGame (laws : List (Nat × Law)) : State tinySettlers :=
  { initialState tinySettlers 6 42 [25283273] with phase := .actions, laws := laws }

/-- A roll law counts against the limit on one law. At 6 seats, 10 transfers for each seat pass. -/
example : lawProblems tinySettlers (sixSeatGame []) (wideRollLaw 10) = [] := by decide +kernel

/-- At 6 seats, 11 transfers for each seat ask for 66 payments on one roll, over the limit of 64. -/
theorem roll_law_over_the_cap_is_rejected :
    "this law could make too many payments at once" ∈
      lawProblems tinySettlers (sixSeatGame []) (wideRollLaw 11) := by
  decide +kernel

/-- Roll laws count against the limit on all laws in force. Two laws of 60 payments are in force. A
third would make 180, over the limit of 128. -/
theorem roll_laws_over_the_total_cap_are_rejected :
    "the laws in force could make too many payments at once" ∈
      lawProblems tinySettlers (sixSeatGame [(0, wideRollLaw 10), (1, wideRollLaw 10)])
        (wideRollLaw 10) := by
  decide +kernel

/-- The conditions the theorems assume can be met: this new game is reachable. -/
example : Reachable tinySettlers (initialState tinySettlers 2 42 [25283273]) :=
  .start 2 42 [25283273] (by decide) (by decide) (by simp)

end Charter
