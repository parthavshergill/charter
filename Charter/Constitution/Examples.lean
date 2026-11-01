import Charter.Constitution
import Charter.Constitution.Supporting
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
* Totals, the most, the least, division by a computed number and the round each move money in a real
  game, and a wrong amount is rejected.
* A declaration changes what a law does. `an_auction_settles` is a worked auction, with a tie and a bid
  nobody can pay.
* A resource can be worth points, and a seat that reaches the target at a turn change wins at the next
  move or vote.
* A law can take a seat's newest piece, at a round's end or on a roll, and never its last.
* A decree fires once, the moment its law passes, and it names no actor.
* A bank trade and a setup placement run on real games, with every hypothesis of
  `bank_trades_and_setup_are_exact` met. A bank trade or a setup placement can end the game.
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
example : rollEntries sevenGame.afterRoundEnd sevenRoll =
    luckySevenEntries 1 := by
  decide +kernel

/-- On any other roll, the law moves nothing. -/
example : rollEntries sevenGame 8 = [] := by decide +kernel

/-- A roll that skips the law's payments. X rejects this: the entries of a roll must be exactly
`rollEntries`, and those are not empty. -/
theorem skipped_seven_is_rejected :
    ([] : List Entry) ≠ rollEntries sevenGame.afterRoundEnd sevenRoll := by
  decide +kernel

/-- On a 7, a step takes 1 grain from seat 0 for seat 1, and no law asks for it. V rejects this. -/
theorem forged_seven_payment_is_rejected :
    ¬ MoneyLeavesSeatOnlyFor sevenGame sevenGame .forceEndTurn
      ⟨.player 0, .player 1, "grain", 1, .lawEffect⟩ := by
  intro h
  have hEnd : ⟨.player 0, .player 1, "grain", 1, .lawEffect⟩ ∉
      rollEntries sevenGame.afterRoundEnd sevenRoll := by decide +kernel
  have hRound : ⟨.player 0, .player 1, "grain", 1, .lawEffect⟩ ∉
      sevenGame.roundEndLawEntries := by decide +kernel
  rcases h 0 rfl with ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨_, _, hf, _⟩ | ⟨_, h1⟩
  · cases hr
  · cases hr
  · cases hf
  · rcases h1 with ⟨_, _, _, he, _⟩ | ⟨_, h2⟩ | ⟨_, ⟨_, _, _, he, _⟩, _⟩
    · cases he
    · rcases h2 with h2 | h2
      · exact hRound h2
      · exact hEnd h2
    · cases he

/-- On a 7, the bank pays the timber to seat 0, but the law pays the seat whose turn starts, which is
seat 1. V rejects this. -/
theorem wrong_actor_is_rejected :
    ¬ MoneyLeavesBankOnlyFor sevenGame .forceEndTurn ⟨.bank, .player 0, "timber", 1, .lawEffect⟩ := by
  intro h
  have hEnd : ⟨.bank, .player 0, "timber", 1, .lawEffect⟩ ∉
      rollEntries sevenGame.afterRoundEnd sevenRoll := by decide +kernel
  have hRound : ⟨.bank, .player 0, "timber", 1, .lawEffect⟩ ∉
      sevenGame.roundEndLawEntries := by decide +kernel
  rcases h (Or.inl rfl) with ⟨hr, _⟩ | ⟨hr, _⟩ | ⟨_, h1⟩
  · cases hr
  · cases hr
  · rcases h1 with ⟨_, _, _, he, _⟩ | ⟨_, h2⟩ | ⟨_, ⟨_, _, _, he, _⟩, _⟩
    · cases he
    · rcases h2 with h2 | h2
      · exact hRound h2
      · exact hEnd h2
    · cases he

/-- The honest entry is allowed: the bank pays seat 1, whose turn the roll starts. -/
example : MoneyLeavesBankOnlyFor sevenGame .forceEndTurn ⟨.bank, .player 1, "timber", 1, .lawEffect⟩ :=
  fun _ => Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨trivial, Or.inr (by decide +kernel)⟩)⟩)

/-- With no law that reacts to a roll, a roll is the harvest alone, read from the round it starts. So a
saved game with no such law replays as it always did: no old law could read the round. -/
theorem no_roll_law_means_harvest_alone {G : GameDef} (s : State G) (roll : Nat)
    (h : ∀ x ∈ s.laws, ∀ c ∈ x.2.clauses, ∀ b, c ≠ .onRoll b) :
    rollEntries s roll = harvestEntries s.atRoll roll :=
  Proofs.rollEntries_no_roll_law s roll h

/-- A law that reacts to a roll, with this many transfers for each seat. -/
def wideRollLaw (transfers : Nat) : Law :=
  { title := "Wide"
    clauses := [.onRoll [.forEach .yes
      (List.replicate transfers (.transfer .each .treasury (.lit "grain") (.lit 1)))]] }

/-- A game of 6 seats, the most a game can have, with these laws in force. -/
def sixSeatGame (laws : List (Nat × Law)) : State tinySettlers :=
  { initialState tinySettlers 6 42 [25283273] with phase := .actions, laws := laws }

/-- A roll law counts against the limit on one law. At 6 seats, 21 transfers for each seat pass. -/
example : lawProblems tinySettlers (sixSeatGame []) (wideRollLaw 21) = [] := by decide +kernel

/-- At 6 seats, 22 transfers for each seat ask for 132 payments on one roll, over the limit of 128. -/
theorem roll_law_over_the_cap_is_rejected :
    "this law could make too many payments at once" ∈
      lawProblems tinySettlers (sixSeatGame []) (wideRollLaw 22) := by
  decide +kernel

/-- Roll laws count against the limit on all laws in force. Two laws of 126 payments are in force. A
third would make 378, over the limit of 256. -/
theorem roll_laws_over_the_total_cap_are_rejected :
    "the laws in force could make too many payments at once" ∈
      lawProblems tinySettlers (sixSeatGame [(0, wideRollLaw 21), (1, wideRollLaw 21)])
        (wideRollLaw 21) := by
  decide +kernel

/-! ## Measures: totals, the most, the least, division by a computed number, and the round

Each game here is real: it starts from a new game and every event goes through the engine. Nobody builds.
A founding law pays the seat whose turn each roll starts, as much as the dice show, so the seats hold
different amounts. The law under test then reads them. -/

/-- What a step writes in the journal, after these events from a new game. -/
def stepEntries (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (events : List Event) (e : Event) : Option (List Entry) :=
  match Engine.replay G seats serverSeed nonces events with
  | .error _ => none
  | .ok s =>
    match Engine.step G s e with
    | .error _ => none
    | .ok s' => some (newEntries s s')

/-- If those entries are what `stepEntries` says, a reachable state really takes that step and writes
them. So a game with no empty hypotheses comes from a single computed check. -/
theorem real_step {G : GameDef} (hG : G.Valid) {seats : Nat} {serverSeed : UInt64} {nonces : List UInt64}
    {events : List Event} {e : Event} {es : List Entry} (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats)
    (hc : stepEntries G seats serverSeed nonces events e = some es) :
    ∃ s s', Reachable G s ∧ Engine.step G s e = .ok s' ∧ newEntries s s' = es := by
  unfold stepEntries at hc
  split at hc
  · cases hc
  · rename_i s hr
    split at hc
    · cases hc
    · rename_i s' hs
      refine ⟨s, s', ((X_what_you_vote_on_is_what_runs G hG).1 s).mpr
        ⟨seats, serverSeed, nonces, events, h1, h2, hr⟩, hs, ?_⟩
      exact Option.some.inj hc

/-- A founding law: the seat whose turn the roll starts gets as much grain as the dice show. -/
def rollerGift : Law :=
  { title := "Roller's gift", clauses := [.onRoll [.transfer .bank .actor (.lit "grain") .rolled]] }

/-- Tiny Settlers with two dice, with `rollerGift` and one more founding law. -/
def giftGame (L : Law) : GameDef :=
  { tinySettlers with
    name := "Gift"
    diceCount := 2
    diceSides := 6
    foundingLaws := [rollerGift, L] }

/-- Every setup turn is skipped, and then the first two turns of round 1 end. The next turn end closes
round 1. -/
def toRoundEnd : List Event := List.replicate 5 .forceEndTurn

/-- A step of a gift game, after `toRoundEnd`. -/
theorem real_gift_step {L : Law} (hG : (giftGame L).Valid) {es : List Entry}
    (hc : stepEntries (giftGame L) 2 42 [2] toRoundEnd .forceEndTurn = some es) :
    ∃ s s', Reachable (giftGame L) s ∧ Engine.step (giftGame L) s .forceEndTurn = .ok s' ∧
      newEntries s s' = es :=
  real_step hG (by decide) (by decide) hc

/-- A total: at a round's end, the bank pays the treasury as much timber as all seats hold grain. -/
def totalLaw : Law :=
  { title := "Total"
    clauses := [.onRoundEnd [.transfer .bank .treasury (.lit "timber")
      (.totalOver .yes (.holding .each (.lit "grain")))]] }

theorem totalLaw_valid : (giftGame totalLaw).Valid := by decide +kernel

/-- The law really moves money in a real game. The seats hold 10 and 5 grain, so the treasury gets 15 timber. The last entry is
the next roll's gift. -/
theorem a_total_moves_money :
    ∃ s s', Reachable (giftGame totalLaw) s ∧ Engine.step (giftGame totalLaw) s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.bank, .treasury, "timber", 15, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] :=
  real_gift_step totalLaw_valid (by decide +kernel)

/-- A step that pays only one seat's grain as the total is not what the law says. -/
theorem wrong_total_is_rejected :
    stepEntries (giftGame totalLaw) 2 42 [2] toRoundEnd .forceEndTurn ≠
      some [⟨.bank, .treasury, "timber", 10, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] := by
  decide +kernel

/-- The most and the least: at a round's end, the bank pays timber to each seat with the most grain and
brick to each seat with the least. These are numbers, so each seat is compared with them. -/
def rankLaw : Law :=
  { title := "Rank"
    clauses := [.onRoundEnd
      [ .forEach (.eq (.holding .each (.lit "grain")) (.mostOver .yes (.holding .each (.lit "grain"))))
          [.transfer .bank .each (.lit "timber") (.lit 2)]
      , .forEach (.eq (.holding .each (.lit "grain")) (.leastOver .yes (.holding .each (.lit "grain"))))
          [.transfer .bank .each (.lit "brick") (.lit 1)] ]] }

theorem rankLaw_valid : (giftGame rankLaw).Valid := by decide +kernel

/-- In a real game, the richer seat gets the timber and the poorer seat gets the brick. -/
theorem the_most_and_the_least_move_money :
    ∃ s s', Reachable (giftGame rankLaw) s ∧ Engine.step (giftGame rankLaw) s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.bank, .player 0, "timber", 2, .lawEffect⟩,
        ⟨.bank, .player 1, "brick", 1, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] :=
  real_gift_step rankLaw_valid (by decide +kernel)

/-- Paying the prize to the poorer seat is rejected. -/
theorem prize_to_the_wrong_seat_is_rejected :
    stepEntries (giftGame rankLaw) 2 42 [2] toRoundEnd .forceEndTurn ≠
      some [⟨.bank, .player 1, "timber", 2, .lawEffect⟩,
        ⟨.bank, .player 0, "brick", 1, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] := by
  decide +kernel

/-- A real tie: with this seed both seats hold 7 grain, so both have the most and both have the least. -/
theorem a_tie_pays_both_seats :
    ∃ s s', Reachable (giftGame rankLaw) s ∧ Engine.step (giftGame rankLaw) s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.bank, .player 0, "timber", 2, .lawEffect⟩, ⟨.bank, .player 1, "timber", 2, .lawEffect⟩,
        ⟨.bank, .player 0, "brick", 1, .lawEffect⟩, ⟨.bank, .player 1, "brick", 1, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] :=
  real_step (seats := 2) (serverSeed := 42) (nonces := [3]) (events := toRoundEnd) rankLaw_valid
    (by decide) (by decide) (by decide +kernel)

/-- A tie means several seats match. In a new game every seat holds 0 grain, so both seats pass. No seat
is told apart, and the name of a seat plays no part. -/
example : (Expr.mostOver .yes (.holding .each (.lit "grain"))).eval
    (initialState tinySettlers 2 42 [3]) {} = 0 := by decide +kernel
example : Effect.planAll (initialState tinySettlers 2 42 [3])
    [.forEach (.eq (.holding .each (.lit "grain")) (.mostOver .yes (.holding .each (.lit "grain"))))
      [.transfer .bank .each (.lit "timber") (.lit 2)]] {} =
    [⟨.bank, .player 0, "timber", 2, .lawEffect⟩, ⟨.bank, .player 1, "timber", 2, .lawEffect⟩] := by
  decide +kernel

/-- With no seat passing the test, the most and the least are 0, and a total is 0. -/
example : (Expr.mostOver (.lt (.lit 1) (.lit 0)) (.lit 5)).eval (initialState tinySettlers 2 42 [3]) {} = 0 ∧
    (Expr.leastOver (.lt (.lit 1) (.lit 0)) (.lit 5)).eval (initialState tinySettlers 2 42 [3]) {} = 0 ∧
    (Expr.totalOver (.lt (.lit 1) (.lit 0)) (.lit 5)).eval (initialState tinySettlers 2 42 [3]) {} = 0 := by
  decide +kernel

/-- Division by a computed number: at a round's end, each seat pays the treasury its grain divided by how
many seats hold any. A number that turns out to be 0 gives 0. -/
def divLaw : Law :=
  { title := "Share"
    clauses := [.onRoundEnd [.forEach .yes [.transfer .each .treasury (.lit "grain")
      (.divBy (.holding .each (.lit "grain")) (.totalOver (.lt (.lit 0) (.holding .each (.lit "grain"))) (.lit 1)))]]] }

theorem divLaw_valid : (giftGame divLaw).Valid := by decide +kernel

theorem division_moves_money :
    ∃ s s', Reachable (giftGame divLaw) s ∧ Engine.step (giftGame divLaw) s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.player 0, .treasury, "grain", 5, .lawEffect⟩,
        ⟨.player 1, .treasury, "grain", 2, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] :=
  real_gift_step divLaw_valid (by decide +kernel)

/-- Paying each seat's whole grain is not dividing it. -/
theorem undivided_payment_is_rejected :
    stepEntries (giftGame divLaw) 2 42 [2] toRoundEnd .forceEndTurn ≠
      some [⟨.player 0, .treasury, "grain", 10, .lawEffect⟩,
        ⟨.player 1, .treasury, "grain", 5, .lawEffect⟩, ⟨.bank, .player 0, "grain", 3, .lawEffect⟩] := by
  decide +kernel

example : (Expr.divBy (.lit 7) (.lit 2)).eval (initialState tinySettlers 2 42 [3]) {} = 3 ∧
    (Expr.divBy (.lit 7) (.holding .treasury (.lit "grain"))).eval (initialState tinySettlers 2 42 [3]) {} = 0 := by
  decide +kernel

/-- A law cannot write a literal division by zero, in its own words. It can compute one. -/
theorem literal_division_by_zero_is_rejected :
    "a law cannot divide by zero" ∈
      lawProblems tinySettlers (initialState tinySettlers 2 42 [3])
        { title := "Zero", clauses := [.onRoundEnd [.transfer .bank .treasury (.lit "grain")
            (.divBy (.lit 1) (.lit 0))]] } := by
  decide +kernel

/-- The round: on each roll, the bank pays the treasury as much timber as the round's number. -/
def roundLaw : Law :=
  { title := "Round", clauses := [.onRoll [.transfer .bank .treasury (.lit "timber") .round]] }

theorem roundLaw_valid : (giftGame roundLaw).Valid := by decide +kernel

/-- In a real game, the roll that starts round 2 reads 2, not 1. -/
theorem the_round_moves_money :
    ∃ s s', Reachable (giftGame roundLaw) s ∧ Engine.step (giftGame roundLaw) s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.bank, .player 0, "grain", 3, .lawEffect⟩, ⟨.bank, .treasury, "timber", 2, .lawEffect⟩] :=
  real_gift_step roundLaw_valid (by decide +kernel)

/-- A roll that starts round 2 and reads round 1 is rejected. -/
theorem old_round_is_rejected :
    stepEntries (giftGame roundLaw) 2 42 [2] toRoundEnd .forceEndTurn ≠
      some [⟨.bank, .player 0, "grain", 3, .lawEffect⟩, ⟨.bank, .treasury, "timber", 1, .lawEffect⟩] := by
  decide +kernel

/-- Measures that nest read what is inside them once per seat, so they count against `maxReadsTotal`.
Three levels read 517 numbers at 6 seats. Five levels read over 18,000. -/
def nestedMeasure : Nat → Expr
  | 0 => .lit 1
  | n + 1 => .totalOver .yes (nestedMeasure n)

example : (nestedMeasure 3).reads 6 = 517 := by decide +kernel

theorem nested_measures_over_the_cap_are_rejected :
    "the laws in force would read too many numbers at once" ∈
      lawProblems tinySettlers (sixSeatGame [])
        { title := "Deep", clauses := [.onRoundEnd [.transfer .bank .treasury (.lit "grain") (nestedMeasure 6)]] } := by
  decide +kernel

/-! ## Declarations

Each seat has one public number per resource, which it can change on its turn and which clears when the
round ends. In these games, each roll pays the seat whose turn it starts in wool, and puts grain in the
treasury. -/

/-- A founding law: wool for the seat whose turn the roll starts, and 4 grain for the treasury. -/
def auctionIncome : Law :=
  { title := "Income"
    clauses := [.onRoll [.transfer .bank .actor (.lit "wool") .rolled,
      .transfer .bank .treasury (.lit "grain") (.lit 4)]] }

/-- The bid of the seat being looked at. -/
def bid : Expr := .declared .each (.lit "grain")

/-- This seat holds enough wool to pay its bid. A bid it cannot pay does not count. -/
def canPayBid : Cond := .le bid (.holding .each (.lit "wool"))

/-- The worked auction, which uses a declaration, a test and the most. At a round's end, each seat with
the highest bid it can pay pays its bid to the treasury and asks for all the treasury's grain. If two
seats tie, both pay and they share the grain, as `settle` shrinks both requests alike. No seat's name
plays a part. -/
def auctionLaw : Law :=
  { title := "Grain auction"
    clauses := [.onRoundEnd [.forEach
      (.and (.lt (.lit 0) bid) (.and canPayBid (.eq bid (.mostOver canPayBid bid))))
      [ .transfer .each .treasury (.lit "wool") bid
      , .transfer .treasury .each (.lit "grain") (.holding .treasury (.lit "grain")) ]]] }

def auctionGame : GameDef :=
  { tinySettlers with
    name := "Auction"
    resources := [⟨"grain", 200⟩, ⟨"timber", 24⟩, ⟨"brick", 24⟩, ⟨"wool", 200⟩]
    diceCount := 2
    diceSides := 6
    foundingLaws := [auctionIncome, auctionLaw] }

theorem auctionGame_valid : auctionGame.Valid := by decide +kernel

/-- Setup is skipped. Rolls of 10 and 5 pay seats 0 and 1, and the treasury has 8 grain. These are the
events up to seat 1's turn, with seat 0 having bid `a`, and then seat 1 bidding `b`. -/
def auctionEvents (a b : Nat) : List Event :=
  List.replicate 4 .forceEndTurn ++
    [.move 0 (.declare "grain" a), .move 0 .endTurn, .move 1 (.declare "grain" b)]

/-- The auction really settles. Seat 0 bids 5 and seat 1 bids 3. Seat 0 pays 5 wool and gets 8 grain. The
last entries are the next roll's income. So a declaration changes what a law does. -/
theorem an_auction_settles :
    ∃ s s', Reachable auctionGame s ∧ Engine.step auctionGame s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.player 0, .treasury, "wool", 5, .lawEffect⟩,
        ⟨.treasury, .player 0, "grain", 8, .lawEffect⟩,
        ⟨.bank, .player 0, "wool", 3, .lawEffect⟩, ⟨.bank, .treasury, "grain", 4, .lawEffect⟩] :=
  real_step (seats := 2) (serverSeed := 42) (nonces := [2]) (events := auctionEvents 5 3)
    auctionGame_valid (by decide) (by decide) (by decide +kernel)

/-- The loser getting the grain is rejected. -/
theorem wrong_auction_winner_is_rejected :
    stepEntries auctionGame 2 42 [2] (auctionEvents 5 3) .forceEndTurn ≠
      some [⟨.player 1, .treasury, "wool", 3, .lawEffect⟩,
        ⟨.treasury, .player 1, "grain", 8, .lawEffect⟩,
        ⟨.bank, .player 0, "wool", 3, .lawEffect⟩, ⟨.bank, .treasury, "grain", 4, .lawEffect⟩] := by
  decide +kernel

/-- A tie is neutral. Both seats bid 5, both pay, and each gets half the treasury's grain. -/
theorem an_auction_tie_is_shared :
    ∃ s s', Reachable auctionGame s ∧ Engine.step auctionGame s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.player 0, .treasury, "wool", 5, .lawEffect⟩,
        ⟨.treasury, .player 0, "grain", 4, .lawEffect⟩,
        ⟨.player 1, .treasury, "wool", 5, .lawEffect⟩,
        ⟨.treasury, .player 1, "grain", 4, .lawEffect⟩,
        ⟨.bank, .player 0, "wool", 3, .lawEffect⟩, ⟨.bank, .treasury, "grain", 4, .lawEffect⟩] :=
  real_step (seats := 2) (serverSeed := 42) (nonces := [2]) (events := auctionEvents 5 5)
    auctionGame_valid (by decide) (by decide) (by decide +kernel)

/-- A bid the seat cannot pay does not count. Seat 1 bids 100 and holds 5 wool, so seat 0's bid of 5 wins. -/
theorem a_bid_nobody_can_pay_does_not_count :
    ∃ s s', Reachable auctionGame s ∧ Engine.step auctionGame s .forceEndTurn = .ok s' ∧
      newEntries s s' = [⟨.player 0, .treasury, "wool", 5, .lawEffect⟩,
        ⟨.treasury, .player 0, "grain", 8, .lawEffect⟩,
        ⟨.bank, .player 0, "wool", 3, .lawEffect⟩, ⟨.bank, .treasury, "grain", 4, .lawEffect⟩] :=
  real_step (seats := 2) (serverSeed := 42) (nonces := [2]) (events := auctionEvents 5 100)
    auctionGame_valid (by decide) (by decide) (by decide +kernel)

/-- With no declaration, the auction moves nothing. Only the next roll's income is written. -/
example : stepEntries auctionGame 2 42 [2] (List.replicate 5 .forceEndTurn) .forceEndTurn =
    some [⟨.bank, .player 0, "wool", 3, .lawEffect⟩, ⟨.bank, .treasury, "grain", 4, .lawEffect⟩] := by
  decide +kernel

/-- What this event does after these events: `none` if the engine rejects it. -/
def declaredAfter (events : List Event) (q : Seat) (r : Res) : Option Nat :=
  match Engine.replay auctionGame 2 42 [2] events with
  | .ok s => some (s.declared q r)
  | .error _ => none

/-- A declaration writes no entries, and it changes that seat's number. -/
example : stepEntries auctionGame 2 42 [2] (List.replicate 4 .forceEndTurn)
    (.move 0 (.declare "grain" 5)) = some [] := by decide +kernel
example : declaredAfter (auctionEvents 5 3) 0 "grain" = some 5 := by decide +kernel
example : declaredAfter (auctionEvents 5 3) 1 "grain" = some 3 := by decide +kernel

/-- Declarations clear when the round ends. They clear after the round's end laws have read them, and
before the roll that starts the next round. -/
example : declaredAfter (auctionEvents 5 3 ++ [.forceEndTurn]) 0 "grain" = some 0 := by decide +kernel
example : declaredAfter (auctionEvents 5 3 ++ [.forceEndTurn]) 1 "grain" = some 0 := by decide +kernel

/-- A roll that starts a new round reads the numbers as cleared. -/
example : (Expr.declared .actor (.lit "grain")).eval
    (({ initialState auctionGame 2 42 [2] with
        phase := .actions, turnIndex := 1, declared := fun _ _ => 5 } : State auctionGame).atRoll)
    { actor := some 0 } = 0 := by decide +kernel

/-- A seat cannot declare out of turn, for an unknown resource, or over the limit. -/
theorem a_foreign_declaration_is_rejected :
    stepEntries auctionGame 2 42 [2] (List.replicate 4 .forceEndTurn) (.move 1 (.declare "grain" 5)) = none := by
  decide +kernel

theorem an_unknown_resource_is_rejected :
    stepEntries auctionGame 2 42 [2] (List.replicate 4 .forceEndTurn) (.move 0 (.declare "gold" 5)) = none := by
  decide +kernel

theorem a_declaration_over_the_limit_is_rejected :
    stepEntries auctionGame 2 42 [2] (List.replicate 4 .forceEndTurn)
      (.move 0 (.declare "grain" (maxDeclared + 1))) = none := by
  decide +kernel

/-- A step that takes a declaration from seat 0 and also changes seat 1's number breaks `DeclarationsKept`:
it forges a number in another seat's name. -/
theorem a_forged_declaration_is_rejected :
    ¬ DeclarationsKept (({ initialState auctionGame 2 42 [2] with phase := .actions }) : State auctionGame)
      ({ initialState auctionGame 2 42 [2] with
          phase := .actions, declared := fun q _ => if q = 1 then 9 else 0 })
      (.move 0 (.declare "grain" 5)) := by
  intro h
  obtain ⟨_, _, _, _, hk⟩ := h.1 0 "grain" 5 rfl
  have h9 : (9 : Nat) = 0 := hk 1 "grain"
  exact absurd h9 (by decide)

/-- A number that stays after a round's end breaks it too. -/
theorem a_number_that_stays_is_rejected :
    ¬ DeclarationsKept (({ initialState auctionGame 2 42 [2] with phase := .actions, turnIndex := 1 }) : State auctionGame)
      ({ initialState auctionGame 2 42 [2] with declared := fun _ _ => 9 })
      .forceEndTurn := by
  intro h
  have h9 : (9 : Nat) = 0 := h.2.1 trivial (by decide +kernel) 0 "grain"
  exact absurd h9 (by decide)

/-! ## Proposing costs nothing -/

/-- A law that takes everything every seat has been paid, each round. -/
def drainLaw : Law :=
  { title := "Drain"
    clauses := [.onRoundEnd [.forEach .yes
      [.transfer .each .bank (.lit "grain") (.holding .each (.lit "grain"))]]] }

/-- A founding law drains everyone, and nobody holds anything. The law that repeals it is still accepted,
and it writes no entry. A fee would have made this law impossible to repeal. -/
theorem a_ruined_seat_can_ask_for_a_repeal :
    ∃ s s', Reachable ({ giftGame drainLaw with foundingLaws := [drainLaw] } : GameDef) s ∧
      Engine.step ({ giftGame drainLaw with foundingLaws := [drainLaw] } : GameDef) s
        (.propose 0 (.law { title := "Repeal", clauses := [.repeal 0] })) = .ok s' ∧
      newEntries s s' = [] :=
  real_step (seats := 2) (serverSeed := 42) (nonces := [2]) (events := List.replicate 4 .forceEndTurn)
    (by decide +kernel) (by decide) (by decide) (by decide +kernel)

/-- A step that charges a seat for proposing a law is rejected. V lists every way money can leave a seat,
and a proposal is not on it. -/
theorem charging_to_propose_is_rejected :
    ¬ MoneyLeavesSeatOnlyFor sevenGame sevenGame (.propose 0 (.law luckySeven))
      ⟨.player 0, .bank, "grain", 1, .cost⟩ := by
  intro h
  rcases h 0 rfl with ⟨_, _, _, he, _⟩ | ⟨hr, _⟩ | ⟨_, _, hf, _⟩ | ⟨hr, _⟩
  · cases he
  · cases hr
  · cases hf
  · cases hr

/-! ## What a resource is worth

A law can say that a resource is worth points. Only a seat's own account counts. -/

/-- Grain is worth a point, so holding it can win a game. -/
def grainCounts : Law := { title := "Grain counts", clauses := [.setWorth "grain" 1] }

/-- Tiny Settlers with `rollerGift` and grain worth a point, and a target of 15 points. -/
def worthGame : GameDef :=
  { tinySettlers with
    name := "Worth"
    diceCount := 2
    diceSides := 6
    targetPoints := 15
    foundingLaws := [rollerGift, grainCounts] }

theorem worthGame_valid : worthGame.Valid := by decide +kernel

/-- What a state looks like after these events. -/
def after2 (G : GameDef) (nonce : UInt64) (events : List Event) : Option (State G) :=
  (Engine.replay G 2 42 [nonce] events).toOption

/-- A real game. The first three rolls pay seat 0 10 grain, seat 1 5 grain and seat 0 3 grain. So seat 0
has 13 points. A resource moves the score. -/
example : ((after2 worthGame 2 (List.replicate 6 .forceEndTurn)).map (·.pointsOf 0)) = some 13 := by
  decide +kernel

/-- Later rolls take seat 0 past the target at a turn change, and the game goes on: a turn change does not
look for a winner. -/
def worthEvents : List Event := List.replicate 8 .forceEndTurn

/-- At the end of those events, a seat is at the target and the game runs. -/
example : ((after2 worthGame 2 worthEvents).map fun s =>
    (s.phase, decide (15 ≤ s.pointsOf 0))) = some (.actions, true) := by decide +kernel

/-- Any move or vote then ends the game, even one by another seat that moves nothing. So the winner is
named the next time anyone acts. -/
theorem a_seat_at_the_target_wins_at_the_next_move :
    ∃ s s', Reachable worthGame s ∧ Engine.step worthGame s (.move 0 (.declare "grain" 0)) = .ok s' ∧
      s.phase = .actions ∧ 15 ≤ s.pointsOf 0 ∧ s'.phase = .ended ∧ s'.winner = some 0 := by
  have hc : (match Engine.replay worthGame 2 42 [2] worthEvents with
      | .error _ => false
      | .ok s =>
        match Engine.step worthGame s (.move 0 (.declare "grain" 0)) with
        | .error _ => false
        | .ok s' => s.phase == .actions && decide (15 ≤ s.pointsOf 0) && s'.phase == .ended &&
            s'.winner == some 0) = true := by decide +kernel
  cases hr : Engine.replay worthGame 2 42 [2] worthEvents with
  | error m => rw [hr] at hc; simp at hc
  | ok s =>
    rw [hr] at hc
    cases hs : Engine.step worthGame s (.move 0 (.declare "grain" 0)) with
    | error m => simp [hs] at hc
    | ok s' =>
      simp only [hs, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      exact ⟨s, s', ((X_what_you_vote_on_is_what_runs worthGame worthGame_valid).1 s).mpr
        ⟨2, 42, [2], _, by decide, by decide, hr⟩, hs, h1, h2, h3, h4⟩

/-- A move that does not end the game with a seat at the target is rejected: that is a false end. -/
theorem no_win_at_the_target_is_rejected {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hl : LooksForWinner e) (hp : p ∈ s'.turnOrder) (ht : G.targetPoints ≤ s'.pointsOf p) :
    s'.phase = .ended :=
  Proofs.looks_for_winner h hl ⟨p, hp, ht⟩

/-- A deposit does not count. These books give seat 0 3 grain in a deposit and none in hand, so seat 0 has
no points from them. -/
example : (({ initialState worthGame 2 42 [2] with
      books := fun a r => match a, r with
        | .deposit 0 0, "grain" => 3
        | _, _ => 0 } : State worthGame)).pointsOf 0 = 0 := by decide +kernel

/-- A law that names no real resource is refused. -/
theorem worth_of_nothing_is_rejected :
    "there is no resource called gold" ∈ lawProblems tinySettlers (initialState tinySettlers 2 42 [3])
      { title := "Gold", clauses := [.setWorth "gold" 1] } := by decide +kernel

/-- Repealing the law takes the worth away. -/
example : (({ initialState worthGame 2 42 [2] with
      laws := [] ,
      books := fun a r => match a, r with
        | .player 0, "grain" => 3
        | _, _ => 0 } : State worthGame)).pointsOf 0 = 0 := by decide +kernel

/-! ## Moving pieces

A law can take a seat's newest piece of a kind, at a round's end or on a roll. To the bank, it is destroyed.
To a seat, it is seized. A seat keeps its last piece. -/

/-- A list of pieces: seat 0 has a settlement with a mill on it and another settlement, and seat 1 has one. -/
def movePieces : List Piece :=
  [⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩, ⟨0, "settlement", .spot 3⟩, ⟨1, "settlement", .spot 6⟩]

/-- Rules with a mill that attaches to a settlement, with a limit of 1 for each. -/
def moveRules : Rules :=
  { pieces := [ { name := "settlement", cost := [], points := 1, placement := .spot, yield := 1, limit := 2 }
              , { name := "mill", cost := [], points := 1, placement := .attach "settlement", yield := 1, limit := 1 } ]
    bankRate := 4, worth := [] }

/-- The bank destroys the newest settlement, and the older one stays. -/
example : applyOrder moveRules movePieces ⟨0, none, "settlement"⟩ =
    [⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩, ⟨1, "settlement", .spot 6⟩] := by decide +kernel

/-- A seizure keeps the piece where it is, and changes its owner. -/
example : applyOrder moveRules movePieces ⟨0, some 1, "settlement"⟩ =
    [⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩, ⟨1, "settlement", .spot 3⟩, ⟨1, "settlement", .spot 6⟩] := by
  decide +kernel

/-- What sits on a piece goes with it, and the seat's other settlement stays. -/
example : applyOrder moveRules [⟨0, "settlement", .spot 3⟩, ⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩]
      ⟨0, none, "settlement"⟩ = [⟨0, "settlement", .spot 3⟩] := by decide +kernel

/-- A seat at its limit cannot receive a piece, so it is destroyed. -/
example : applyOrder { moveRules with pieces := [ { name := "settlement", cost := [], points := 1, placement := .spot, yield := 1, limit := 1 } ] }
      movePieces ⟨0, some 1, "settlement"⟩ =
    [⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩, ⟨1, "settlement", .spot 6⟩] := by decide +kernel

/-- A seat keeps its last piece: the order does nothing. Taking the settlement takes the mill on it, and that
is all the seat has. -/
example : applyOrder moveRules [⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩] ⟨0, none, "settlement"⟩ =
    [⟨0, "settlement", .spot 0⟩, ⟨0, "mill", .spot 0⟩] := by decide +kernel

/-- A step that takes a seat's last piece is rejected. -/
theorem taking_the_last_piece_is_rejected :
    ¬ SeatsKeepAPiece
      ({ initialState tinySettlers 2 42 [2] with pieces := [⟨0, "settlement", .spot 0⟩] } : State tinySettlers)
      (initialState tinySettlers 2 42 [2]) := by
  intro h
  obtain ⟨_, hx, _⟩ := h 0 ⟨⟨0, "settlement", .spot 0⟩, by simp, rfl⟩
  cases hx

/-- A piece that vanishes at a turn change with no law asking for it is rejected. -/
theorem a_piece_vanishing_with_no_law_is_rejected :
    ¬ PieceLeavesOnlyFor
      ({ initialState tinySettlers 2 42 [2] with pieces := [⟨0, "settlement", .spot 0⟩] } : State tinySettlers)
      (initialState tinySettlers 2 42 [2]) .forceEndTurn := by
  intro h
  rcases h ⟨0, "settlement", .spot 0⟩ (by simp) (by simp [initialState]) with ⟨_, _, he⟩ | ⟨_, L, hL, _⟩ | _
  · cases he
  · cases hL
  · obtain ⟨_, ⟨_, _, _, he, _⟩, _⟩ := ‹∃ L, LawPasses _ _ L ∧ _›
    cases he

/-- A law that names a build or a harvest is refused, so commandment VII stays as it is. -/
theorem moving_a_piece_on_a_build_is_rejected :
    "a law can move a piece only at a round's end or on a roll" ∈
      lawProblems tinySettlers (initialState tinySettlers 2 42 [2])
        { title := "x", clauses := [.onBuild "road" [.movePiece .actor .bank "settlement"]] } := by
  decide +kernel

theorem moving_a_piece_on_a_harvest_is_rejected :
    "a law can move a piece only at a round's end or on a roll" ∈
      lawProblems tinySettlers (initialState tinySettlers 2 42 [2])
        { title := "x", clauses := [.onHarvest [.movePiece .actor .bank "settlement"]] } := by
  decide +kernel

/-- A roll law takes the roller's newest road when the dice show anything. So in a real game the board changes. -/
def roadTax : Law :=
  { title := "Road tax", clauses := [.onRoll [.movePiece .actor .bank "road"]] }

def roadGame : GameDef :=
  { tinySettlers with name := "Road tax", diceCount := 2, diceSides := 6, foundingLaws := [roadTax] }

theorem roadGame_valid : roadGame.Valid := by decide +kernel

/-- Each seat places a settlement and a road, twice. On the roll that starts seat 0's turn, it loses its newest
road and keeps everything else. -/
def roadEvents : List Event :=
  [ .move 0 (.place "settlement" (.spot 0)), .move 0 (.place "road" (.link (0, 1))), .move 0 .endTurn
  , .move 1 (.place "settlement" (.spot 5)), .move 1 (.place "road" (.link (5, 6))), .move 1 .endTurn
  , .move 1 (.place "settlement" (.spot 8)), .move 1 (.place "road" (.link (8, 9))), .move 1 .endTurn
  , .move 0 (.place "settlement" (.spot 3)), .move 0 (.place "road" (.link (3, 4))) ]

/-- A real game. After the last setup turn ends, seat 0 has lost the road it placed last. -/
theorem a_law_really_takes_a_piece :
    ∃ s s', Reachable roadGame s ∧ Engine.step roadGame s (.move 0 .endTurn) = .ok s' ∧
      ⟨0, "road", .link (3, 4)⟩ ∈ s.pieces ∧ ⟨0, "road", .link (3, 4)⟩ ∉ s'.pieces ∧
      ⟨0, "road", .link (0, 1)⟩ ∈ s'.pieces := by
  have hc : (match Engine.replay roadGame 2 42 [2] roadEvents with
      | .error _ => false
      | .ok s =>
        match Engine.step roadGame s (.move 0 .endTurn) with
        | .error _ => false
        | .ok s' => s.pieces.contains ⟨0, "road", .link (3, 4)⟩ && !s'.pieces.contains ⟨0, "road", .link (3, 4)⟩ &&
            s'.pieces.contains ⟨0, "road", .link (0, 1)⟩) = true := by decide +kernel
  cases hr : Engine.replay roadGame 2 42 [2] roadEvents with
  | error m => rw [hr] at hc; simp at hc
  | ok s =>
    rw [hr] at hc
    cases hs : Engine.step roadGame s (.move 0 .endTurn) with
    | error m => simp [hs] at hc
    | ok s' =>
      simp only [hs, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hc
      obtain ⟨⟨h1, h2⟩, h3⟩ := hc
      exact ⟨s, s', ((X_what_you_vote_on_is_what_runs roadGame roadGame_valid).1 s).mpr
        ⟨2, 42, [2], _, by decide, by decide, hr⟩, hs, h1,
        (fun hm => by rw [List.contains_iff_mem.mpr hm] at h2; cases h2), h3⟩

/-! ## Decrees: a clause that fires once

A `now` clause runs once, the moment its law passes. Nobody is the actor. A law of only such clauses does not
join the laws in force and takes no slot. -/

/-- The bank gives every seat 2 grain, once. -/
def giftOnce : Law :=
  { title := "One gift", clauses := [.now [.forEach .yes [.transfer .bank .each (.lit "grain") (.lit 2)]]] }

/-- A law with a `now` part and a part that stays: every seat gets 2 grain now, and a road costs 1 brick. -/
def giftAndRule : Law :=
  { giftOnce with clauses := giftOnce.clauses ++ [.setCost "road" [("brick", 1)]] }

def decreeEvents (L : Law) : List Event :=
  List.replicate 4 .forceEndTurn ++ [.propose 0 (.law L), .vote 0 0 true]

/-- The deciding vote moves the money, in a real game, and writes exactly the decree. -/
theorem a_decree_moves_money :
    ∃ s s', Reachable tinySettlers s ∧ Engine.step tinySettlers s (.vote 1 0 true) = .ok s' ∧
      newEntries s s' = [⟨.bank, .player 0, "grain", 2, .lawEffect⟩, ⟨.bank, .player 1, "grain", 2, .lawEffect⟩] :=
  real_step (seats := 2) (serverSeed := 42) (nonces := [25283273]) (events := decreeEvents giftOnce)
    tinySettlers_valid (by decide) (by decide) (by decide +kernel)

/-- A vote that pays only the seat that cast it is rejected. -/
theorem a_decree_that_rewards_the_voter_is_rejected :
    stepEntries tinySettlers 2 42 [25283273] (decreeEvents giftOnce) (.vote 1 0 true) ≠
      some [⟨.bank, .player 1, "grain", 4, .lawEffect⟩] := by decide +kernel

/-- The law takes no slot among the laws in force. A law with a part that stays does. -/
example : ((after2 tinySettlers 25283273 (decreeEvents giftOnce ++ [.vote 1 0 true])).map (·.laws.length)) = some 0 := by
  decide +kernel
example : ((after2 tinySettlers 25283273 (decreeEvents giftAndRule ++ [.vote 1 0 true])).map (·.laws.length)) = some 1 := by
  decide +kernel

/-- It fires once. The law in force does nothing at later turn changes. -/
example : stepEntries tinySettlers 2 42 [25283273] (decreeEvents giftAndRule ++ [.vote 1 0 true]) (.move 0 .endTurn) =
    some [] := by decide +kernel

/-- A decree cannot name the deciding voter. -/
theorem a_decree_naming_the_actor_is_rejected :
    "a rule that acts once has no acting player, so it cannot reward one" ∈
      lawProblems tinySettlers (initialState tinySettlers 2 42 [2])
        { title := "x", clauses := [.now [.when (.lt (.lit 0) (.points .actor)) [.transfer .bank .treasury (.lit "grain") (.lit 1)]]] } := by
  decide +kernel

/-- A founding law cannot be a decree. -/
theorem a_founding_decree_is_invalid :
    ¬ ({ tinySettlers with foundingLaws := [giftOnce] } : GameDef).Valid := by decide +kernel

/-! ## Ending the game by law -/

/-- A law that ends the game. -/
def callIt : Law := { title := "Call it", clauses := [.endGame] }

/-- The events up to the vote that decides it. -/
def callEvents : List Event :=
  List.replicate 4 .forceEndTurn ++ [.propose 0 (.law callIt), .vote 0 0 true]

/-- In a real game, the deciding vote ends the game. A seat has the most points, or the earliest of those tied. -/
theorem a_majority_can_end_the_game :
    ∃ s s', Reachable tinySettlers s ∧ Engine.step tinySettlers s (.vote 1 0 true) = .ok s' ∧
      s.phase = .actions ∧ s'.phase = .ended ∧ s'.winner = some 0 ∧ MajorityEndedTheGame s' := by
  have hc : (match Engine.replay tinySettlers 2 42 [25283273] callEvents with
      | .error _ => false
      | .ok s =>
        match Engine.step tinySettlers s (.vote 1 0 true) with
        | .error _ => false
        | .ok s' => s.phase == .actions && s'.phase == .ended && s'.winner == some 0 && s'.lawEnds) = true := by
    decide +kernel
  cases hr : Engine.replay tinySettlers 2 42 [25283273] callEvents with
  | error m => rw [hr] at hc; simp at hc
  | ok s =>
    rw [hr] at hc
    cases hs : Engine.step tinySettlers s (.vote 1 0 true) with
    | error m => simp [hs] at hc
    | ok s' =>
      simp only [hs, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      obtain ⟨x, hx, hl⟩ := List.any_eq_true.mp h4
      exact ⟨s, s', ((X_what_you_vote_on_is_what_runs tinySettlers tinySettlers_valid).1 s).mpr
        ⟨2, 42, [25283273], _, by decide, by decide, hr⟩, hs, h1, h2, h3, x, hx, hl⟩

/-- One yes of two seats is not a majority, so the game goes on. -/
example : ((after2 tinySettlers 25283273 callEvents).map (·.phase)) = some .actions := by decide +kernel

/-- A step that ends the game when no seat is at the target, no rounds ran out and no law says so is
rejected. -/
theorem an_unearned_end_is_rejected :
    ¬ PhaseChangesOnlyByTurnOrWin (initialState tinySettlers 2 42 [2])
      ({ initialState tinySettlers 2 42 [2] with phase := .ended }) (.move 0 (.bankTrade "grain" "wool")) := by
  intro h
  rcases h (by simp [EndsTurn]) with hp | ⟨_, ⟨p, hp, ht⟩ | ⟨x, hx, _⟩⟩
  · cases hp
  · have hzero : ({ initialState tinySettlers 2 42 [2] with phase := .ended } : State tinySettlers).pointsOf p = 0 := by
      have hp' : p ∈ List.range 2 := hp
      have hlt : p < 2 := List.mem_range.mp hp'
      have : p = 0 ∨ p = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hlt)
      rcases this with rfl | rfl <;> decide +kernel
    rw [hzero] at ht
    exact absurd ht (by decide)
  · cases hx

/-- A founding law cannot end the game. -/
theorem a_founding_end_is_invalid : ¬ ({ tinySettlers with foundingLaws := [callIt] } : GameDef).Valid := by
  decide +kernel

/-! ## Bank trades and setup placements

`bank_trades_and_setup_are_exact` runs on real games with every hypothesis met, and its named parts say
no to bad steps. The rejected states are built by hand, like those above. -/

/-- A step after these events from a new game is accepted, and this holds of it. -/
def stepPasses {G : GameDef} (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64)
    (events : List Event) (e : Event) (P : State G → State G → Prop)
    [∀ s s', Decidable (P s s')] : Bool :=
  match Engine.replay G seats serverSeed nonces events with
  | .error _ => false
  | .ok s =>
    match Engine.step G s e with
    | .error _ => false
    | .ok s' => decide (P s s')

/-- If `stepPasses` says so, a reachable state really takes that step. -/
theorem real_tested_step {G : GameDef} (hG : G.Valid) {seats : Nat} {serverSeed : UInt64}
    {nonces : List UInt64} {events : List Event} {e : Event} {P : State G → State G → Prop}
    [∀ s s', Decidable (P s s')] (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats)
    (hc : stepPasses seats serverSeed nonces events e P = true) :
    ∃ s s', Reachable G s ∧ Engine.step G s e = .ok s' ∧ P s s' := by
  unfold stepPasses at hc
  split at hc
  · cases hc
  · rename_i s hr
    split at hc
    · cases hc
    · rename_i s' hs
      exact ⟨s, s', ((X_what_you_vote_on_is_what_runs G hG).1 s).mpr
        ⟨seats, serverSeed, nonces, events, h1, h2, hr⟩, hs, of_decide_eq_true hc⟩

/-- Tiny Settlers with `rollerGift`, so the seats hold grain early. -/
def tradeGame : GameDef :=
  { tinySettlers with
    name := "Trade"
    diceCount := 2
    diceSides := 6
    foundingLaws := [rollerGift] }

theorem tradeGame_valid : tradeGame.Valid := by decide +kernel

/-- A real bank trade, with every hypothesis met. It is seat 1's turn and it holds 5 grain. It pays the rate
of 4 grain and gets 1 timber. -/
theorem a_bank_trade_is_exact :
    ∃ s s', Reachable tradeGame s ∧
      Engine.step tradeGame s (.move 1 (.bankTrade "grain" "timber")) = .ok s' ∧
      BankTradeIsAllowed s 1 "grain" "timber" ∧
      BankTradeIsExact s s' 1 "grain" "timber" ∧
      s'.phase = .actions ∧
      newEntries s s' = [⟨.player 1, .bank, "grain", 4, .trade⟩, ⟨.bank, .player 1, "timber", 1, .trade⟩] ∧
      s.balance (.player 1) "grain" = 5 ∧ s'.balance (.player 1) "grain" = 1 ∧
      s.balance (.player 1) "timber" = 0 ∧ s'.balance (.player 1) "timber" = 1 := by
  obtain ⟨s, s', hr, hstep, hP⟩ := real_tested_step
    (G := tradeGame) (P := fun s s' => s'.phase = .actions ∧
      newEntries s s' = [⟨.player 1, .bank, "grain", 4, .trade⟩, ⟨.bank, .player 1, "timber", 1, .trade⟩] ∧
      s.balance (.player 1) "grain" = 5 ∧ s'.balance (.player 1) "grain" = 1 ∧
      s.balance (.player 1) "timber" = 0 ∧ s'.balance (.player 1) "timber" = 1)
    (seats := 2) (serverSeed := 42) (nonces := [2]) (events := List.replicate 5 .forceEndTurn)
    (e := .move 1 (.bankTrade "grain" "timber"))
    tradeGame_valid (by decide) (by decide) (by decide +kernel)
  obtain ⟨_, htrade, _⟩ := bank_trades_and_setup_are_exact tradeGame tradeGame_valid s hr 1
  exact ⟨s, s', hr, hstep, (htrade _ _).1.mp ⟨s', hstep⟩, (htrade _ _).2 s' hstep, hP⟩

/-- Timber is worth a point. -/
def timberCounts : Law := { title := "Timber counts", clauses := [.setWorth "timber" 1] }

/-- `tradeGame`, where 1 timber reaches the target. -/
def timberRace : GameDef :=
  { tradeGame with
    name := "Timber race"
    targetPoints := 1
    foundingLaws := [rollerGift, timberCounts] }

theorem timberRace_valid : timberRace.Valid := by decide +kernel

/-- Seats 0 and 1 sign a deal, and seat 1 puts down 1 grain. -/
def smallDeal : Deal :=
  { title := "Pact", signers := [0, 1], rounds := 1, exitNotice := 0
    deposits := [(1, "grain", 1)], terms := [] }

/-- A real bank trade that ends the game, with a deal running. The timber puts seat 1 at the target. So the
deal refunds its 1 grain after the trade, and that grain is seat 1's. Seat 1 had 4 grain, paid 4 and got 1 back. -/
theorem a_bank_trade_can_end_the_game :
    ∃ s s', Reachable timberRace s ∧
      Engine.step timberRace s (.move 1 (.bankTrade "grain" "timber")) = .ok s' ∧
      BankTradeIsExact s s' 1 "grain" "timber" ∧
      s'.phase = .ended ∧ s'.winner = some 1 ∧
      newEntries s s' =
        [⟨.player 1, .bank, "grain", 4, .trade⟩, ⟨.bank, .player 1, "timber", 1, .trade⟩,
         ⟨.deposit 0 1, .player 1, "grain", 1, .refund⟩] ∧
      refundsTo s 1 "grain" = 1 ∧
      s.balance (.player 1) "grain" = 4 ∧ s'.balance (.player 1) "grain" = 1 := by
  obtain ⟨s, s', hr, hstep, hP⟩ := real_tested_step
    (G := timberRace) (P := fun s s' => s'.phase = .ended ∧ s'.winner = some 1 ∧
      newEntries s s' =
        [⟨.player 1, .bank, "grain", 4, .trade⟩, ⟨.bank, .player 1, "timber", 1, .trade⟩,
         ⟨.deposit 0 1, .player 1, "grain", 1, .refund⟩] ∧
      refundsTo s 1 "grain" = 1 ∧
      s.balance (.player 1) "grain" = 4 ∧ s'.balance (.player 1) "grain" = 1)
    (seats := 2) (serverSeed := 42) (nonces := [2])
    (events := List.replicate 5 .forceEndTurn ++ [.propose 1 (.deal smallDeal), .sign 0 2, .sign 1 2])
    (e := .move 1 (.bankTrade "grain" "timber"))
    timberRace_valid (by decide) (by decide) (by decide +kernel)
  obtain ⟨_, htrade, _⟩ := bank_trades_and_setup_are_exact timberRace timberRace_valid s hr 1
  exact ⟨s, s', hr, hstep, (htrade _ _).2 s' hstep, hP⟩

/-- A real setup placement, with every hypothesis met. Seat 0 places its first settlement. The piece is on
the board, no entry is written, and the turn stays with seat 0, which has now used 1 action. -/
theorem a_setup_placement_is_exact :
    ∃ s s', Reachable tinySettlers s ∧ s.phase = .setup ∧
      Engine.step tinySettlers s (.move 0 (.place "settlement" (.spot 0))) = .ok s' ∧
      SetupPlacementIsAllowed s 0 "settlement" (.spot 0) ∧
      SetupPlacementIsExact s s' 0 "settlement" (.spot 0) ∧
      s'.phase = .setup ∧ s'.pieces = [⟨0, "settlement", .spot 0⟩] ∧ newEntries s s' = [] ∧
      s'.actionsThisTurn 0 = 1 ∧ s'.turnIndex = 0 := by
  obtain ⟨s, s', hr, hstep, hP⟩ := real_tested_step
    (G := tinySettlers) (P := fun s s' => s.phase = .setup ∧ s'.phase = .setup ∧
      s'.pieces = [⟨0, "settlement", .spot 0⟩] ∧ newEntries s s' = [] ∧
      s'.actionsThisTurn 0 = 1 ∧ s'.turnIndex = 0)
    (seats := 2) (serverSeed := 42) (nonces := [25283273]) (events := [])
    (e := .move 0 (.place "settlement" (.spot 0)))
    tinySettlers_valid (by decide) (by decide) (by decide +kernel)
  obtain ⟨_, _, hsetup⟩ := bank_trades_and_setup_are_exact tinySettlers tinySettlers_valid s hr 0
  have hph := hP.1
  exact ⟨s, s', hr, hph, hstep, (hsetup _ _ hph).1.mp ⟨s', hstep⟩, (hsetup _ _ hph).2 s' hstep, hP.2⟩

/-- Tiny Settlers with a target of 1 point. -/
def quickGame : GameDef := { tinySettlers with name := "Quick", targetPoints := 1 }

theorem quickGame_valid : quickGame.Valid := by decide +kernel

/-- A setup placement can end the game: the first settlement reaches this game's target. It still writes no
entries. -/
theorem a_setup_placement_can_end_the_game :
    ∃ s s', Reachable quickGame s ∧ s.phase = .setup ∧
      Engine.step quickGame s (.move 0 (.place "settlement" (.spot 0))) = .ok s' ∧
      SetupPlacementIsExact s s' 0 "settlement" (.spot 0) ∧
      s'.phase = .ended ∧ s'.winner = some 0 ∧ newEntries s s' = [] := by
  obtain ⟨s, s', hr, hstep, hP⟩ := real_tested_step
    (G := quickGame) (P := fun s s' => s.phase = .setup ∧ s'.phase = .ended ∧ s'.winner = some 0 ∧
      newEntries s s' = [])
    (seats := 2) (serverSeed := 42) (nonces := [25283273]) (events := [])
    (e := .move 0 (.place "settlement" (.spot 0)))
    quickGame_valid (by decide) (by decide) (by decide +kernel)
  obtain ⟨_, _, hsetup⟩ := bank_trades_and_setup_are_exact quickGame quickGame_valid s hr 0
  exact ⟨s, s', hr, hP.1, hstep, (hsetup _ _ hP.1).2 s' hstep, hP.2⟩

/-- Tiny Settlers whose setup list has a settlement and then a city. -/
def upgradeSetup : GameDef :=
  { tinySettlers with name := "Upgrade setup", setupPieces := ["settlement", "city"] }

theorem upgradeSetup_valid : upgradeSetup.Valid := by decide +kernel

/-- The one exception to "the old pieces plus the new one". A game can list an upgrade in setup, and the
upgrade replaces the piece under it. -/
theorem a_setup_upgrade_replaces_its_piece :
    ∃ s s', Reachable upgradeSetup s ∧ s.phase = .setup ∧
      Engine.step upgradeSetup s (.move 0 (.place "city" (.spot 0))) = .ok s' ∧
      SetupPlacementIsExact s s' 0 "city" (.spot 0) ∧
      s.pieces = [⟨0, "settlement", .spot 0⟩] ∧ s'.pieces = [⟨0, "city", .spot 0⟩] := by
  obtain ⟨s, s', hr, hstep, hP⟩ := real_tested_step
    (G := upgradeSetup) (P := fun s s' => s.phase = .setup ∧
      s.pieces = [⟨0, "settlement", .spot 0⟩] ∧ s'.pieces = [⟨0, "city", .spot 0⟩])
    (seats := 2) (serverSeed := 42) (nonces := [25283273])
    (events := [.move 0 (.place "settlement" (.spot 0))])
    (e := .move 0 (.place "city" (.spot 0)))
    upgradeSetup_valid (by decide) (by decide) (by decide +kernel)
  obtain ⟨_, _, hsetup⟩ := bank_trades_and_setup_are_exact upgradeSetup upgradeSetup_valid s hr 0
  exact ⟨s, s', hr, hP.1, hstep, (hsetup _ _ hP.1).2 s' hstep, hP.2⟩

/-- A game in the actions phase. It is seat 0's turn, seat 0 holds 5 grain, and the bank holds the rest. -/
def bankGame : State tinySettlers :=
  { sampleGame with
    books := fun a r => match a, r with
      | .player 0, "grain" => 5
      | .bank, _ => 24
      | _, _ => 0 }

/-- `bankGame` after a step that writes these entries, posts them and counts the action. -/
def afterTrade (es : List Entry) : State tinySettlers :=
  { bankGame with
    books := (bankGame.books.postAll es).getD bankGame.books
    journal := es
    actionsThisTurn := countsAfter bankGame 0
    eventsApplied := 1 }

/-- Seat 0's trade of grain for brick, at this rate, for this much brick. -/
def tradeAt (rate paid : Nat) : List Entry :=
  [⟨.player 0, .bank, "grain", rate, .trade⟩, ⟨.bank, .player 0, "brick", paid, .trade⟩]

theorem afterTrade_goes_on (es : List Entry) : (afterTrade es).phase ≠ .ended := by
  simp [afterTrade, bankGame, sampleGame, initialState]

example : bankGame.bankTradeEntries 0 "grain" "brick" = tradeAt 4 1 := by decide +kernel

/-- The honest step is allowed: seat 0 pays 4 grain and gets 1 brick. -/
example : BankTradeIsExact bankGame (afterTrade (tradeAt 4 1)) 0 "grain" "brick" := by
  refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, rfl⟩, fun h => absurd h (afterTrade_goes_on _)⟩ <;> decide +kernel

/-- A bank trade takes the seat's goods and gives nothing back. This is the bug the promise is for. -/
theorem a_trade_that_pays_nothing_back_is_rejected :
    ¬ BankTradeIsExact bankGame (afterTrade [⟨.player 0, .bank, "grain", 4, .trade⟩]) 0 "grain" "brick" :=
  fun h => absurd (h.2.1 (afterTrade_goes_on _)).1 (by decide +kernel)

/-- The entries are right, but the seat's balance does not gain the brick. -/
theorem a_trade_that_only_writes_it_down_is_rejected :
    ¬ BankTradeIsExact bankGame { afterTrade (tradeAt 4 1) with books := bankGame.books } 0 "grain" "brick" :=
  fun h => absurd (h.2.1 (by simp [afterTrade, bankGame, sampleGame, initialState])).2.2.1 (by decide +kernel)

/-- A trade at a better rate than the rules say. -/
theorem a_trade_at_the_wrong_rate_is_rejected :
    ¬ BankTradeIsExact bankGame (afterTrade (tradeAt 3 1)) 0 "grain" "brick" :=
  fun h => absurd (h.2.1 (afterTrade_goes_on _)).1 (by decide +kernel)

/-- The bank pays out 2 for the price of 1. -/
theorem a_trade_that_pays_too_much_is_rejected :
    ¬ BankTradeIsExact bankGame (afterTrade (tradeAt 4 2)) 0 "grain" "brick" :=
  fun h => absurd (h.2.1 (afterTrade_goes_on _)).1 (by decide +kernel)

/-- A trade that also gives the seat a piece. -/
theorem a_trade_that_adds_a_piece_is_rejected :
    ¬ BankTradeIsExact bankGame
      { afterTrade (tradeAt 4 1) with pieces := [⟨0, "settlement", .spot 0⟩] } 0 "grain" "brick" :=
  fun h => absurd h.1 (by decide +kernel)

/-- A trade that also ends the turn. -/
theorem a_trade_that_moves_the_turn_is_rejected :
    ¬ BankTradeIsExact bankGame { afterTrade (tradeAt 4 1) with turnIndex := 1 } 0 "grain" "brick" :=
  fun h => by
    have := congrArg State.turnIndex (h.2.1 (by simp [afterTrade, bankGame, sampleGame, initialState])).2.2.2
    exact absurd this (by decide +kernel)

/-- Seat 0 can make that trade. -/
example : BankTradeIsAllowed bankGame 0 "grain" "brick" := by
  unfold BankTradeIsAllowed
  decide +kernel

/-- It is not seat 1's turn. -/
example : ¬ BankTradeIsAllowed bankGame 1 "grain" "brick" := by
  unfold BankTradeIsAllowed
  decide +kernel

/-- A seat cannot trade a resource for itself. -/
example : ¬ BankTradeIsAllowed bankGame 0 "grain" "grain" := by
  unfold BankTradeIsAllowed
  decide +kernel

/-- There is no such resource as gold. -/
example : ¬ BankTradeIsAllowed bankGame 0 "grain" "gold" := by
  unfold BankTradeIsAllowed
  decide +kernel

/-- Seat 0 holds no brick, so it cannot pay the rate in brick. -/
example : ¬ BankTradeIsAllowed bankGame 0 "brick" "grain" := by
  unfold BankTradeIsAllowed
  decide +kernel

/-- The bank has no brick left to pay. -/
example : ¬ BankTradeIsAllowed
    ({ bankGame with books := fun a r => match a, r with
        | .player 0, "grain" => 5
        | _, _ => 0 } : State tinySettlers) 0 "grain" "brick" := by
  unfold BankTradeIsAllowed
  decide +kernel

/-- A new game, in setup. -/
def setupGame : State tinySettlers := initialState tinySettlers 2 42 [25283273]

/-- `setupGame` after seat 0 places its first settlement at spot 0. -/
def afterSetup : State tinySettlers :=
  { setupGame with
    pieces := setupGame.placedPieces 0 "settlement" (.spot 0)
    actionsThisTurn := countsAfter setupGame 0
    eventsApplied := 1 }

theorem afterSetup_goes_on : afterSetup.phase ≠ .ended := by
  simp [afterSetup, setupGame, initialState]

/-- The honest step is allowed. -/
example : SetupPlacementIsExact setupGame afterSetup 0 "settlement" (.spot 0) :=
  ⟨rfl, fun _ => rfl, by decide +kernel, rfl, fun _ => rfl, fun h => absurd h afterSetup_goes_on⟩

/-- A setup placement that charges for the piece. -/
theorem a_charged_setup_piece_is_rejected :
    ¬ SetupPlacementIsExact setupGame
      { afterSetup with journal := [⟨.player 0, .bank, "grain", 1, .cost⟩] } 0 "settlement" (.spot 0) :=
  fun h => absurd h.2.2.1 (by decide +kernel)

/-- A setup placement that moves resources without writing them down. -/
theorem a_silent_setup_payment_is_rejected :
    ¬ SetupPlacementIsExact setupGame
      { afterSetup with books := fun _ _ => 0 } 0 "settlement" (.spot 0) :=
  fun h => absurd (congrFun (congrFun h.2.2.2.1 .bank) "grain") (by decide +kernel)

/-- A setup placement that adds a second piece as well. -/
theorem an_extra_setup_piece_is_rejected :
    ¬ SetupPlacementIsExact setupGame
      { afterSetup with pieces := [⟨0, "settlement", .spot 0⟩, ⟨0, "road", .link (0, 1)⟩] }
      0 "settlement" (.spot 0) :=
  fun h => absurd h.1 (by decide +kernel)

/-- A setup placement that does not count the action, so the seat could place the same piece again. -/
theorem an_uncounted_setup_piece_is_rejected :
    ¬ SetupPlacementIsExact setupGame
      { afterSetup with actionsThisTurn := fun _ => 0 } 0 "settlement" (.spot 0) :=
  fun h => by
    have := congrArg State.actionsThisTurn (h.2.2.2.2.1 (by simp [afterSetup, setupGame, initialState]))
    exact absurd (congrFun this 0) (by decide +kernel)

/-- A setup placement that also ends the turn. -/
theorem a_setup_piece_that_moves_the_turn_is_rejected :
    ¬ SetupPlacementIsExact setupGame { afterSetup with turnIndex := 1 } 0 "settlement" (.spot 0) :=
  fun h => by
    have := congrArg State.turnIndex (h.2.2.2.2.1 (by simp [afterSetup, setupGame, initialState]))
    exact absurd this (by decide +kernel)

/-- On a state in setup, `SetupPlacementIsAllowed` says yes where the engine's own check does. So the examples
below can compute their answers. -/
theorem setupAllowed_iff (s : State tinySettlers) (hPhase : s.phase = .setup) (p : Seat) (k : PieceKind)
    (loc : Loc) : SetupPlacementIsAllowed s p k loc ↔ s.canSetupPlace p k loc = true :=
  (Proofs.canSetupPlace_iff s hPhase p k loc).symm

/-- Seat 0 can place its first settlement anywhere empty. -/
example : SetupPlacementIsAllowed setupGame 0 "settlement" (.spot 0) :=
  (setupAllowed_iff _ rfl _ _ _).mpr (by decide +kernel)

/-- It is not seat 1's turn. -/
example : ¬ SetupPlacementIsAllowed setupGame 1 "settlement" (.spot 0) :=
  fun h => absurd ((setupAllowed_iff _ rfl _ _ _).mp h) (by decide +kernel)

/-- The next piece on the setup list is a settlement, not a road. -/
example : ¬ SetupPlacementIsAllowed setupGame 0 "road" (.link (0, 1)) :=
  fun h => absurd ((setupAllowed_iff _ rfl _ _ _).mp h) (by decide +kernel)

/-- There is no spot 99. -/
example : ¬ SetupPlacementIsAllowed setupGame 0 "settlement" (.spot 99) :=
  fun h => absurd ((setupAllowed_iff _ rfl _ _ _).mp h) (by decide +kernel)

/-- Spot 1 is one link from a piece at spot 0. -/
example : ¬ SetupPlacementIsAllowed
    ({ setupGame with pieces := [⟨1, "settlement", .spot 0⟩] } : State tinySettlers)
    0 "settlement" (.spot 1) :=
  fun h => absurd ((setupAllowed_iff _ rfl _ _ _).mp h) (by decide +kernel)

/-- A road needs a link that reaches one of the seat's own pieces, even in setup. -/
example : ¬ SetupPlacementIsAllowed
    ({ setupGame with actionsThisTurn := fun _ => 1 } : State tinySettlers)
    0 "road" (.link (0, 1)) :=
  fun h => absurd ((setupAllowed_iff _ rfl _ _ _).mp h) (by decide +kernel)

/-- The conditions the theorems assume can be met: this new game is reachable. -/
example : Reachable tinySettlers (initialState tinySettlers 2 42 [25283273]) :=
  .start 2 42 [25283273] (by decide) (by decide) (by simp)

end Charter
