import Charter.Proofs.RenameEngine
import Charter.Games.Tiny

/-!
# Renaming: deals, proposals, the turn change, and `step`

The last engine helpers, and then the whole of `step`: a renamed event on a renamed game has the
renamed result. This holds for every state, not only for reachable ones, and it covers the rejected
events too.
-/

namespace Charter.Renaming

open Charter Charter.Engine

variable (σ : Renaming) {G : GameDef}

/-! ## Open proposals -/

@[simp] theorem openProposal_id (p : OpenProposal) : (σ.openProposal p).id = p.id := rfl
@[simp] theorem openProposal_by (p : OpenProposal) : (σ.openProposal p).by_ = σ.to p.by_ := rfl
@[simp] theorem openProposal_body (p : OpenProposal) :
    (σ.openProposal p).body = σ.proposal p.body := rfl
@[simp] theorem openProposal_votes (p : OpenProposal) :
    (σ.openProposal p).votes = p.votes.map fun x => (σ.to x.1, x.2) := rfl
@[simp] theorem openProposal_signed (p : OpenProposal) :
    (σ.openProposal p).signed = p.signed.map σ.to := rfl

theorem openProposal?_rename (s : State G) (id : Nat) :
    (σ.state s).openProposal? id = (s.openProposal? id).map σ.openProposal := by
  simp [State.openProposal?, List.find?_map, Function.comp_def]

theorem filter_proposals (s : State G) (id : Nat) :
    (s.openProposals.map σ.openProposal).filter (·.id != id) =
      (s.openProposals.filter (·.id != id)).map σ.openProposal := by
  simp [List.filter_map, Function.comp_def]

/-! ## Deals -/

theorem canStartDeal_rename (s : State G) : (σ.state s).canStartDeal = s.canStartDeal := by
  have h : (s.deals.map σ.activeDeal).length = s.deals.length := by simp
  unfold State.canStartDeal
  show (decide _ && decide ((s.deals.map σ.activeDeal).length < maxActiveDeals)) = _
  rw [h]
  rfl

theorem depositEntries_rename (id : Nat) (d : Deal) :
    depositEntries id (σ.deal d) = (depositEntries id d).map σ.entry := by
  simp [depositEntries, Function.comp_def, entry]

theorem startDeal_rename (s : State G) (id : Nat) (d : Deal) :
    startDeal (σ.state s) id (σ.deal d) = (startDeal s id d).map σ.state := by
  unfold startDeal
  simp only [canStartDeal_rename, dealProblems_rename, state_dealsStarted, depositEntries_rename,
    record_rename]
  split
  · rfl
  · split
    · rfl
    · cases record s (depositEntries s.dealsStarted d) with
      | error m => rfl
      | ok s1 =>
        simp only [bind, Except.bind, pure, Except.pure, map_ok]
        congr 1
        state_ext
        · exact σ.filter_proposals s id
        · simp [activeDeal, deal_rounds]

theorem signBody_rename (s : State G) (seat id : Nat) :
    signBody (σ.state s) (σ.to seat) id = (signBody s seat id).map σ.state := by
  unfold signBody
  simp only [state_phase, openProposal?_rename]
  split
  · rfl
  · cases s.openProposal? id with
    | none => rfl
    | some p =>
      simp only [Option.map_some, openProposal_body]
      cases p.body with
      | law L => rfl
      | deal d =>
        have hall : ((d.signers.map σ.to).all (p.signed.map σ.to ++ [σ.to seat]).contains) =
            d.signers.all (p.signed ++ [seat]).contains := by
          rw [List.all_map]
          congr 1
          funext x
          have : p.signed.map σ.to ++ [σ.to seat] = (p.signed ++ [seat]).map σ.to := by simp
          rw [this]
          exact σ.contains_map_to _ x
        simp only [proposal, deal_signers, contains_map_to, openProposal_signed, hall]
        split
        · rfl
        · split
          · rfl
          · split
            · exact σ.startDeal_rename s id d
            · simp only [map_ok, Except.ok.injEq]
              state_ext
              simp only [state_openProposals, List.map_map, Function.comp_def]
              congr 1
              funext q
              simp only [openProposal_id]
              by_cases h : (q.id == id) = true
              · simp only [h, ↓reduceIte]
                simp [openProposal]
              · simp only [h, ↓reduceIte, Bool.false_eq_true]

theorem exitBody_rename (s : State G) (seat id : Nat) :
    exitBody (σ.state s) (σ.to seat) id = (exitBody s seat id).map σ.state := by
  unfold exitBody
  simp only [state_phase, state_deals, List.any_map, Function.comp_def, activeDeal_id,
    activeDeal_deal, deal_signers, contains_map_to]
  split
  · rfl
  · split
    · simp only [map_ok, Except.ok.injEq]
      state_ext
      simp only [state_deals, List.map_map, Function.comp_def]
      congr 1
      funext d
      simp only [activeDeal_id]
      by_cases h : (d.id == id) = true
      · simp only [h, ↓reduceIte]
        rfl
      · simp only [h, ↓reduceIte, Bool.false_eq_true]
    · rfl

/-! ## Proposals and votes -/

theorem addProposal_rename (s : State G) (seat : Seat) (body : Proposal) :
    addProposal (σ.state s) (σ.to seat) (σ.proposal body) = σ.state (addProposal s seat body) := by
  state_ext
  simp [addProposal, openProposal]

theorem proposeLaw_rename (s : State G) (seat : Seat) (L : Law) :
    proposeLaw (σ.state s) (σ.to seat) L = (proposeLaw s seat L).map σ.state := by
  unfold proposeLaw
  simp only [lawProblems_rename]
  split
  · rfl
  · exact congrArg Except.ok (σ.addProposal_rename s seat (.law L))

theorem proposeDeal_rename (s : State G) (seat : Seat) (d : Deal) :
    proposeDeal (σ.state s) (σ.to seat) (σ.deal d) = (proposeDeal s seat d).map σ.state := by
  unfold proposeDeal
  simp only [deal_signers, contains_map_to, dealProblems_rename]
  split
  · rfl
  · split
    · rfl
    · exact congrArg Except.ok (σ.addProposal_rename s seat (.deal d))

theorem proposeBody_rename (s : State G) (seat : Seat) (body : Proposal) :
    proposeBody (σ.state s) (σ.to seat) (σ.proposal body) = (proposeBody s seat body).map σ.state := by
  unfold proposeBody
  have hl : ((s.openProposals.map σ.openProposal).filter (·.by_ == σ.to seat)).length =
      (s.openProposals.filter (·.by_ == seat)).length := by
    simp [List.filter_map, Function.comp_def]
  simp only [state_phase, state_openProposals, hl]
  split
  · rfl
  · split
    · rfl
    · cases body with
      | law L => exact σ.proposeLaw_rename s seat L
      | deal d => exact σ.proposeDeal_rename s seat d

theorem yesCount_rename (p : OpenProposal) : (σ.openProposal p).yesCount = p.yesCount := by
  simp [OpenProposal.yesCount, List.filter_map, Function.comp_def]

theorem withVote_rename (p : OpenProposal) (seat : Seat) (yes : Bool) :
    (σ.openProposal p).withVote (σ.to seat) yes = σ.openProposal (p.withVote seat yes) := by
  simp [OpenProposal.withVote, openProposal]

theorem isDecidingVote_rename (s : State G) (p : OpenProposal) (seat : Seat) (yes : Bool) :
    isDecidingVote (σ.state s) (σ.openProposal p) (σ.to seat) yes = isDecidingVote s p seat yes := by
  simp only [isDecidingVote, withVote_rename, yesCount_rename, state_turnOrder, List.length_map]

theorem decideLaw_rename (s : State G) (id : Nat) (L : Law) :
    decideLaw (σ.state s) id L = σ.state (decideLaw s id L) := by
  unfold decideLaw
  simp only [lawProblems_rename, state_openProposals, state_laws, filter_proposals]
  split <;> rfl

theorem voteBody_rename (s : State G) (seat id : Nat) (yes : Bool) :
    voteBody (σ.state s) (σ.to seat) id yes = (voteBody s seat id yes).map σ.state := by
  unfold voteBody
  simp only [state_phase, openProposal?_rename]
  split
  · rfl
  · cases s.openProposal? id with
    | none => rfl
    | some p =>
      simp only [Option.map_some, openProposal_body]
      cases hb : p.body with
      | deal d => rfl
      | law L =>
        have hv : ((p.votes.map fun x => (σ.to x.1, x.2)).map (·.1)).contains (σ.to seat) =
            (p.votes.map (·.1)).contains seat := by
          have : (p.votes.map fun x => (σ.to x.1, x.2)).map (·.1) = (p.votes.map (·.1)).map σ.to := by
            simp [Function.comp_def]
          rw [this]
          exact σ.contains_map_to _ seat
        simp only [proposal, openProposal_votes, hv, isDecidingVote_rename]
        split
        · rfl
        · split
          · exact congrArg Except.ok (σ.decideLaw_rename s id L)
          · simp only [map_ok, Except.ok.injEq]
            state_ext
            simp only [state_openProposals, List.map_map, Function.comp_def]
            congr 1
            funext q
            simp only [openProposal_id]
            by_cases h : (q.id == id) = true
            · simp only [h, ↓reduceIte]
              exact σ.withVote_rename q seat yes
            · simp only [h, ↓reduceIte, Bool.false_eq_true]

/-! ## The turn change -/

theorem nextStage_rename (s : State G) : nextStage (σ.state s) = nextStage s := by
  unfold nextStage
  rw [isLastTurn_rename]
  simp only [state_turnOrder, List.length_map]
  rfl

theorem nextRoller_rename (s : State G) : (σ.state s).nextRoller = s.nextRoller.map σ.to := by
  unfold State.nextRoller
  rw [nextStage_rename]
  cases nextStage s <;> simp [state_turnOrder]

theorem atRoll_rename (s : State G) : (σ.state s).atRoll = σ.state s.atRoll := by
  unfold State.atRoll
  rw [nextStage_rename]
  split <;> rfl

theorem rollEntries_rename (s : State G) (roll : Nat) :
    rollEntries (σ.state s) roll = (rollEntries s roll).map σ.entry := by
  simp only [rollEntries, atRoll_rename, harvestEntries_rename, afterPosting_rename, nextRoller_rename,
    List.map_append]
  congr 1
  cases s.nextRoller with
  | none => rfl
  | some a => exact σ.lawEntries_rename _ (.roll a roll)

theorem turnEntries_rename (s : State G) (roll : Nat) :
    turnEntries (σ.state s) roll = (turnEntries s roll).map σ.entry := by
  simp only [turnEntries, entriesBeforeRoll_rename, nextStage_rename, afterPosting_rename,
    rollEntries_rename]
  split <;> simp

theorem some_to_bne (a : Seat) (b : Option Seat) :
    (some (σ.to a) != b.map σ.to) = (some a != b) := by
  cases b <;> simp [bne]

theorem beginActionTurn_rename (s : State G) (index roll : Nat) :
    beginActionTurn (σ.state s) index roll = σ.state (beginActionTurn s index roll) := by
  state_ext
  simp [beginActionTurn, List.filter_map, Function.comp_def, some_to_bne]

/-- What every turn change does to a state, whatever comes next. -/
def turnBase (s : State G) : State G :=
  { s with
    turnsTaken := s.turnsTaken + 1
    eventsApplied := s.eventsApplied + 1
    actionsThisTurn := fun _ => 0
    offers := [] }

theorem turnBase_rename (s : State G) : turnBase (σ.state s) = σ.state (turnBase s) := rfl

/-- What a new round adds to `turnBase`. -/
def roundBase (s : State G) : State G :=
  { turnBase s with
    round := s.round + 1
    builtThisRound := []
    declared := fun _ _ => 0
    deals := s.deals.filter fun d => decide (s.round < d.lastRound) }

theorem roundBase_rename (s : State G) : roundBase (σ.state s) = σ.state (roundBase s) := by
  state_ext
  simp [roundBase, List.filter_map, Function.comp_def]
  rfl

theorem startNextTurn_rename (s : State G) (roll : Nat) :
    startNextTurn (σ.state s) roll = σ.state (startNextTurn s roll) := by
  unfold startNextTurn
  rw [nextStage_rename]
  cases nextStage s with
  | setupTurn i => rfl
  | firstRound => exact σ.beginActionTurn_rename (turnBase s) 0 roll
  | sameRound i => exact σ.beginActionTurn_rename (turnBase s) i roll
  | newRound =>
    have := σ.beginActionTurn_rename (roundBase s) 0 roll
    rw [← roundBase_rename] at this
    exact this
  | gameOver =>
    state_ext
    exact σ.bestSeat_rename s s.turnOrder

theorem endTurnNow_rename (s : State G) :
    endTurnNow (σ.state s) = (endTurnNow s).map σ.state := by
  unfold endTurnNow
  simp only [state_seed, state_rollsMade, turnEntries_rename, record_rename]
  cases record s (turnEntries s (rollAt G s.seed s.rollsMade)) with
  | error m => rfl
  | ok s1 => exact congrArg Except.ok (σ.startNextTurn_rename s1 _)

/-! ## The whole of `step` -/

/-- A renamed event on a renamed game has the renamed result, and a rejected event stays rejected.
This holds for every state. -/
theorem step_rename (s : State G) (e : Event) :
    step G (σ.state s) (σ.event e) = (step G s e).map σ.state := by
  unfold step
  simp only [state_phase]
  by_cases h : (s.phase == .ended) = true
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    cases e with
    | forceEndTurn => exact σ.endTurnNow_rename s
    | propose seat body =>
      show act (σ.state s) (σ.to seat) (proposeBody (σ.state s) (σ.to seat) (σ.proposal body)) = _
      rw [proposeBody_rename, act_rename]
    | vote seat id yes =>
      show actThenCheckWin (σ.state s) (σ.to seat) (voteBody (σ.state s) (σ.to seat) id yes) = _
      rw [voteBody_rename, actThenCheckWin_rename]
    | sign seat id =>
      show act (σ.state s) (σ.to seat) (signBody (σ.state s) (σ.to seat) id) = _
      rw [signBody_rename, act_rename]
    | exit seat id =>
      show act (σ.state s) (σ.to seat) (exitBody (σ.state s) (σ.to seat) id) = _
      rw [exitBody_rename, act_rename]
    | move p m =>
      cases m with
      | endTurn =>
        show (if (σ.state s).isTurnOf (σ.to p) then endTurnNow (σ.state s)
              else .error "only the current seat can end its turn") =
            Except.map σ.state (if s.isTurnOf p then endTurnNow s
              else .error "only the current seat can end its turn")
        rw [isTurnOf_rename]
        by_cases ht : s.isTurnOf p = true
        · simp only [ht, ↓reduceIte]
          exact σ.endTurnNow_rename s
        · simp only [ht, ↓reduceIte, Bool.false_eq_true]
          rfl
      | place k loc =>
        show actThenCheckWin (σ.state s) (σ.to p) (moveBody (σ.state s) (σ.to p) (σ.move _)) = _
        rw [moveBody_rename, actThenCheckWin_rename]
      | bankTrade give get =>
        show actThenCheckWin (σ.state s) (σ.to p) (moveBody (σ.state s) (σ.to p) (σ.move _)) = _
        rw [moveBody_rename, actThenCheckWin_rename]
      | offer to give get =>
        show actThenCheckWin (σ.state s) (σ.to p) (moveBody (σ.state s) (σ.to p) (σ.move _)) = _
        rw [moveBody_rename, actThenCheckWin_rename]
      | accept id =>
        show actThenCheckWin (σ.state s) (σ.to p) (moveBody (σ.state s) (σ.to p) (σ.move _)) = _
        rw [moveBody_rename, actThenCheckWin_rename]
      | cancel id =>
        show actThenCheckWin (σ.state s) (σ.to p) (moveBody (σ.state s) (σ.to p) (σ.move _)) = _
        rw [moveBody_rename, actThenCheckWin_rename]
      | declare r n =>
        show actThenCheckWin (σ.state s) (σ.to p) (moveBody (σ.state s) (σ.to p) (σ.move _)) = _
        rw [moveBody_rename, actThenCheckWin_rename]

/-- Commandment II for every state: only acceptance and the resulting state are compared. -/
theorem step_toOption_rename (s : State G) (e : Event) :
    (step G (σ.state s) (σ.event e)).toOption = (step G s e).toOption.map σ.state := by
  rw [step_rename]
  cases step G s e <;> rfl

/-! ## A check that the statement has content

Swapping seats 0 and 1 really changes the game: the other seat goes first, and only that seat can
end the first turn. -/

/-- Swap seats 0 and 1. -/
def swapFirstTwo : Renaming where
  to x := if x = 0 then 1 else if x = 1 then 0 else x
  back x := if x = 0 then 1 else if x = 1 then 0 else x
  back_to x := by
    by_cases h0 : x = 0
    · simp [h0]
    · by_cases h1 : x = 1 <;> simp [h0, h1]
  to_back x := by
    by_cases h0 : x = 0
    · simp [h0]
    · by_cases h1 : x = 1 <;> simp [h0, h1]

/-- A new two-seat game of Tiny Settlers. -/
def swapExample : State tinySettlers := initialState tinySettlers 2 42 [25283273]

#guard (swapFirstTwo.state swapExample).turnOrder == [1, 0]
#guard (step tinySettlers swapExample (.move 0 .endTurn)).toOption.isSome
#guard (step tinySettlers swapExample (.move 1 .endTurn)).toOption.isNone
#guard (step tinySettlers (swapFirstTwo.state swapExample) (.move 1 .endTurn)).toOption.isSome
#guard (step tinySettlers (swapFirstTwo.state swapExample) (.move 0 .endTurn)).toOption.isNone

end Charter.Renaming
