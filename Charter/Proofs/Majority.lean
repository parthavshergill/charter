import Charter.Proofs.CoverStep

/-!
# Only the majority changes the rules

The laws change only at the vote that gives a law more than half of all seats. Such a vote is always
accepted, even when it ends the game, because refunds always post.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

@[simp] theorem countAction_deals (t : State G) (seat : Seat) :
    (countAction t seat).deals = t.deals := rfl
@[simp] theorem countAction_laws (t : State G) (seat : Seat) :
    (countAction t seat).laws = t.laws := rfl

/-- `finish` never changes the laws. -/
theorem finish_laws {s s' : State G} {e : Event} (h : finish s e = .ok s') : s'.laws = s.laws := by
  rcases finish_cases h with rfl | ⟨w, hw⟩
  · rfl
  · obtain ⟨_, _, rfl⟩ := endGame_ok hw
    rfl

theorem endGame_eq {t : State G} {b : Books} (w : Seat)
    (hb : t.books.postAll (t.deals.flatMap t.refundEntries) = some b) :
    endGame t w = .ok { t with
      books := b, journal := t.journal ++ t.deals.flatMap t.refundEntries
      phase := .ended
      winner := some ((bestSeat ({ t with books := b, journal := t.journal ++ t.deals.flatMap t.refundEntries } : State G)
        t.turnOrder).getD w)
      deals := [], offers := [], openProposals := [] } := by
  unfold endGame
  rw [record_some hb]
  rfl

/-- Ending the game always works. -/
theorem endGame_some (hG : G.Valid) (t : State G) (hnd : (t.deals.map (·.id)).Nodup)
    (hsig : ∀ d ∈ t.deals, d.deal.signers.Nodup) (w : Seat) :
    ∃ s', endGame t w = .ok s' ∧ s'.laws = t.laws := by
  obtain ⟨b, hb⟩ := refunds_post hG t t.deals hnd hsig
  exact ⟨_, endGame_eq w hb, rfl⟩

/-- Looking for a winner always works. -/
theorem checkWin_some (hG : G.Valid) (t : State G) (hnd : (t.deals.map (·.id)).Nodup)
    (hsig : ∀ d ∈ t.deals, d.deal.signers.Nodup) :
    ∃ s', checkWin t = .ok s' ∧ s'.laws = t.laws := by
  unfold checkWin
  split
  · exact endGame_some hG t hnd hsig _
  · exact ⟨t, rfl, rfl⟩

/-- Commandment III(a). -/
theorem laws_change {s s' : State G} {e : Event} (h : Engine.step G s e = .ok s')
    (hne : s'.laws ≠ s.laws) :
    ∃ seat id p L,
      e = .vote seat id true ∧ s.openProposal? id = some p ∧ p.body = .law L ∧
      seat ∈ s.turnOrder ∧ (p.votes.map (·.1)).contains seat = false ∧
      (p.withVote seat true).hasMajority s.turnOrder.length ∧
      s'.laws = enact s.laws id L := by
  rcases step_view h with ⟨_, h⟩ | ⟨_, hc, s1, hb, hf⟩
  · obtain ⟨_, _, rfl⟩ := endTurnNow_ok h
    exact absurd (by simp) hne
  · have hl := finish_laws hf
    have hl1 : s'.laws = s1.laws := by rw [hl]; rfl
    cases e with
    | vote seat id yes =>
      have hb' : voteBody s seat id yes = .ok s1 := hb
      obtain ⟨_, p, L, hp, hL, hv, ⟨hd, hs1⟩ | ⟨_, hs1⟩⟩ := voteBody_ok hb'
      · have hseat := (canAct_mem hc).1
        simp only [isDecidingVote, Bool.and_eq_true, decide_eq_true_eq] at hd
        obtain ⟨rfl, hm⟩ := hd
        refine ⟨seat, id, p, L, rfl, hp, hL, hseat, hv, hm, ?_⟩
        rw [hl1, hs1]
        unfold decideLaw
        simp only
        split
        · rfl
        · rename_i hprob
          exfalso
          apply hne
          rw [hl1, hs1]
          unfold decideLaw
          simp [hprob]
      · exact absurd (by rw [hl1, hs1]) hne
    | forceEndTurn => cases hb
    | move p m => exact absurd (hl1.trans (body_laws (by simp) hb)) hne
    | propose a b => exact absurd (hl1.trans (body_laws (by simp) hb)) hne
    | sign a b => exact absurd (hl1.trans (body_laws (by simp) hb)) hne
    | exit a b => exact absurd (hl1.trans (body_laws (by simp) hb)) hne

/-- Commandment III(b). -/
theorem majority_passes (hG : G.Valid) {s : State G} (hi : IdInv s) (seat id : Nat) (p : OpenProposal)
    (L : Law) (hPhase : s.phase = .actions) (hSeat : seat ∈ s.turnOrder)
    (hp : s.openProposal? id = some p) (hL : p.body = .law L)
    (hv : (p.votes.map (·.1)).contains seat = false)
    (hA : s.actionsThisTurn seat < maxActionsPerTurn)
    (hM : (p.withVote seat true).hasMajority s.turnOrder.length) (hprob : lawProblems G s L = []) :
    ∃ s'', Engine.step G s (.vote seat id true) = .ok s'' ∧ s''.laws = enact s.laws id L := by
  have hd : isDecidingVote s p seat true = true := by
    simp only [isDecidingVote, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨trivial, hM⟩
  have hbody : voteBody s seat id true = .ok (decideLaw s id L) := by
    unfold voteBody
    simp only [hPhase, hp, hL, hv, hd]
    rfl
  have hdl : (decideLaw s id L).laws = enact s.laws id L := by
    have hx : (lawProblems G s L).isEmpty = true := by rw [hprob]; rfl
    unfold decideLaw
    simp only [hx, ↓reduceIte]
  have hdeals : (decideLaw s id L).deals = s.deals := (decideLaw_counters s id L).2.2.1
  obtain ⟨s'', h1, h2⟩ := checkWin_some hG (countAction (decideLaw s id L) seat)
    (by rw [countAction_deals, hdeals]; exact hi.deal_nodup)
    (by
      intro d hd'
      rw [countAction_deals, hdeals] at hd'
      exact hi.signers_nodup d hd')
  have h2' : s''.laws = enact s.laws id L := by
    rw [h2, countAction_laws, hdl]
  refine ⟨s'', ?_, h2'⟩
  have hca : canAct s seat = true := by simp [canAct, hSeat, hA]
  unfold Engine.step
  rw [ite_eq_right_of_eq_false _ _ (by simp [hPhase])]
  simp only [actThenCheckWin, act, hca, ↓reduceIte, hbody]
  exact h1

end Charter.Proofs
