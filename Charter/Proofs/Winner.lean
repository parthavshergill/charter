import Charter.Proofs.Deals

/-!
# A winner earned it

A game ends in one of two ways: a seat reaches the target, or the rounds run out. Either way the
winner is the seat with the most points.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-- `bestSeat` finds a seat from the list, with the most points on the list. -/
theorem bestSeat_spec {s : State G} {L : List Seat} {w : Seat} (h : bestSeat s L = some w) :
    w ∈ L ∧ ∀ p ∈ L, s.pointsOf p ≤ s.pointsOf w := by
  have key : ∀ (f : Option Seat → Seat → Option Seat),
      (∀ c, f none c = some c) →
      (∀ b c, f (some b) c = if s.pointsOf b < s.pointsOf c then some c else some b) →
      ∀ (L acc : List Seat) (o : Option Seat),
        (o = none → acc = []) →
        (∀ b, o = some b → b ∈ acc ∧ ∀ p ∈ acc, s.pointsOf p ≤ s.pointsOf b) →
        ∀ w, L.foldl f o = some w → w ∈ acc ++ L ∧ ∀ p ∈ acc ++ L, s.pointsOf p ≤ s.pointsOf w := by
    intro f hn hsome L
    induction L with
    | nil =>
      intro acc o _ h2 w hw
      simp only [List.foldl_nil] at hw
      simpa using h2 w hw
    | cons c t ih =>
      intro acc o h1 h2 w hw
      simp only [List.foldl_cons] at hw
      have hstep := ih (acc ++ [c]) (f o c) (by
        intro he
        cases o with
        | none => rw [hn] at he; cases he
        | some b =>
          rw [hsome] at he
          split at he <;> cases he) (by
        intro b hb
        cases o with
        | none =>
          rw [hn] at hb
          injection hb with hb
          subst hb
          have := h1 rfl
          subst this
          simp
        | some b0 =>
          rw [hsome] at hb
          obtain ⟨h3, h4⟩ := h2 b0 rfl
          split at hb
          · rename_i hlt
            injection hb with hb
            subst hb
            refine ⟨by simp, ?_⟩
            intro p hp
            cases List.mem_append.mp hp with
            | inl hp =>
              have := h4 p hp
              omega
            | inr hp =>
              simp only [List.mem_singleton] at hp
              subst hp
              exact Nat.le_refl _
          · rename_i hlt
            injection hb with hb
            subst hb
            refine ⟨List.mem_append_left _ h3, ?_⟩
            intro p hp
            cases List.mem_append.mp hp with
            | inl hp => exact h4 p hp
            | inr hp =>
              simp only [List.mem_singleton] at hp
              subst hp
              omega) w hw
      simpa [List.append_assoc] using hstep
  have := key _ (fun _ => rfl) (fun _ _ => rfl) L [] none (fun _ => rfl) (fun _ hb => by cases hb) w h
  simpa using this

/-- What is true of a winner. -/
structure WinnerInv (G : GameDef) (s : State G) : Prop where
  running : s.phase ≠ .ended → s.winner = none
  won : ∀ w, s.winner = some w →
    s.phase = .ended ∧ w ∈ s.turnOrder ∧
    (∀ p ∈ s.turnOrder, s.pointsOf p ≤ s.pointsOf w) ∧
    (G.targetPoints ≤ s.pointsOf w ∨ s.turnsTaken = maxTurns G s.turnOrder.length)
  isSome : s.phase = .ended → s.winner.isSome = true

theorem WinnerInv.start (G : GameDef) (seats : Nat) (serverSeed : UInt64) (nonces : List UInt64) :
    WinnerInv G (initialState G seats serverSeed nonces) :=
  ⟨fun _ => rfl, fun _ hw => (by cases hw), fun h => (by cases h)⟩

/-- A seat at the target beats every seat below it, and is best among those at it. -/
theorem endGame_winner {t s' : State G} {w : Seat} (hb : bestSeat t (seatsAtTarget t) = some w)
    (he : endGame t w = .ok s') :
    WinnerInv G s' := by
  obtain ⟨hw, hmax⟩ := bestSeat_spec hb
  obtain ⟨_, _, rfl⟩ := endGame_ok he
  have hmem := List.mem_filter.mp hw
  have htarget : G.targetPoints ≤ t.pointsOf w := by simpa using hmem.2
  refine ⟨fun h => (h rfl).elim, ?_, fun _ => rfl⟩
  intro x hx
  simp only [Option.some.injEq] at hx
  subst hx
  refine ⟨rfl, hmem.1, ?_, Or.inl htarget⟩
  intro p hp
  change t.pointsOf p ≤ t.pointsOf _
  by_cases hat : G.targetPoints ≤ t.pointsOf p
  · exact hmax p (List.mem_filter.mpr ⟨hp, by simpa using hat⟩)
  · omega

theorem WinnerInv.startNextTurn {s : State G} (hw : WinnerInv G s) (ht : TurnInv s)
    (hn : s.turnOrder ≠ []) (he : s.phase ≠ .ended) (roll : Nat) :
    WinnerInv G (startNextTurn s roll) := by
  have hnone := hw.running he
  have hT : (Engine.startNextTurn s roll).turnOrder = s.turnOrder := startNextTurn_turnOrder _ _
  have hK : (Engine.startNextTurn s roll).turnsTaken = s.turnsTaken + 1 :=
    startNextTurn_turnsTaken _ _
  have keep : Charter.nextStage s ≠ .gameOver → (Engine.startNextTurn s roll).winner = s.winner := by
    intro hs
    unfold Engine.startNextTurn
    split
    · rfl
    · rfl
    · rfl
    · rfl
    · rename_i hc
      exact absurd hc hs
  have running : ∀ {x : State G}, x.phase ≠ .ended → x.winner = none → WinnerInv G x := by
    intro x h1 h2
    exact ⟨fun _ => h2, fun w hw' => (by rw [h2] at hw'; cases hw'), fun h => absurd h h1⟩
  rcases nextStage_cases he with ⟨hp, ⟨i, hs, _⟩ | ⟨hs, _⟩⟩ | ⟨hp, ⟨_, hs⟩ | ⟨_, _, hs⟩ | ⟨h1, h2, hs⟩⟩
  · apply running
    · rw [(startNextTurn_setupTurn hs).1]; exact he
    · rw [keep (by rw [hs]; simp), hnone]
  · apply running
    · rw [(startNextTurn_firstRound hs).1]; simp
    · rw [keep (by rw [hs]; simp), hnone]
  · apply running
    · rw [(startNextTurn_sameRound hs).1]; simp
    · rw [keep (by rw [hs]; simp), hnone]
  · apply running
    · rw [(startNextTurn_newRound hs).1]; simp
    · rw [keep (by rw [hs]; simp), hnone]
  · have hphase := startNextTurn_gameOver (roll := roll) hs
    have hwin : (Engine.startNextTurn s roll).winner = bestSeat s s.turnOrder := by
      unfold Engine.startNextTurn
      rw [hs]
    have hagree : Agree (Engine.startNextTurn s roll) s :=
      ⟨hT, startNextTurn_books _ _, startNextTurn_pieces _ _, startNextTurn_laws _ _⟩
    cases hbest : bestSeat s s.turnOrder with
    | none => exact absurd (bestSeat_none hbest) hn
    | some w =>
      obtain ⟨hwm, hmax⟩ := bestSeat_spec hbest
      refine ⟨fun h => (h hphase).elim, ?_, fun _ => by rw [hwin, hbest]; rfl⟩
      intro x hx
      rw [hwin, hbest] at hx
      simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨hphase, by rw [hT]; exact hwm, ?_, Or.inr ?_⟩
      · intro p hp2
        rw [hT] at hp2
        rw [hagree.pointsOf, hagree.pointsOf]
        exact hmax p hp2
      · rw [hT, hK]
        obtain ⟨a1, a2, _, a4⟩ := ht.actions hp
        have hr : s.round = G.rounds := by omega
        obtain ⟨r, hr'⟩ : ∃ r, G.rounds = r + 1 := ⟨G.rounds - 1, by omega⟩
        rw [hr, hr'] at a4
        unfold maxTurns
        rw [hr']
        simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul] at a4 ⊢
        omega

theorem finish_winner {t s' : State G} {e : Event} (h : finish t e = .ok s') :
    s' = t ∨ ∃ w, bestSeat t (seatsAtTarget t) = some w ∧ endGame t w = .ok s' := by
  have fromCheck : checkWin t = .ok s' →
      s' = t ∨ ∃ w, bestSeat t (seatsAtTarget t) = some w ∧ endGame t w = .ok s' := by
    intro hc
    unfold checkWin at hc
    split at hc
    · rename_i w hb
      exact Or.inr ⟨w, hb, hc⟩
    · exact Or.inl (by simpa using hc.symm)
  cases e with
  | move p m => exact fromCheck h
  | vote a b c => exact fromCheck h
  | propose a b => exact Or.inl (by simpa [finish] using h.symm)
  | sign a b => exact Or.inl (by simpa [finish] using h.symm)
  | exit a b => exact Or.inl (by simpa [finish] using h.symm)
  | forceEndTurn => exact Or.inl (by simpa [finish] using h.symm)

theorem WinnerInv.step {s s' : State G} {e : Event} (hw : WinnerInv G s) (ht : TurnInv s)
    (hn : s.turnOrder ≠ []) (h : Engine.step G s e = .ok s') : WinnerInv G s' := by
  have he := step_not_ended h
  rcases step_view h with ⟨_, h⟩ | ⟨_, _, s1, hb, hf⟩
  · obtain ⟨b, _, rfl⟩ := endTurnNow_ok h
    exact WinnerInv.startNextTurn (s := { s with books := b, journal := _ })
      ⟨hw.1, hw.2, hw.3⟩ ⟨ht.1, ht.2, ht.3⟩ hn he _
  · have f := bodyOf_frame hb
    rcases finish_winner hf with rfl | ⟨w, hbest, hend⟩
    · have hph : (countAction s1 (seatOf e)).phase ≠ .ended := by
        change s1.phase ≠ .ended
        rw [f.phase]
        exact he
      have hwin : (countAction s1 (seatOf e)).winner = none := by
        change s1.winner = none
        rw [f.winner]
        exact hw.running he
      exact ⟨fun _ => hwin, fun w hw' => (by rw [hwin] at hw'; cases hw'), fun h => absurd h hph⟩
    · exact endGame_winner hbest hend

end Charter.Proofs
