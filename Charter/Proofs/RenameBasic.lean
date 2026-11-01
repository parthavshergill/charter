import Charter.Engine

/-!
# Renaming: names, books and the simple views of a state

Commandment II says that the engine treats renamed seats alike. These files prove it one helper at
a time. Each lemma has the same shape: run the helper on renamed inputs, and get the renamed result.

This file holds the facts about names and books, and the small views of a state: balances, turns,
piece counts and points.
-/

namespace Charter.Renaming

open Charter Charter.Engine

variable (σ : Renaming) {G : GameDef}

/-! ## Names -/

/-- The same renaming, read backwards. `Renaming.state` uses it for the books. -/
def inv : Renaming := ⟨σ.back, σ.to, σ.to_back, σ.back_to⟩

theorem to_inj {a b : Seat} (h : σ.to a = σ.to b) : a = b := by
  have := congrArg σ.back h
  simpa [σ.back_to] using this

@[simp] theorem to_eq_to {a b : Seat} : σ.to a = σ.to b ↔ a = b :=
  ⟨σ.to_inj, fun h => h ▸ rfl⟩

@[simp] theorem to_beq_to {a b : Seat} : (σ.to a == σ.to b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

@[simp] theorem to_bne_to {a b : Seat} : (σ.to a != σ.to b) = (a != b) := by
  simp [bne]

@[simp] theorem some_to_eq {a : Seat} {b : Option Seat} :
    (some (σ.to a) = b.map σ.to) ↔ some a = b := by
  cases b <;> simp

@[simp] theorem map_to_eq_map_to {a b : Option Seat} : a.map σ.to = b.map σ.to ↔ a = b := by
  cases a <;> cases b <;> simp

@[simp] theorem map_to_beq_some {a : Option Seat} {b : Seat} :
    (a.map σ.to == some (σ.to b)) = (a == some b) := by
  cases a with
  | none => rfl
  | some x => simp

@[simp] theorem contains_map_to (l : List Seat) (a : Seat) :
    (l.map σ.to).contains (σ.to a) = l.contains a := by
  induction l with
  | nil => rfl
  | cons x t ih => simp

@[simp] theorem nodup_map_to (l : List Seat) : (l.map σ.to).Nodup ↔ l.Nodup := by
  simp [List.Nodup, List.pairwise_map]

@[simp] theorem inv_account_account (a : Account) : σ.inv.account (σ.account a) = a := by
  cases a <;> simp [account, inv, σ.back_to]

@[simp] theorem account_inv_account (a : Account) : σ.account (σ.inv.account a) = a := by
  cases a <;> simp [account, inv, σ.to_back]

theorem account_inj {a b : Account} (h : σ.account a = σ.account b) : a = b := by
  have := congrArg σ.inv.account h
  simpa using this

@[simp] theorem account_eq_account {a b : Account} : σ.account a = σ.account b ↔ a = b :=
  ⟨σ.account_inj, fun h => h ▸ rfl⟩

@[simp] theorem account_beq_account {a b : Account} : (σ.account a == σ.account b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

@[simp] theorem account_bne_account {a b : Account} : (σ.account a != σ.account b) = (a != b) := by
  simp [bne]

@[simp] theorem account_player (i : Seat) : σ.account (.player i) = .player (σ.to i) := rfl
@[simp] theorem account_deposit (k : Nat) (i : Seat) :
    σ.account (.deposit k i) = .deposit k (σ.to i) := rfl
@[simp] theorem account_bank : σ.account .bank = .bank := rfl
@[simp] theorem account_treasury : σ.account .treasury = .treasury := rfl

/-! ## Entries -/

@[simp] theorem entry_src (e : Entry) : (σ.entry e).src = σ.account e.src := rfl
@[simp] theorem entry_dst (e : Entry) : (σ.entry e).dst = σ.account e.dst := rfl
@[simp] theorem entry_res (e : Entry) : (σ.entry e).res = e.res := rfl
@[simp] theorem entry_amount (e : Entry) : (σ.entry e).amount = e.amount := rfl
@[simp] theorem entry_reason (e : Entry) : (σ.entry e).reason = e.reason := rfl

/-! ## Books -/

/-- Books with every account renamed. -/
def books (b : Books) : Books := fun a r => b (σ.inv.account a) r

@[simp] theorem books_account (b : Books) (a : Account) (r : Res) :
    σ.books b (σ.account a) r = b a r := by
  simp [books]

theorem books_apply (b : Books) (a : Account) (r : Res) :
    σ.books b a r = b (σ.inv.account a) r := rfl

/-- Posting a renamed entry to renamed books gives the renamed result. -/
theorem post_rename (b : Books) (e : Entry) :
    (σ.books b).post (σ.entry e) = (b.post e).map σ.books := by
  unfold Books.post
  by_cases h : e.amount ≤ b e.src e.res ∧ e.src ≠ e.dst
  · have h' : (σ.entry e).amount ≤ σ.books b (σ.entry e).src (σ.entry e).res ∧
        (σ.entry e).src ≠ (σ.entry e).dst := by simpa using h
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h')]
    simp only [Option.map_some]
    congr 1
    funext a r
    obtain ⟨a, rfl⟩ : ∃ c, a = σ.account c := ⟨σ.inv.account a, by simp⟩
    simp
  · have h' : ¬ ((σ.entry e).amount ≤ σ.books b (σ.entry e).src (σ.entry e).res ∧
        (σ.entry e).src ≠ (σ.entry e).dst) := by simpa using h
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h')]
    rfl

/-- Posting a renamed list to renamed books gives the renamed result. -/
theorem postAll_rename (b : Books) (es : List Entry) :
    (σ.books b).postAll (es.map σ.entry) = (b.postAll es).map σ.books := by
  induction es generalizing b with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, Books.postAll, post_rename]
    cases b.post e with
    | none => rfl
    | some b' => simpa using ih b'

/-! ## The fields of a renamed state -/

section fields
variable (s : State G)

@[simp] theorem state_turnOrder : (σ.state s).turnOrder = s.turnOrder.map σ.to := rfl
@[simp] theorem state_phase : (σ.state s).phase = s.phase := rfl
@[simp] theorem state_round : (σ.state s).round = s.round := rfl
@[simp] theorem state_turnIndex : (σ.state s).turnIndex = s.turnIndex := rfl
@[simp] theorem state_turnsTaken : (σ.state s).turnsTaken = s.turnsTaken := rfl
@[simp] theorem state_rollsMade : (σ.state s).rollsMade = s.rollsMade := rfl
@[simp] theorem state_lastRoll : (σ.state s).lastRoll = s.lastRoll := rfl
@[simp] theorem state_seed : (σ.state s).seed = s.seed := rfl
@[simp] theorem state_seedCommitment : (σ.state s).seedCommitment = s.seedCommitment := rfl
theorem state_books : (σ.state s).books = σ.books s.books := rfl
@[simp] theorem state_journal : (σ.state s).journal = s.journal.map σ.entry := rfl
@[simp] theorem state_pieces : (σ.state s).pieces = s.pieces.map σ.piece := rfl
@[simp] theorem state_laws : (σ.state s).laws = s.laws := rfl
@[simp] theorem state_openProposals :
    (σ.state s).openProposals = s.openProposals.map σ.openProposal := rfl
@[simp] theorem state_nextProposalId : (σ.state s).nextProposalId = s.nextProposalId := rfl
@[simp] theorem state_deals : (σ.state s).deals = s.deals.map σ.activeDeal := rfl
@[simp] theorem state_dealsStarted : (σ.state s).dealsStarted = s.dealsStarted := rfl
@[simp] theorem state_offers : (σ.state s).offers = s.offers.map σ.offer := rfl
@[simp] theorem state_nextOfferId : (σ.state s).nextOfferId = s.nextOfferId := rfl
@[simp] theorem state_builtThisRound :
    (σ.state s).builtThisRound = s.builtThisRound.map (fun x => (σ.to x.1, x.2)) := rfl
@[simp] theorem state_actionsThisTurn_to (p : Seat) :
    (σ.state s).actionsThisTurn (σ.to p) = s.actionsThisTurn p := by
  simp [state, σ.back_to]
@[simp] theorem state_eventsApplied : (σ.state s).eventsApplied = s.eventsApplied := rfl
@[simp] theorem state_winner : (σ.state s).winner = s.winner.map σ.to := rfl

@[simp] theorem state_rules : (σ.state s).rules = s.rules := rfl
@[simp] theorem state_costOf (k : PieceKind) : (σ.state s).costOf k = s.costOf k := rfl

end fields

/-! ## Small views of a state -/

section views
variable (s : State G)

@[simp] theorem piece_owner (x : Piece) : (σ.piece x).owner = σ.to x.owner := rfl
@[simp] theorem piece_kind (x : Piece) : (σ.piece x).kind = x.kind := rfl
@[simp] theorem piece_loc (x : Piece) : (σ.piece x).loc = x.loc := rfl

theorem balance_rename (a : Account) (r : Res) :
    (σ.state s).balance (σ.account a) r = s.balance a r := by
  simp [State.balance, state_books]

theorem balance_player (i : Seat) (r : Res) :
    (σ.state s).balance (.player (σ.to i)) r = s.balance (.player i) r :=
  σ.balance_rename s (.player i) r

theorem balance_deposit (k : Nat) (i : Seat) (r : Res) :
    (σ.state s).balance (.deposit k (σ.to i)) r = s.balance (.deposit k i) r :=
  σ.balance_rename s (.deposit k i) r

@[simp] theorem currentSeat_rename : (σ.state s).currentSeat = s.currentSeat.map σ.to := by
  simp [State.currentSeat]

@[simp] theorem isTurnOf_rename (p : Seat) : (σ.state s).isTurnOf (σ.to p) = s.isTurnOf p := by
  simp [State.isTurnOf]

@[simp] theorem isLastTurn_rename : (σ.state s).isLastTurn = s.isLastTurn := by
  simp [State.isLastTurn]

@[simp] theorem affords_rename (p : Seat) (b : Bundle) :
    (σ.state s).affords (σ.to p) b = s.affords p b := by
  simp [State.affords, balance_player]

@[simp] theorem countOf_rename (p : Seat) (k : PieceKind) :
    (σ.state s).countOf (σ.to p) k = s.countOf p k := by
  simp [State.countOf, List.filter_map, Function.comp_def]

@[simp] theorem pointsOf_rename (p : Seat) : (σ.state s).pointsOf (σ.to p) = s.pointsOf p := by
  simp [State.pointsOf, List.filter_map, Function.comp_def]

end views

end Charter.Renaming
