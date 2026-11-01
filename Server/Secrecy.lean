import Charter.Words

/-!
# What a seat may know

A game can keep some things from its players. The engine still holds everything. The server hides
things through one function, `observe`, and it builds everything it sends to a seat from what `observe`
gives that seat. `Server/SecrecyPromise.lean` states what `observe` hides, and proves it.

A game marks three kinds of secret, in its `GameSpec`:

* **Hidden goods.** Of a hidden resource, a seat sees only what it holds itself, in its hand or in its
  own deposits. It does not see what other seats, the bank or the treasury hold. The bank and the
  treasury must be hidden too: every resource has a fixed total, so the public piles would give away the
  sum of the hands.
* **Sealed declarations.** A seat sees only its own declarations. They clear when the round ends.
* **A hidden roll.** Only the seat whose turn the roll starts sees it.

The game's seed is always hidden, as commandment VIII asks: it tells every roll to come. When the game
has ended, `observe` hides nothing.

This file has definitions only. The proofs are in `Server/SecrecyProofs.lean`.
-/

namespace CharterServer

open Charter

/-- What a game keeps from its players. A game that marks nothing keeps only the seed. -/
structure Secrecy where
  /-- Resources whose amounts only their owner sees. -/
  hidden : List Res := []
  /-- A seat's declarations are seen only by that seat. -/
  sealedDeclarations : Bool := false
  /-- The roll is seen only by the seat whose turn it starts. -/
  hiddenRoll : Bool := false
  deriving Repr, DecidableEq, Inhabited

namespace Secrecy

/-- This account belongs to the viewer: its own hand, or its own deposit in a deal. A spectator, `none`,
owns nothing. -/
def owns (viewer : Option Seat) : Account → Bool
  | .player p => viewer == some p
  | .deposit _ p => viewer == some p
  | _ => false

/-- The viewer may see how much of `r` this account holds. -/
def seesHolding (sec : Secrecy) (viewer : Option Seat) (a : Account) (r : Res) : Bool :=
  !(sec.hidden.contains r) || owns viewer a

/-- The viewer may see the amount of this journal entry. It always sees the rest of it: who paid whom,
what and why. -/
def seesAmount (sec : Secrecy) (viewer : Option Seat) (e : Entry) : Bool :=
  !(sec.hidden.contains e.res) || owns viewer e.src || owns viewer e.dst

/-- The viewer may see what this seat has declared. -/
def seesDeclared (sec : Secrecy) (viewer : Option Seat) (p : Seat) : Bool :=
  !sec.sealedDeclarations || viewer == some p

/-- The viewer may see the last roll: the roll is public, or it started the viewer's own turn. -/
def seesRoll {G : GameDef} (sec : Secrecy) (viewer : Option Seat) (s : State G) : Bool :=
  !sec.hiddenRoll || (viewer.isSome && viewer == s.currentSeat)

/-- A journal entry as the viewer sees it: in full, or with its amount as 0. -/
def shownEntry (sec : Secrecy) (viewer : Option Seat) (e : Entry) : Entry :=
  if sec.seesAmount viewer e then e else { e with amount := 0 }

end Secrecy

/-- **The one choke point.** Everything a viewer may know about this state. `viewer` is a seat, or `none`
for a spectator. Each hidden number becomes 0, a hidden roll becomes no roll, and the seed becomes 0.
Nothing else changes. After the game ends, nothing is hidden. -/
def observe {G : GameDef} (sec : Secrecy) (viewer : Option Seat) (s : State G) : State G :=
  if s.phase = .ended then s else
  { s with
    books := fun a r => if sec.seesHolding viewer a r then s.books a r else 0
    journal := if sec.hidden.isEmpty then s.journal else
      s.journal.map (sec.shownEntry viewer)
    declared := fun p r => if sec.seesDeclared viewer p then s.declared p r else 0
    lastRoll := if sec.seesRoll viewer s then s.lastRoll else none
    seed := 0 }

/-- **What may differ** between two states while the viewer cannot tell them apart. Only the hidden
numbers, the hidden roll and the seed differ. Everything the viewer may see is the same. -/
structure HiddenDifference {G : GameDef} (sec : Secrecy) (viewer : Option Seat) (s₁ s₂ : State G) : Prop where
  /-- Apart from the books, the journal, the declarations, the last roll and the seed, the states are
  the same. -/
  restSame : { s₁ with books := s₂.books, journal := s₂.journal, declared := s₂.declared,
                       lastRoll := s₂.lastRoll, seed := s₂.seed } = s₂
  /-- Every holding the viewer may see is the same. -/
  holdings : ∀ a r, sec.seesHolding viewer a r → s₁.balance a r = s₂.balance a r
  /-- The journals list the same movements, of the same goods, between the same accounts, for the same
  reasons. Only amounts the viewer may not see can differ. -/
  journal : s₁.journal.length = s₂.journal.length ∧
    ∀ xy ∈ s₁.journal.zip s₂.journal,
      { xy.1 with amount := 0 } = { xy.2 with amount := 0 } ∧ (sec.seesAmount viewer xy.1 → xy.1 = xy.2)
  /-- Every declaration the viewer may see is the same. -/
  declared : ∀ p r, sec.seesDeclared viewer p → s₁.declared p r = s₂.declared p r
  /-- If the viewer may see the last roll, it is the same. -/
  roll : sec.seesRoll viewer s₁ → s₁.lastRoll = s₂.lastRoll

/-! ## Events -/

/-- An event as the viewer may know it. A sealed declaration by another seat keeps its resource and
loses its number. No other event holds a secret. -/
def observeEvent (sec : Secrecy) (viewer : Option Seat) : Event → Event
  | .move p (.declare r n) => .move p (.declare r (if sec.seesDeclared viewer p then n else 0))
  | e => e

end CharterServer
