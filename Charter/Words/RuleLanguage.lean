import Charter.Words.Game

/-!
# The rule language

A law has no way to name a seat. `Party` lists everything a law can refer to. The rest of this
file is the grammar. `Charter/Words/LawEffects.lean` says what it means.
-/

namespace Charter

/-- Who a law can name. There is no way to name one seat. -/
inductive Party where
  /-- The player who caused the trigger: the builder, the player the dice just paid, or the seat
  whose turn the roll starts. -/
  | actor
  /-- The current player inside a `forEach`. -/
  | each
  | treasury
  | bank
  deriving Repr, DecidableEq

/-- A resource, as a law names it. -/
inductive ResRef where
  | lit (r : Res)
  /-- The resource the dice just paid. -/
  | harvested
  deriving Repr, DecidableEq

mutual
  /-- A number a law can compute. `sub` stops at zero and `div` rounds down. -/
  inductive Expr where
    | lit (n : Nat)
    /-- The amount the dice just paid. -/
    | harvestedAmount
    /-- The total the dice just showed. It is 0 outside a roll. -/
    | rolled
    | holding (p : Party) (r : ResRef)
    | points (p : Party)
    | count (p : Party) (k : PieceKind)
    | add (a b : Expr)
    | sub (a b : Expr)
    | mul (a b : Expr)
    /-- Divides by a fixed number. -/
    | div (a : Expr) (n : Nat)
    /-- Divides by a computed number. Dividing by zero gives 0. -/
    | divBy (a b : Expr)
    | min (a b : Expr)
    | max (a b : Expr)
    /-- The current round. -/
    | round
    /-- The number this seat has declared for this resource this round. It is 0 for the treasury, the
    bank and anyone not in play here. -/
    | declared (p : Party) (r : ResRef)
    /-- The sum of `a` over every seat that passes `c`. Inside, `each` means the seat being measured. -/
    | totalOver (c : Cond) (a : Expr)
    /-- The most of `a` over every seat that passes `c`, or 0 if none does. This is a number, not a seat.
    Inside, `each` means the seat being measured. -/
    | mostOver (c : Cond) (a : Expr)
    /-- The least of `a` over every seat that passes `c`, or 0 if none does. This is a number, not a seat.
    Inside, `each` means the seat being measured. -/
    | leastOver (c : Cond) (a : Expr)
    deriving Repr, DecidableEq

  /-- A true-or-false test a law can make. -/
  inductive Cond where
    | yes
    | lt (a b : Expr)
    | le (a b : Expr)
    | eq (a b : Expr)
    | and (a b : Cond)
    | or (a b : Cond)
    | not (c : Cond)
    | harvestedIs (r : Res)
    deriving Repr, DecidableEq
end

/-- What a law can do: move resources, for each seat that passes a test, or if a test passes. -/
inductive Effect where
  | transfer (src dst : Party) (r : ResRef) (amount : Expr)
  | forEach (c : Cond) (body : List Effect)
  | when (c : Cond) (body : List Effect)
  deriving Repr

/-- One part of a law: a reaction to a trigger, or a change to the rules. -/
inductive Clause where
  | onHarvest (body : List Effect)
  | onBuild (k : PieceKind) (body : List Effect)
  | onRoundEnd (body : List Effect)
  /-- Runs on every roll of the dice, including a roll that pays nobody. -/
  | onRoll (body : List Effect)
  | setCost (k : PieceKind) (b : Bundle)
  | setPoints (k : PieceKind) (n : Nat)
  | setBankRate (n : Nat)
  | newPiece (p : PieceDef)
  /-- Removes the law with this id, and with it every rule that law changed. If that law made a new
  piece, the pieces already on the board stay there, and they are worth 0 points and yield 0. -/
  | repeal (lawId : Nat)
  deriving Repr

/-- A law. Its `title` is free text with no meaning in the game. -/
structure Law where
  title : String
  clauses : List Clause
  deriving Repr

end Charter
