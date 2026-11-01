
/-!
# The layout of observations and actions (layout version 1)

A copy of the training harness's `rl/lean/CharterRL/Layout.lean` at layout version 1, without the optional table
of moves (no shipped policy reads it) and without the JSON printer. The trained network reads numbers by
position, so this file must match the layout the checkpoint was trained on, number for number.
`scripts/policy_diff.py` and `ServerTests` check the sizes.

An observation is one flat list of numbers made of tables. Each table has a fixed number of rows. Column 0 of
every table is `real`: 1 for a row that means something, 0 for padding. Nothing in a table names a resource, a
piece or a law. A table's rows may be in step with the rows of `resources` or `kinds`, and a group of columns may
run across them, as `by_res`, `by_kind` and `by_seat` say. Seats are always in the order: this seat, then the
others in turn order.
-/

namespace CharterServer.Policy

/-- Goes up whenever the layout of observations or actions changes. A saved policy names the one it needs. -/
def version : Nat := 1

/-! ## Named limits. A game that does not fit is refused when an environment is created. -/

def maxSeats : Nat := 6
def maxRes : Nat := 8
/-- Kinds of piece that go on a link. Every game so far has one. -/
def maxLinkKinds : Nat := 1
/-- Kinds of piece that go on a spot: placed there, replacing a piece, or attached to one. -/
def maxSpotKinds : Nat := 8
def maxKinds : Nat := maxLinkKinds + maxSpotKinds
def maxSpots : Nat := 60
def maxLinks : Nat := 84
def maxTiles : Nat := 24
def maxLaws : Nat := 16

/-- The numbers a seat can declare. -/
def declareLevels : Array Nat := #[0, 1, 2, 3, 4, 6, 8, 12]

/-! ## Tables -/

/-- What a run of columns lines up with. -/
inductive Across where
  /-- A single number. -/
  | one
  /-- One column per seat: this seat first. -/
  | seats
  /-- One column per row of `resources`. -/
  | res
  /-- One column per row of `kinds`. -/
  | kinds
  deriving BEq, Inhabited

/-- A run of columns. -/
structure Cols where
  name : String
  across : Across := .one
  deriving Inhabited

def Cols.width (c : Cols) : Nat :=
  match c.across with
  | .one => 1
  | .seats => maxSeats
  | .res => maxRes
  | .kinds => maxKinds

/-- One table. -/
structure Table where
  name : String
  rows : Nat
  /-- The rows line up with this. -/
  rowsAre : Across := .one
  cols : List Cols
  deriving Inhabited

def Table.width (t : Table) : Nat := (t.cols.map (·.width)).sum

/-- The column where this run starts. A wrong name stops the program when it loads. -/
def Table.col (t : Table) (name : String) : Nat :=
  let rec go (cs : List Cols) (at_ : Nat) : Nat :=
    match cs with
    | [] => panic! s!"table {t.name} has no column {name}"
    | c :: rest => if c.name == name then at_ else go rest (at_ + c.width)
  go t.cols 0

private def ones (names : List String) : List Cols := names.map fun n => { name := n }
private def across (a : Across) (names : List String) : List Cols := names.map fun n => { name := n, across := a }

/-- What a law does, by its shape. Laws in force and the open proposal both have these columns. -/
def lawShape : List String :=
  [ "on_harvest", "on_build", "on_round_end", "on_roll", "now", "set_cost", "set_points", "set_bank_rate"
  , "set_worth", "new_piece", "end_game", "repeal", "transfers", "piece_moves", "for_each", "when"
  , "from_actor", "from_each", "from_treasury", "from_bank", "to_actor", "to_each", "to_treasury", "to_bank"
  , "size" ]

def tGlobal : Table :=
  { name := "global", rows := 1, cols := ones
      [ "real", "decide_vote", "decide_setup", "decide_turn", "round", "rounds_left", "target", "seats", "bank_rate"
      , "dice_top", "last_roll", "actions_used", "setup_step", "turn_pos", "my_pos", "laws", "moves_overflow" ] }

def tSeats : Table :=
  { name := "seats", rows := maxSeats, rowsAre := .seats, cols := ones
      [ "real", "current", "order_pos", "points", "to_target", "goods", "income", "spot_pieces", "link_pieces"
      , "actions_used" ] }

def tResources : Table :=
  { name := "resources", rows := maxRes, rowsAre := .res
    cols := ones ["real", "is_good", "stock", "bank", "treasury", "map_pips", "tiles", "demand", "worth"]
      ++ across .seats ["holding", "income", "declared"] }

def tKinds : Table :=
  { name := "kinds", rows := maxKinds, rowsAre := .kinds
    cols := ones
        [ "real", "on_link", "on_spot", "on_upgrade", "on_attach", "points", "yield", "limit", "cost_total"
        , "under_points", "under_yield", "my_short", "my_afford", "my_room" ]
      ++ across .res ["cost"] ++ across .seats ["count"] }

def tTiles : Table :=
  { name := "tiles", rows := maxTiles
    cols := ones ["real", "x", "y", "number", "pips", "stock", "demand", "worth", "my_income", "my_holding"]
      ++ across .res ["res"] }

def tSpots : Table :=
  { name := "spots", rows := maxSpots
    cols := ones
        [ "real", "x", "y", "degree", "pips", "goods", "demand_value", "new_for_me", "free", "reach_me", "occupied"
        , "piece_points", "piece_yield", "attached" ]
      ++ across .seats ["owner"] ++ across .res ["pips_by_res"] }

def tLinks : Table :=
  { name := "links", rows := maxLinks
    cols := ones ["real", "x", "y", "end_a", "end_b", "taken", "reach_me", "free_ends", "best_end_pips"]
      ++ across .seats ["owner"] }

def tLaws : Table :=
  { name := "laws", rows := maxLaws, cols := ones (["real", "founding"] ++ lawShape) }

def tProposal : Table :=
  { name := "proposal", rows := 1
    cols := ones (["real"] ++ lawShape ++ ["yes_count", "yes_needed", "deciding", "previewed", "ends_game", "bank_rate_change"])
      ++ across .seats ["by", "voted_yes", "voted_no", "next_turn_net", "now_net", "points_change"]
      ++ across .res ["next_turn_my_net"] ++ across .kinds ["cost_change"] }

/-- The tables of every observation, in order. -/
def baseTables : List Table := [tGlobal, tSeats, tResources, tKinds, tTiles, tSpots, tLinks, tLaws, tProposal]

def Table.size (t : Table) : Nat := t.rows * t.width

/-- Where a table starts. -/
def offsetOf (name : String) : Nat :=
  let rec go (ts : List Table) (at_ : Nat) : Nat :=
    match ts with
    | [] => at_
    | t :: rest => if t.name == name then at_ else go rest (at_ + t.size)
  go baseTables 0

def baseSize : Nat := (baseTables.map (·.size)).sum

/-! ## Actions

One flat list: end turn, the two votes, bank trades by row of `resources`, declarations by row and level, a link
piece on a link, and a spot piece on a spot. Offers and deals have no action. -/

def actEnd : Nat := 0
def actVoteNo : Nat := 1
def actVoteYes : Nat := 2
def actBank : Nat := 3
def actDeclare : Nat := actBank + maxRes * maxRes
def actLink : Nat := actDeclare + maxRes * declareLevels.size
def actSpot : Nat := actLink + maxLinkKinds * maxLinks
def actSize : Nat := actSpot + maxSpotKinds * maxSpots

#guard baseSize == 4434
#guard actSize == 695

end CharterServer.Policy
