import Charter.Words.Game

/-!
# The layout of observations and actions (layout version 2)

A copy of the training harness's `rl/lean/CharterRL/Layout.lean` at commit `89a3a51` (layout version 2, the
layout of `entity2`'s `CANDIDATE 1`), without the optional table of moves (no shipped policy reads it) and without
the JSON printer. The trained network reads numbers by position, so this file must match the layout the checkpoint
was trained on, number for number. The weights file records the layout version, and the server checks it.
-/

namespace CharterServer.Policy

/-- Goes up whenever the layout of observations or actions changes. A saved policy names the one it needs.

Version 2: every game that passes `G.Valid` fits, at any seat count from 2 to 6. The limits are the engine's own.
Links and tiles have no fixed limit in the engine, so they have no table of their own: what a spot's links and tiles
hold is in the spot's row, and a placement is chosen by its row in `places`, the table of legal placements. -/
def version : Nat := 2

/-! ## Named limits: the engine's (`Charter/Words/Game.lean`), so no valid game is refused. -/

def maxSeats : Nat := Charter.maxSeats
def maxRes : Nat := Charter.maxResources
/-- Kinds of piece, of any placement, counting those a law adds. -/
def maxKinds : Nat := Charter.maxPieceKinds
def maxSpots : Nat := Charter.maxSpots
def maxLaws : Nat := Charter.maxLawsInForce
/-- Rows of `places`, the table of legal placements. When more placements are legal, the first this many in
`placeOrder` have rows, and `place_overflow` is 1. A turn always has another action (end turn), and a setup turn
always has one row, so a seat is never left without a legal action. -/
def maxPlaceRows : Nat := 128
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
  /-- The numbers in one row. Kept, so that writing a number does not add up the columns again. -/
  width : Nat := (cols.map Cols.width).sum
  deriving Inhabited

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
      , "dice_top", "last_roll", "actions_used", "setup_step", "turn_pos", "my_pos", "laws", "moves_overflow"
      , "places", "place_overflow", "spots", "links" ] }

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

/-- One row per spot. A spot's links and tiles are counted here, since they have no table. -/
def tSpots : Table :=
  { name := "spots", rows := maxSpots
    cols := ones
        [ "real", "x", "y", "degree", "pips", "goods", "tiles", "demand_value", "new_for_me", "free", "reach_me"
        , "occupied", "piece_points", "piece_yield", "attached", "links_open", "links_mine" ]
      ++ across .seats ["owner", "links_of"] ++ across .res ["pips_by_res"] }

def tLaws : Table :=
  { name := "laws", rows := maxLaws, cols := ones (["real", "founding"] ++ lawShape) }

def tProposal : Table :=
  { name := "proposal", rows := 1
    cols := ones (["real"] ++ lawShape ++ ["yes_count", "yes_needed", "deciding", "previewed", "ends_game", "bank_rate_change"])
      ++ across .seats ["by", "voted_yes", "voted_no", "next_turn_net", "now_net", "points_change"]
      ++ across .res ["next_turn_my_net"] ++ across .kinds ["cost_change"] }

/-- One row per legal placement, in `placeOrder`. Action `actPlace + i` places row `i`'s piece. For a piece on a
spot, `at` is the spot; for one on a link, `at` and `at_b` are its ends, and the spot columns are those of the end
with more pips that is free (or of `at` if neither is). Spot numbers are on the scale of `maxSpots`, so a
row can be matched with its rows of `spots`, which have the pips by resource. -/
def tPlaces : Table :=
  { name := "places", rows := maxPlaceRows
    cols := ones
        [ "real", "on_link", "on_spot", "on_upgrade", "on_attach", "at", "at_b", "x", "y", "pips", "goods"
        , "demand_value", "new_for_me", "free_ends", "reach_me", "points_gain", "yield_gain", "cost_total", "my_short" ]
      ++ across .kinds ["kind"] }

/-- The tables of every observation, in order. -/
def baseTables : List Table := [tGlobal, tSeats, tResources, tKinds, tSpots, tLaws, tProposal, tPlaces]

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

One flat list: end turn, the two votes, bank trades by row of `resources`, declarations by row and level, and a
placement by its row of `places`. Offers and deals have no action yet, and a later version can add them at the end.
-/

def actEnd : Nat := 0
def actVoteNo : Nat := 1
def actVoteYes : Nat := 2
def actBank : Nat := 3
def actDeclare : Nat := actBank + maxRes * maxRes
def actPlace : Nat := actDeclare + maxRes * declareLevels.size
def actSize : Nat := actPlace + maxPlaceRows

#guard baseSize == 11465
#guard actSize == 515

end CharterServer.Policy
