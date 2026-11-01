import HexGrid
/-!
Second use case (not a game): shortest paths on a hex map with obstacles.

A field robot moves between hex cells of a survey area (radius 4). Some
cells are blocked (rocks). We compute breadth-first distances from a base
cell, print an ASCII map, and compare with the straight-line hex distance.
-/
open HexGrid

def area : List Hex := hexagon 4

def blocked (h : Hex) : Bool :=
  -- a wall along q = 1 for r in [-3, 1], and a rock cluster
  (h.q == 1 && h.r ≥ -3 && h.r ≤ 1) || h == ⟨-2, 3⟩ || h == ⟨-1, 2⟩

def passable (h : Hex) : Bool := area.contains h && !blocked h

/-- Breadth-first search; `fuel` bounds the number of rounds. -/
def bfs (start : Hex) (fuel : Nat) : List (Hex × Nat) :=
  go fuel [start] [(start, 0)] 0
where
  go : Nat → List Hex → List (Hex × Nat) → Nat → List (Hex × Nat)
  | 0, _, seen, _ => seen
  | _ + 1, [], seen, _ => seen
  | fuel + 1, frontier, seen, d =>
    let next := frontier.flatMap Hex.neighbors |>.filter fun n =>
      passable n && !(seen.any fun p => p.1 == n)
    let next := next.foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []
    go fuel next (seen ++ next.map (·, d + 1)) (d + 1)

def lookup (t : List (Hex × Nat)) (h : Hex) : Option Nat :=
  (t.find? (·.1 == h)).map (·.2)

def cell (t : List (Hex × Nat)) (h : Hex) : String :=
  if blocked h then " ## "
  else match lookup t h with
    | some d => if d < 10 then s!"  {d} " else s!" {d} "
    | none => "  . "

/-- Render rows r = -4..4 (north to south). Only cells inside the area are
printed; row `r` is indented by `2 * |r|` so the pointy-top stagger shows. -/
def render (t : List (Hex × Nat)) : String := Id.run do
  let mut out := ""
  for i in [0:9] do
    let r : Int := i - 4
    let mut line := String.ofList (List.replicate (2 * r.natAbs) ' ')
    for j in [0:9] do
      let h : Hex := ⟨(j : Int) - 4, r⟩
      if area.contains h then line := line ++ cell t h
    out := out ++ line ++ "\n"
  return out

def main : IO Unit := do
  let base : Hex := ⟨-2, 0⟩
  let goal : Hex := ⟨3, -1⟩
  let t := bfs base 100
  IO.println s!"Survey area: {area.length} cells, {(area.filter blocked).length} blocked"
  IO.println s!"BFS distances from base {repr base}:"
  IO.print (render t)
  let reach := (t.filter fun p => passable p.1).length
  IO.println s!"Reachable cells: {reach}"
  IO.println s!"Straight-line distance base→goal: {base.dist goal}"
  IO.println s!"Path length around the wall:      {(lookup t goal).getD 0}"
  -- every BFS distance is at least the hex distance (sanity check)
  let ok := t.all fun p => base.dist p.1 ≤ p.2
  IO.println s!"BFS ≥ hex distance everywhere: {ok}"
