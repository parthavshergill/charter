import Charter.Engine
import Charter.Games.Island
import Charter.Scene.OfState
import Server.Preview

/-!
`charter-measure`: how long the worst turn takes.

Every limit in `Charter/Words/Game.lean` keeps a turn fast, so its number must come from a measurement.
This program builds a game at the limits it is told to try: the Island's map, every seat with its pieces
on the corners that one roll pays, and every law as big as the limits allow, all reacting to each payment.
It then plays turns and times the slow parts of the last turn: the turn change, the moves the screen
lists, and a preview. The state is built directly, so nothing here needs the limits to be in force.
-/

namespace CharterServer.Measure
open Charter

structure Options where
  seats : Nat := 6
  resources : Nat := maxResources
  kinds : Nat := maxPieceKinds
  stock : Nat := maxStock
  laws : Nat := maxLawsInForce
  lawSize : Nat := maxLawSize
  entries : Nat := maxPlannedEntries
  total : Nat := maxPlannedTotal
  rounds : Nat := maxRoundsAllowed

def parseArgs : List String → Options → Options
  | "--seats" :: n :: r, o => parseArgs r { o with seats := n.toNat?.getD o.seats }
  | "--resources" :: n :: r, o => parseArgs r { o with resources := n.toNat?.getD o.resources }
  | "--kinds" :: n :: r, o => parseArgs r { o with kinds := n.toNat?.getD o.kinds }
  | "--stock" :: n :: r, o => parseArgs r { o with stock := n.toNat?.getD o.stock }
  | "--laws" :: n :: r, o => parseArgs r { o with laws := n.toNat?.getD o.laws }
  | "--law-size" :: n :: r, o => parseArgs r { o with lawSize := n.toNat?.getD o.lawSize }
  | "--entries" :: n :: r, o => parseArgs r { o with entries := n.toNat?.getD o.entries }
  | "--total" :: n :: r, o => parseArgs r { o with total := n.toNat?.getD o.total }
  | "--rounds" :: n :: r, o => parseArgs r { o with rounds := n.toNat?.getD o.rounds }
  | _ :: r, o => parseArgs r o
  | [], o => o

def resName (i : Nat) : Res := s!"res{i}"

/-- The Island's map with this many resources, and every extra kind of piece attached to a settlement. -/
def benchGame (o : Options) : GameDef :=
  let names := (List.range o.resources).map resName
  let island := Games.Island.island
  { island with
    name := "Measure"
    resources := names.map fun r => ⟨r, o.stock⟩
    pieces :=
      [ { name := "road", cost := [(resName 0, 1)], points := 0, placement := .link, yield := 0, limit := 15 }
      , { name := "settlement", cost := [(resName 0, 1)], points := 0, placement := .spot, yield := 1, limit := 5 }
      , { name := "city", cost := [(resName 1, 1)], points := 0, placement := .upgrade "settlement", yield := 2, limit := 4 } ] ++
      (List.range (o.kinds - 3)).map fun i =>
        { name := s!"extra{i}", cost := [(resName 2, 1)], points := 0, placement := .attach "settlement", yield := 1, limit := 5 }
    map := { island.map with
      regions := island.map.regions.map fun x =>
        { x with res := resName (x.number % o.resources) } }
    targetPoints := 1000000
    rounds := o.rounds }

/-- A number that reads holdings and has this size. -/
def bigAmount (size : Nat) (r : Res) : Expr :=
  (List.range (size / 4)).foldl (fun e _ => .add e (.min (.holding .each (.lit r)) (.lit 0))) (.lit 1)

/-- One law that reacts to each payment. It asks for `want` entries at this many seats and has about
`size` nodes: every seat pays the treasury, with amounts that read holdings, and any spare size goes into
those numbers. -/
def bigLaw (o : Options) (i want size : Nat) : Law :=
  let groups := max 1 (want / o.seats)
  let perTransfer := (size - 2) / groups
  -- Money goes round, so that the game keeps moving it however long it runs.
  let body : List Effect := (List.range groups).map fun j =>
    let r := resName ((i + j) % o.resources)
    match (i + j) % 3 with
    | 0 => .transfer .each .treasury (.lit r) (bigAmount perTransfer r)
    | 1 => .transfer .treasury .each (.lit r) (bigAmount perTransfer r)
    | _ => .transfer .each .bank (.lit r) (bigAmount perTransfer r)
  { title := s!"Law {i}", clauses := [.onHarvest [.forEach .yes body]] }

/-- As many laws as allowed, sharing out the total of entries as evenly as they can. -/
def benchLaws (o : Options) : List (Nat × Law) :=
  let base := min o.entries (o.total / max 1 o.laws)
  let groups := max 1 (base / o.seats)
  let spare := (o.total - min o.total (o.laws * groups * o.seats)) / o.seats
  (List.range o.laws).map fun i =>
    let extra := if i < spare then o.seats else 0
    (i, bigLaw o i (min o.entries (groups * o.seats + extra)) o.lawSize)

/-- As many corners as can hold a settlement, with no two neighbours. -/
def freeCorners (G : GameDef) : List Nat :=
  let near (a b : Nat) : Bool :=
    G.map.links.any fun l => (l.1 == a && l.2 == b) || (l.1 == b && l.2 == a)
  (List.range G.map.spotCount).foldl (fun acc v => if acc.any (near v) then acc else acc ++ [v]) []

/-- A game in the actions phase. Every seat holds a lot, and has a settlement on as many corners as it can,
with every extra kind of piece on each one. So most rolls pay many pieces. -/
def benchState (o : Options) : State (benchGame o) :=
  let G := benchGame o
  let s := initialState G o.seats 1 [1]
  let seats := List.range o.seats
  let names := (List.range o.resources).map resName
  let hands : List Entry := seats.flatMap fun p => names.map fun r =>
    { src := .bank, dst := .player p, res := r, amount := o.stock / (2 * o.seats), reason := .trade }
  let extras := (List.range (o.kinds - 3)).map fun i => s!"extra{i}"
  let spots := freeCorners G
  let pieces : List Piece := (spots.zipIdx.take (5 * o.seats)).flatMap fun (v, i) =>
    let owner := i % o.seats
    (⟨owner, "settlement", .spot v⟩ : Piece) :: extras.map fun k => (⟨owner, k, .spot v⟩ : Piece)
  { s with
    phase := .actions
    books := (s.books.postAll hands).getD s.books
    pieces := pieces
    laws := benchLaws o }

/-- Time one thing, in milliseconds. `force` makes sure the answer is really computed. -/
def timed {α : Type} (act : Unit → α) (force : α → Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let x := act ()
  let n := force x
  let t1 ← IO.monoMsNow
  return (t1 - t0, n)

def run (o : Options) : IO UInt32 := do
  let G := benchGame o
  let s0 := benchState o
  IO.println s!"seats {o.seats}, resources {o.resources}, kinds {o.kinds}, stock {o.stock}, laws {o.laws}, law size {o.lawSize}, entries per law {o.entries}, total {o.total}, rounds {o.rounds}"
  IO.println s!"laws built: size {(s0.laws.head?.map (·.2.size)).getD 0}, entries per law {(s0.laws.head?.map (·.2.plannedEntries o.seats)).getD 0}, total {plannedTotal s0.laws o.seats}, reads {readsTotal s0.laws o.seats}, pieces {s0.pieces.length}, paid on a 6: {(baseHarvest s0 6).length}"
  let mut s := s0
  let mut worst := 0
  let turns := o.rounds * o.seats
  let budgetMs := 60000
  let startedMs ← IO.monoMsNow
  let mut played := 0
  for _ in List.range turns do
    let nowMs ← IO.monoMsNow
    if nowMs - startedMs > budgetMs then break
    if s.phase == .ended then break
    let t0 ← IO.monoMsNow
    match Engine.step G s .forceEndTurn with
    | .error m => IO.println s!"rejected: {m}"; return 1
    | .ok s' =>
      s := s'
      played := played + 1
      let t1 ← IO.monoMsNow
      if t1 - t0 > worst then worst := t1 - t0
  IO.println s!"played {played} of {turns} turns: journal {s.journal.length} entries, slowest turn change {worst} ms"
  -- Now the other slow parts, on the first state, when every seat holds most, and on the last.
  let names : Nat → String := fun i => s!"Seat {i}"
  let law := bigLaw o 99 (min o.entries 12) 40
  for (label, x) in [("first", { s0 with turnIndex := 1 }), ("last", ({ s with phase := .actions, turnIndex := 1, pieces := s0.pieces } : State G))] do
    let (ms, n) ← timed (fun () => harvestEntries x 6) List.length
    IO.println s!"{label} state: harvest on a 6: {ms} ms for {n} entries"
    let (ms, n) ← timed (fun () => Engine.legalMoves G x 1) List.length
    IO.println s!"{label} state: legal moves: {ms} ms for {n} moves"
    let (ms, n) ← timed (fun () => (Preview.lawPreview x 999 law (some 1) names).compress) String.length
    IO.println s!"{label} state: one preview: {ms} ms for {n} bytes"
  return 0

end CharterServer.Measure

def main (args : List String) : IO UInt32 := do
  let o := CharterServer.Measure.parseArgs args {}
  -- The server's requests run on threads like this one.
  let t ← IO.asTask (prio := .dedicated) (CharterServer.Measure.run o)
  match t.get with
  | .ok code => return code
  | .error e => IO.eprintln s!"{e}"; return 1
