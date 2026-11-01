import GpuCmd

/-!
# Second use case: a 3D bar chart

Writes two scene streams with different data (`barchart-a.gpc`, `barchart-b.gpc`)
into the directory given as the first argument (default `examples`).
`examples/index.html` loads them and toggles between them, so the player's
tweens are visible.

Run: `lake exe bar-chart-demo examples`
-/

open GpuCmd

def months : List String :=
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- Monthly rainfall in mm (illustrative numbers). -/
def seriesA : List (String × UInt32 × List Float) :=
  [("Lisbon", 0x3E7CB1, [100, 87, 61, 64, 47, 14, 4, 6, 33, 91, 120, 128]),
   ("Dublin", 0x5FA36A, [69, 51, 51, 54, 55, 56, 50, 71, 59, 70, 72, 76]),
   ("Mumbai", 0xE07A3F, [1, 0, 0, 1, 11, 500, 840, 520, 300, 90, 10, 2])]

def seriesB : List (String × UInt32 × List Float) :=
  [("Lisbon", 0x3E7CB1, [80, 95, 70, 50, 40, 20, 8, 10, 45, 110, 100, 140]),
   ("Dublin", 0x5FA36A, [80, 60, 45, 60, 50, 66, 60, 80, 50, 85, 90, 70]),
   ("Mumbai", 0xE07A3F, [3, 1, 2, 4, 30, 420, 700, 610, 350, 60, 20, 4])]

def barMesh : UInt32 := 1
def floorMesh : UInt32 := 2

/-- Pick id of a bar: `series * 100 + month + 1` (stable across frames). -/
def barPick (s m : Nat) : UInt32 := (s * 100 + m + 1).toUInt32

def scene (data : List (String × UInt32 × List Float)) : List Cmd := Id.run do
  let gap : Float := 1.2
  let rowGap : Float := 1.6
  let maxV := data.foldl (fun acc (_, _, vs) => vs.foldl max acc) 1
  let height (v : Float) : Float := 0.05 + 6.0 * v / maxV
  let x0 := -(gap * 11) / 2
  let z0 := -(rowGap * (data.length.toFloat - 1)) / 2
  let mut cs : List Cmd :=
    [.clear 0x241A12,
     .camera (vec3 9 11 15) (vec3 0 2 0) 40,
     .light (vec3 (-0.5) (-1) (-0.35)) 1.0,
     .defineMesh barMesh (.box 0.8 1 0.8),
     .defineMesh floorMesh (.box 1 0.08 1),
     .draw floorMesh { pos := vec3 0 0 0, scale := vec3 (gap * 12 + 0.6) 1 (rowGap * data.length.toFloat + 0.6) }
       0xD9C7A7 0]
  -- the tallest bar of each series gets highlighted
  let mut highlights : List Cmd := []
  for (s, (name, color, vs)) in (List.range data.length).zip data do
    let z := z0 + rowGap * s.toFloat
    cs := cs ++ [.label name (vec3 (x0 - 1.6) 0.4 z) 0.45 0xF4E9D8 0]
    let best := vs.foldl max 0
    for (m, v) in (List.range vs.length).zip vs do
      let x := x0 + gap * m.toFloat
      let t : Transform := { pos := vec3 x 0.08 z, scale := vec3 1 (height v) 1 }
      cs := cs ++ [.draw barMesh t color (barPick s m)]
      if v == best then
        highlights := highlights ++ [.highlight (barPick s m) 0xFFD27A,
          .label s!"{v.toUInt32} mm" (vec3 x (0.08 + height v + 0.45) z) 0.32 0xFFE7B0 (barPick s m)]
  for (m, name) in (List.range months.length).zip months do
    cs := cs ++ [.label name (vec3 (x0 + gap * m.toFloat) 0.3 (z0 + rowGap * data.length.toFloat)) 0.36 0xE8D9C0 0]
  return cs ++ highlights

def main (args : List String) : IO Unit := do
  let dir := args.headD "examples"
  for (file, data) in [("barchart-a.gpc", seriesA), ("barchart-b.gpc", seriesB)] do
    let cmds := scene data
    let bytes := encode cmds
    -- sanity: the stream decodes back to the same commands (proved; checked here too)
    if decode bytes != some cmds then throw <| IO.userError "round trip failed"
    IO.FS.writeBinFile (System.FilePath.mk dir / file) bytes
    IO.println s!"wrote {dir}/{file}: {cmds.length} commands, {bytes.size} bytes"
