import Charter.Games.Omerta
import Charter.Scene.Render
import Charter.Games.Omerta.Meshes

/-!
# How Omertà looks

A 1950s city at night. Each tile is a city block. Streets run along its sides, and a kerb and a sidewalk
run inside them. The middle tile is the piazza, with a fountain, where the laws' monuments stand. A wine
block has vines and a cellar, a cement block has a building yard, and a fish block has a quay, a boat and
a market stall. The meshes come from `packs/omerta/gen.py`.

Every piece a seat owns shows the seat's colour, and also a second mark that does not need colour: a
column of pale crates beside a building or a back room, and dark crossing bars on a street. Seat 1 has
none, seat 2 has one, seat 3 has two and seat 4 has three.

The treasury is the district attorney's desk. The reward for talking is the heap of cash on it: one
bundle for each cash, up to 50.
-/

namespace Charter.Games.Omerta
open Charter.Scene GpuCmd
open Meshes

/-- Seat colours that show against dark streets: crimson, gold, cream, emerald, violet and orange. -/
def seats : List UInt32 := [0xF23A4E, 0xF2C230, 0xF3ECDA, 0x22B573, 0xB477FF, 0xFF7A1F]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- The warm light of a street lamp. -/
def lampLight : UInt32 := 0xFFD98A

/-- The pale crates by an owned building or back room: none for seat 1, then one, two or three. -/
def tell (s : Nat) (x z : Float) : List Part :=
  (List.range (s % 4)).map fun i => box x (0.046 * i.toFloat) z 0.044 0.044 0.044 0xD9B77A (0.3 * i.toFloat)

#guard (tell 0 0 0).length == 0
#guard (tell 3 0 0).length == 3

/-- A street: cobbles in the seat's colour between kerb stones, and dark crossing bars by seat. -/
def streetModel (s : Nat) : List Part :=
  let bars : List Float := match s % 4 with
    | 0 => []
    | 1 => [0.2]
    | 2 => [0.17, 0.23]
    | _ => [0.14, 0.2, 0.26]
  [m streetBody 0 0 0, m streetTint 0 0 0 (seat s)] ++ bars.map fun u => box u 0.014 0 0.022 0.004 0.11 0x1A1A1E

/-- A link piece that a law made: a police barricade. -/
def barricadeModel (s : Nat) : List Part :=
  [m barricade 0 0 0 (seat s)]

/-- A front: a corner shop with awnings in the seat's colour. -/
def frontModel (_seed s _round : Nat) : List Part :=
  [m frontBody 0 0 0, m frontTint 0 0 0 (seat s)] ++ tell s 0.13 0.0

/-- A club: a nightclub with a marquee and a glowing neon tower in the seat's colour. -/
def clubModel (_seed s _round : Nat) : List Part :=
  [m clubBody 0 0 0, m clubTint 0 0 0 (seat s), m clubNeon 0 0 0 (seat s)] ++ tell s (-0.2) 0.0

/-- A racket: a back room, with a rug, a card table's felt and a lampshade in the seat's colour. -/
def racketModel (s : Nat) : List Part :=
  [m racketBody 0 0 0, m racketTint 0 0 0 (seat s)] ++ tell s 0.0 0.13

/-- A piece that a law made. The name's hash picks the shape: a phone booth, a newsstand or a truck. -/
def madeModel (name : String) (s : Nat) : List Part :=
  let id := match hashText name % 3 with
    | 0 => madeBooth
    | 1 => madeKiosk
    | _ => madeTruck
  [m id 0 0 0 (seat s)] ++ tell s 0.13 0.0

/-- The top of a tile, by resource. A tile turns by a sixth or not at all, so its tall things stay at the
back, behind the token. -/
def tileTop (res : Option Res) (seed : Nat) : List Part :=
  let turned : Float := pickFrom [0.0, pi / 3.0, -pi / 3.0] seed 3
  match res with
  | some "wine" => [m tileWine 0 0 0 0xFFFFFF 1 turned]
  | some "cement" => [m tileCement 0 0 0 0xFFFFFF 1 turned]
  | some "fish" => [m tileFish 0 0 0 0xFFFFFF 1 turned]
  | _ => [m tilePiazza 0 0 0]

/-- Small things on a tile: street lamps on the sidewalk, and on some blocks cement bags or crates of
fish. A lamp goes when a piece takes the corner next to it. No lamp stands in front of the token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let lamps := (List.range 6).flatMap fun i =>
    if (seed / 7 + i) % 3 != 0 then [] else
    let a := pi / 2.0 - pi / 3.0 * i.toFloat + 0.33
    let (x, z) := (0.67 * Float.cos a, 0.67 * Float.sin a)
    if keep x z && !hidesToken x z then [m lampPost x 0 z 0xFFFFFF 1 (0 - a), m lampGlow x 0 z lampLight 1 (0 - a)] else []
  let small (id : UInt32) : List Part :=
    ((scatter seed 4 0.34 0.52).filter fun (x, z, _) => keep x z && x + z > 0.25).map fun (x, z, i) =>
      m id x 0 z 0xFFFFFF 1 (6.28 * rnd seed (i + 9))
  lamps ++ match res with
    | some "cement" => small decoBags
    | some "fish" => small decoCrates
    | _ => []

/-- A law's monument, by what the law is about. -/
def lawMonument : MonumentKind → List Part
  | .cost => [m monCost 0 0 0]
  | .points => [m monPoints 0 0 0]
  | .bank => [m monBank 0 0 0]
  | .harvest => [m monHarvest 0 0 0]
  | .build => [m monBuild 0 0 0]
  | .roundEnd => [m monRound 0 0 0]
  | .roll => [m monRoll 0 0 0]
  | .newPiece _ => [m monPiece 0 0 0]
  | .repeal => [m monRepeal 0 0 0]

/-- The floor directions as the viewer sees them: `u` to the right, `v` away from the viewer. -/
def cityAt (u v : Float) : Float × Float := (0.7071 * (u - v), -0.7071 * (u + v))

/-- A mesh placed on the table by `u` and `v`. -/
def onTable (id : UInt32) (u v : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (r : Float := 0) : Cmd :=
  let (x, z) := cityAt u v
  (m id x 0.012 z rgb k r).at 0 0 0

/-- The night city round the board: asphalt with pools of lamplight, a ring road, tenements behind, the
harbour on the left, parked cars, and a patrol car waiting at the front. -/
def surround : List Cmd :=
  let lampCmds := Meshes.lamps.flatMap fun (u, v) =>
    [onTable lampPost u v 0xFFFFFF 1.8, onTable lampGlow u v lampLight 1.8]
  -- A car's nose points along +u when it is turned a quarter of a half turn.
  let along := pi / 4.0
  let parked := [(2.0, -5.35, 0x2A2A30), (-1.4, 5.4, 0x6A1E28), (6.1, 2.9, 0xD8CCB0), (-4.75, -1.9, 0x2E5A5E), (4.6, -5.0, 0x3A3A44)]
  let cars := parked.map fun (u, v, c) =>
    onTable sedan u v c 1.8 (if u < -4.0 then 3.0 * pi / 4.0 else if v > 0 then along + pi else along)
  [ (box 0 0 0 90 0.003 90 0x0B0C10).at 0 0 0
  , (m cityGround 0 0 0).at 0 0 0
  , (m skyline 0 0 0).at 0 0 0
  , (m harbour 0 0 0).at 0 0 0
  , onTable policeCar (-4.1) (-5.0) 0xFFFFFF 1.8 along
  , onTable policeLight (-4.1) (-5.0) 0xFF3030 1.8 along ] ++ lampCmds ++ cars

/-- A dark kerb round the city's edge, so the blocks read as one city. -/
def under (ts : List Charter.Games.TileDef) : List Cmd :=
  ts.map fun t =>
    let (x, z) := t.hex.toPixel 1.0
    .draw mLand { pos := vec3 x 0.012 z, scale := vec3 1.1 0.1 1.1 } 0x3A3A40 0

/-- A red fire hydrant by a street, after some rounds, and sometimes a parked car. -/
def roadside (seed : Nat) : List Part :=
  let side := if seed % 2 == 0 then 1.0 else -1.0
  let hydrant := [cyl (0.22 * side) 0 (0.2 * side) 0.014 0.032 0xB8232F, ball (0.22 * side) 0.034 (0.2 * side) 0.022 0xB8232F]
  if seed % 4 == 0 then
    hydrant ++ [m sedan (-0.1 * side) 0.012 0 (pickFrom [0x2A2A30, 0x6A1E28, 0xD8CCB0, 0x2E5A5E] seed 5) 1 (if side > 0 then 0 else pi)]
  else hydrant

/-- The treasury is the district attorney's desk. The reward heaps up on it as bundles of cash. -/
def rewardDesk (total : Nat) : List Part :=
  let heap := (cashSlots.take (min total 50)).map fun (x, y, z, r) => m cashBundle x y z 0xFFFFFF 1 r
  -- Moved toward the board a little, so a narrow window still shows the whole desk.
  ([m daDesk 0 0 0, m daLamp 0 0 0 0xB8F0A8] ++ heap).map fun p => { p with z := p.z + 0.35 }

#guard (rewardDesk 0).length == 2
#guard (rewardDesk 12).length == 14
#guard (rewardDesk 90).length == 52

def theme : Theme :=
  { tableColor := 0x0B0C10
    ground := fun
      | some "wine" => 0x5A2A3A
      | some "cement" => 0x8E8A82
      | some "fish" => 0x2A5E70
      | _ => 0xB8A88A
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := surround
    under := under
    shape := fun k => if k == "front" then some .settlement else if k == "club" then some .city else none
    smallModel := frontModel
    largeModel := clubModel
    linkModel := fun k s => if k == "street" then streetModel s else barricadeModel s
    harbours := false
    ownModel := fun k s => if k == "racket" then some (racketModel s) else none
    madeModel := madeModel
    -- Away from the front's corner and never toward the viewer, so a back room keeps off the token.
    attachAngles := [-3.0 * pi / 4.0, -pi / 4.0, 3.0 * pi / 4.0]
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [m hotRing 0 0 0]
    monumentModel := lawMonument
    square := [m squareFountain 0 0 0, m squareWater 0 0 0 0xCFEFFF]
    roadside := roadside
    treasury := rewardDesk
    flat := fun
      | some "wine" => 0x8A2A50
      | some "cement" => 0xA8A49A
      | some "fish" => 0x2A7A96
      | _ => 0xD2C2A0
    look :=
      { tagline := "Everybody swears. Somebody talks."
        bodyFont := "book"
        displayFont := "typewriter"
        tokens :=
          [ ("walnut-0", "#0b0b10"), ("walnut-1", "#15131b"), ("walnut-2", "#201c28"), ("walnut-3", "#2e2938"), ("brass", "#b08a3e")
          , ("vellum", "#efe4c9"), ("vellum-2", "#e4d5b0"), ("vellum-3", "#cdb98c")
          , ("ink", "#1d1714"), ("ink-2", "#4d3f33"), ("ink-3", "#6e5d49")
          , ("gold", "#e2b13c"), ("gold-2", "#f5d27a"), ("gold-ink", "#241803")
          , ("wax", "#9e1b2a"), ("wax-2", "#c4283a"), ("wax-0", "#6e0f1b"), ("pale", "#ece2cc"), ("pale-2", "#a8a3b4")
          , ("sign-ink", "#7c111c"), ("act-hover", "#2e2a3a"), ("act-hover-2", "#24212e"), ("field", "#f6edd6")
          , ("bright", "#fff8e8"), ("err-ink", "#fff2f2"), ("tool-off", "#6f6a7c"), ("need", "#c8c0a8")
          , ("good", "#1f7a52"), ("stain", "#6d5228")
          , ("roll-0", "#3a2226"), ("roll-1", "#55333a"), ("roll-2", "#70484a"), ("roll-3", "#8a6058"), ("roll-4", "#a27a68")
          , ("roll-5", "#b9967e"), ("roll-6", "#cdb294"), ("roll-7", "#e0ccac"), ("roll-8", "#f2e6c6") ]
        marks := []
        quietPieces := ["street"]
        icons :=
          [ ("wine", [ { d := "M10 2h4v4c0 1 3 2.5 3 6v8.5a1.5 1.5 0 0 1-1.5 1.5h-7A1.5 1.5 0 0 1 7 20.5V12c0-3.5 3-5 3-6z", fill := "#5a1630", stroke := "#23070f", width := 1.3 }
                     , { d := "M7.5 13h9v5h-9z", fill := "#efe2bf" }
                     , { d := "M10 2h4v2.5h-4z", fill := "#c9a24a" } ])
          , ("cement", [ { d := "M5 6c0-2 2-3 7-3s7 1 7 3l1 13c0 1.5-1 2-2 2H6c-1 0-2-.5-2-2z", fill := "#c9c2b0", stroke := "#4a463e", width := 1.3 }
                       , { d := "M4.6 11h14.8v4H4.6z", fill := "#8e8a82" }
                       , { d := "M8 6h8", stroke := "#4a463e", width := 1.1 } ])
          , ("fish", [ { d := "M3 12c3-5 9-6 13-3l5-4v14l-5-4c-4 3-10 2-13-3z", fill := "#7fa6b8", stroke := "#1f3a48", width := 1.3 }
                     , { d := "M7 10.3a1.1 1.1 0 1 0 .01 0z", fill := "#1f3a48" }
                     , { d := "M10.5 9c1 2 1 4 0 6", stroke := "#1f3a48", width := 1 } ])
          , ("cash", [ { d := "M5 4h16v9H5z", fill := "#4f8a48", stroke := "#1c3a1a", width := 1.2 }
                     , { d := "M3 9h16v11H3z", fill := "#79b867", stroke := "#1c3a1a", width := 1.2 }
                     , { d := "M9 9h4v11H9z", fill := "#f2e6c4", stroke := "#1c3a1a", width := 0.8 }
                     , { d := "M5.5 14.5a1.3 1.3 0 1 0 .01 0zM16.5 14.5a1.3 1.3 0 1 0 .01 0z", fill := "#1c3a1a" } ])
          , ("dirt", [ { d := "M6 2.5h11v9H6z", fill := "#f4f0e6", stroke := "#3a3028", width := 1 }
                     , { d := "M7.5 4h8v6h-8z", fill := "#3a3a40" }
                     , { d := "M3 8h18v13H3z", fill := "#d9b46a", stroke := "#5a4220", width := 1.3 }
                     , { d := "M3 8l9 6 9-6", stroke := "#5a4220", width := 1.2 }
                     , { d := "M12 13a1.5 1.5 0 1 0 .01 0z", fill := "#a81d24" } ])
          , ("street", [ { d := "M7 22l3-20h4l3 20z", fill := "currentColor" }
                       , { d := "M12 4v3M12 10v3M12 16v3", stroke := "#1a1a1e", width := 1.4 } ])
          , ("front", [ { d := "M4 21V4h16v17z", fill := "currentColor", opacity := 0.7 }
                      , { d := "M3 10h18v2.5c-1.5 1.5-3 1.5-4.5 0-1.5 1.5-3 1.5-4.5 0-1.5 1.5-3 1.5-4.5 0-1.5 1.5-3 1.5-4.5 0z", fill := "currentColor" }
                      , { d := "M6 15h7v4H6zM15 14.5h3V21h-3z", fill := "#000000", opacity := 0.55 } ])
          , ("club", [ { d := "M2 21V8h15v13z", fill := "currentColor" }
                     , { d := "M18.5 2.5H22V17h-3.5z", fill := "currentColor" }
                     , { d := "M1 13h17v2.2H1z", fill := "currentColor", stroke := "#000000", width := 0.8 }
                     , { d := "M4 10h3v1.8H4zM9 10h3v1.8H9zM13.5 10h2v1.8h-2zM7.5 17h4v4h-4zM19.5 5h1.5v2h-1.5zM19.5 9h1.5v2h-1.5zM19.5 13h1.5v2h-1.5z", fill := "#000000", opacity := 0.55 } ])
          , ("racket", [ { d := "M8 1.5h10a2 2 0 0 1 2 2v13", stroke := "currentColor", width := 1.4 }
                       , { d := "M5 4h10a2 2 0 0 1 2 2v13a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2z", fill := "currentColor" }
                       , { d := "M10 7.5c2 2.5 4.5 4 4.5 6a2.2 2.2 0 0 1-3.8 1.5l.8 2.5h-3l.8-2.5A2.2 2.2 0 0 1 5.5 13.5c0-2 2.5-3.5 4.5-6z", fill := "#000000", opacity := 0.65 } ]) ] } }

end Charter.Games.Omerta
