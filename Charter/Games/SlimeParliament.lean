import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render
import Charter.Games.SlimeParliament.Meshes

/-!
# Slime Parliament

Rival slime moulds share a damp log, and they govern it. Towns are pulsing nodes, roads are tendrils, a
large piece is a swollen node in a Speaker's wig, and each law in force grows as a fruiting body in the
chamber at the middle of the log. The rules are a small game with four founding laws. Balance is not
the point.

The look uses mesh files. `packs/slime-parliament/gen.py` makes them and writes `Meshes.lean`.
-/

namespace Charter.Games.SlimeParliament

open HexGrid

/-! ## The map: a long log, not a round island -/

/-- The chamber first, because the laws' monuments stand on the first tile. The rest lie along the log,
which runs from the viewer's left to the right. -/
def hexes : List Hex :=
  [ ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨2, -1⟩, ⟨-2, 1⟩, ⟨2, -2⟩, ⟨-2, 2⟩
  , ⟨1, -2⟩, ⟨-1, 2⟩, ⟨3, -2⟩, ⟨-3, 2⟩, ⟨3, -1⟩, ⟨-3, 1⟩ ]

def tileResources : List Res :=
  [ "oatmeal", "dew", "rot", "pollen", "dew", "oatmeal", "pollen", "rot"
  , "oatmeal", "rot", "dew", "pollen", "rot", "oatmeal", "pollen", "dew" ]

def tileNumbers : List Nat :=
  [ 6, 8, 5, 9, 10, 4, 3, 11
  , 9, 5, 8, 6, 4, 10, 11, 3 ]

def tiles : List TileDef :=
  match hexes with
  | [] => []
  | center :: rest =>
    { hex := center, res := none, number := none } ::
      ((rest.zip (tileResources.zip tileNumbers)).map fun x =>
        { hex := x.1, res := some x.2.1, number := some x.2.2 })

def spots : List Vertex := spotsOf tiles
def edges : List Edge := sidesOf tiles
def links : List (Nat × Nat) := linksOf tiles

/-! ## The founding laws -/

def held (p : Party) (r : Res) : Expr := .holding p (.lit r)

/-- A puffball bursts when it is built, and everyone breathes it in. -/
def lawPuffball : Law :=
  { title := "A new puffball bursts, and every mould gets pollen"
    clauses := [.onBuild "puffball" [.forEach .yes [.transfer .bank .each (.lit "pollen") (.lit 1)]]] }

/-- Getting fat has a price. -/
def lawSwelling : Law :=
  { title := "A swelling mould feeds every mould behind it"
    clauses := [.onBuild "swelling" [.forEach (.lt (.points .each) (.points .actor)) [.transfer .actor .each (.lit "oatmeal") (.lit 1)]]] }

/-- No mould can sit on the water for ever. -/
def lawDew : Law :=
  { title := "Hoarded dew evaporates at the end of each round"
    clauses := [.onRoundEnd [.forEach (.lt (.lit 5) (held .each "dew")) [.transfer .each .treasury (.lit "dew") (.div (held .each "dew") 2)]]] }

/-- Good rot makes pollen. -/
def lawRot : Law :=
  { title := "Where rot is harvested, pollen comes with it"
    clauses := [.onHarvest [.when (.harvestedIs "rot") [.transfer .bank .actor (.lit "pollen") (.lit 1)]]] }

def foundingLaws : List Law := [lawPuffball, lawSwelling, lawDew, lawRot]

/-! ## The game -/

def game : GameDef where
  name := "Slime Parliament"
  resources := [⟨"oatmeal", 22⟩, ⟨"dew", 22⟩, ⟨"rot", 22⟩, ⟨"pollen", 22⟩]
  pieces :=
    [ { name := "tendril", cost := [("oatmeal", 1), ("dew", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "node", cost := [("oatmeal", 1), ("dew", 1), ("rot", 1)], points := 1
        placement := .spot, yield := 1, limit := 6 }
    , { name := "swelling", cost := [("oatmeal", 2), ("rot", 2)], points := 2
        placement := .upgrade "node", yield := 2, limit := 4 }
    , { name := "puffball", cost := [("pollen", 3), ("oatmeal", 1)], points := 1
        placement := .attach "node", yield := 0, limit := 2 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 10
  rounds := 24
  bankRate := 3
  setupPieces := ["node", "tendril"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look -/

section Look
open Charter.Scene GpuCmd
open Meshes

/-- Six slime moulds that stand out from the log: yellow, magenta, cyan, orange, violet and white. -/
def seats : List UInt32 := [0xF4D416, 0xE0267F, 0x12C4C4, 0xF2601E, 0x9A4DF0, 0xF2F2E6]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- Pale beads that differ by seat, so colour is not the only cue. -/
def tell (s : Nat) (h : Float) : List Part :=
  let beads : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.055, 0.055]
    | _ => [-0.08, 0, 0.08]
  beads.map fun u => ball (u - 0.04) (h - 0.45 * Float.abs u) (0.0 - u - 0.04) 0.052 0xF8F4E4

def nodeModel (_seed s _round : Nat) : List Part :=
  [m nodeBody 0 0 0 (seat s), m nodeEyes 0 0 0] ++ tell s 0.185

def swellingModel (_seed s _round : Nat) : List Part :=
  [m swellBody 0 0 0 (seat s), m swellWig 0 0 0, m swellEyes 0 0 0] ++ tell s 0.415

def puffballModel (s : Nat) : List Part :=
  [m puffBody 0 0 0 (seat s), m puffHead 0 0 0] ++ tell s 0.195

def tendrilModel (s : Nat) : List Part :=
  let marks : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.12, 0.12]
    | _ => [-0.22, 0, 0.22]
  m tendril 0 0 0 (seat s) :: marks.map fun u => ball u 0.045 0 0.065 0xF8F4E4

/-- A link piece that a law made: a thicker vein. -/
def thickVein (s : Nat) : List Part :=
  [{ m tendril 0 0 0 (seat s) with sy := 1.6, sz := 1.9 }, ball 0 0.08 0 0.07 0xF8F4E4]

/-- A piece that a law made. The name's hash picks the shape. -/
def madeModel (name : String) (s : Nat) : List Part :=
  let id := match hashText name % 3 with
    | 0 => madeA
    | 1 => madeB
    | _ => madeC
  [m id 0 0 0 (seat s)] ++ tell s 0.3

def tileMesh : Option Res → UInt32
  | some "oatmeal" => tileOats
  | some "dew" => tileDew
  | some "rot" => tileRot
  | some "pollen" => tileSpores
  | _ => tileChamber

def tileTop (res : Option Res) (seed : Nat) : List Part :=
  match res with
  | none => [m tileChamber 0 0 0]
  | _ => [m (tileMesh res) 0 0 0 0xFFFFFF 1 (pickFrom [0.0, pi / 3.0, -pi / 3.0, pi, 2.0 * pi / 3.0, -2.0 * pi / 3.0] seed 3)]

/-- Small things on a tile. The tall ones keep away from the number token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (lowOk : Bool) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n 0.42 0.74).filter fun (x, z, _) => keep x z && (lowOk || !hidesToken x z)).flatMap fun (x, z, i) => f x z i
  match res with
  | some "oatmeal" => at_ 7 true fun x z i => [m oat x 0 z 0xFFFFFF (0.8 + 0.5 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "dew" => at_ 6 true fun x z i => [m drop x (-0.005) z 0xFFFFFF (0.7 + 0.7 * rnd seed i)]
  | some "rot" => at_ 5 false fun x z i => [m toadstool x 0 z 0xFFFFFF (0.8 + 0.6 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "pollen" => at_ 6 false fun x z i => [m sporeling x 0 z 0xFFFFFF (0.8 + 0.5 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | _ => []

/-- A law's fruiting body, by what the law is about. -/
def fruiting : MonumentKind → List Part
  | .cost => [m fbCost 0 0 0]
  | .points => [m fbPoints 0 0 0]
  | .bank => [m fbBank 0 0 0]
  | .harvest => [m fbHarvest 0 0 0]
  | .build => [m fbBuild 0 0 0]
  | .roundEnd => [m fbRound 0 0 0]
  | .roll => [m fbRoll 0 0 0]
  | .newPiece _ => [m fbPiece 0 0 0]
  | .repeal => [m fbRepeal 0 0 0]

/-- The forest floor, the log, some leaves and toadstools. The floor covers the wooden table. -/
def surround : List Cmd :=
  let leaves := (List.range 30).map fun i =>
    let a := 2.399963 * i.toFloat
    let along := 12.0 * (rnd 51 i - 0.5)
    let across := (if i % 2 == 0 then 1.0 else -1.0) * (3.7 + 2.4 * rnd 52 i)
    let (x, z) := turn (pi / 4.0) along across
    (m leaf x 0.004 z 0xFFFFFF (0.6 + 0.6 * rnd 53 i) a).at 0 0 0
  let shrooms := (List.range 12).map fun i =>
    let along := 12.0 * (rnd 61 i - 0.5)
    let across := -(3.5 + 1.2 * rnd 62 i)
    let (x, z) := turn (pi / 4.0) along across
    (m toadstool x 0 z 0xFFFFFF (2.2 + 2.0 * rnd 63 i) (6.28 * rnd 64 i)).at 0 0 0
  [ (box 0 0 0 90 0.003 90 0x141A10).at 0 0 0
  , (m log 0 0 0 0xFFFFFF 1 (pi / 4.0)).at 0 0 0 ] ++ leaves ++ shrooms

/-- The treasury is a stump with a heap of oatmeal on it. -/
def reserve (total : Nat) : List Part :=
  let heap := (List.range (min total 40)).map fun i =>
    let a := 2.399963 * i.toFloat
    let r := 0.05 + 0.15 * Float.sqrt (i.toFloat / 40.0)
    m oat (r * Float.cos a) (0.34 + 0.012 * (i % 3).toFloat) (r * Float.sin a) 0xFFFFFF 1.1 a
  m stump 0 0 0 :: heap

def theme : Theme :=
  { tableColor := 0x10140C
    ground := fun
      | some "oatmeal" => 0x7C8C46
      | some "dew" => 0x2B6C74
      | some "rot" => 0x4A2A30
      | some "pollen" => 0xC47F26
      | _ => 0xAA8656
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := surround
    under := fun _ => []
    shape := fun k => if k == "node" then some .settlement else if k == "swelling" then some .city else none
    smallModel := nodeModel
    largeModel := swellingModel
    linkModel := fun k s => if k == "tendril" then tendrilModel s else thickVein s
    harbours := false
    ownModel := fun k s => if k == "puffball" then some (puffballModel s) else none
    madeModel := madeModel
    -- Behind and beside a node, never in front of its face.
    attachAngles := [-3.0 * pi / 4.0, -pi / 4.0, 3.0 * pi / 4.0]
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [{ mesh := mCyl, y := 0.002, sx := 0.84, sy := 0.006, sz := 0.84, rgb := withAlpha 0xF4F27A 0.3 }]
    monumentModel := fruiting
    square := [m speaker 0 0 0]
    roadside := fun _ => []
    treasury := reserve
    flat := fun
      | some "oatmeal" => 0x8FA24E
      | some "dew" => 0x3B8C95
      | some "rot" => 0x6A3B44
      | some "pollen" => 0xE29A2E
      | _ => 0xC6A06A
    look :=
      { tagline := "Ooze along the log. Outvote the other moulds."
        bodyFont := "humanist"
        displayFont := "rounded"
        tokens :=
          [ ("walnut-0", "#0d120c"), ("walnut-1", "#141c13"), ("walnut-2", "#1f2a1c"), ("walnut-3", "#2f3d29"), ("brass", "#7f8c3c")
          , ("vellum", "#e8ebcb"), ("vellum-2", "#dbe0b8"), ("vellum-3", "#c3ca98")
          , ("ink", "#1c2313"), ("ink-2", "#4a5336"), ("ink-3", "#737c58")
          , ("gold", "#d6e04a"), ("gold-2", "#eff37c"), ("gold-ink", "#1e2406")
          , ("wax", "#8e1f5e"), ("wax-2", "#b83a80"), ("wax-0", "#6e1648"), ("pale", "#e0e7c8"), ("pale-2", "#a7b18b")
          , ("sign-ink", "#4a1a5e"), ("act-hover", "#3c4c34"), ("act-hover-2", "#33402a"), ("field", "#f5f7df")
          , ("bright", "#f8fbe6"), ("err-ink", "#fbf3f7"), ("tool-off", "#7d8768"), ("need", "#c7d0a6")
          , ("good", "#2a6b2c"), ("stain", "#5a6a28")
          , ("roll-0", "#525c36"), ("roll-1", "#6e7a48"), ("roll-2", "#8d9960"), ("roll-3", "#98a36c"), ("roll-4", "#a4af78")
          , ("roll-5", "#b9c38e"), ("roll-6", "#ccd4a6"), ("roll-7", "#dbe0b8"), ("roll-8", "#eff2d2") ]
        marks := []
        quietPieces := ["tendril"]
        icons :=
          [ ("oatmeal", [ { d := "M4 13c0-5 5-8 10-7 4 1 6 4 6 7s-4 6-9 6-7-2-7-6z", fill := "#d9c583", stroke := "#7a6a38", width := 1.4 }
                     , { d := "M8 14c2-3 5-4 8-4", stroke := "#7a6a38", width := 1.4 } ])
          , ("dew", [ { d := "M12 2.500c3 4.500 6.500 8 6.500 12a6.500 6.500 0 0 1-13 0c0-4 3.500-7.500 6.500-12z", fill := "#6cc3cf", stroke := "#1f4f58", width := 1.4 }
                    , { d := "M9 15a3 3 0 0 0 2.500 3", stroke := "#e6fbff", width := 1.6 } ])
          , ("rot", [ { d := "M3.500 12a8.500 7.500 0 0 1 17 0c0 1-1 1.500-2 1.500H5.500c-1 0-2-.500-2-1.500z", fill := "#6b3c58", stroke := "#2c1a20", width := 1.4 }
                    , { d := "M10 13.500h4l.800 7h-5.600z", fill := "#c9bba6", stroke := "#2c1a20", width := 1.2 }
                    , { d := "M8 8.500a1.300 1.300 0 1 0 .010 0zM14.500 7a1.300 1.300 0 1 0 .010 0z", fill := "#e9dcf0" } ])
          , ("pollen", [ { d := "M8 5a3.500 3.500 0 1 0 .010 0zM16.500 7a3 3 0 1 0 .010 0zM11 14a4 4 0 1 0 .010 0z", fill := "#f08a24", stroke := "#7c4210", width := 1.3 } ])
          , ("tendril", [ { d := "M3 20C8 18 8 13 12 12s5-5 9-8M12 12c-2-2-2-4-1-7M12 12c2 2 5 2 7 4", stroke := "currentColor", width := 2.6 } ])
          , ("node", [ { d := "M3 19c0-8 4-13 9-13s9 5 9 13c0 1-1 1.500-2 1.500H5c-1 0-2-.500-2-1.500z", fill := "currentColor" }
                     , { d := "M9 11a2 2 0 1 0 .010 0zM15 11a2 2 0 1 0 .010 0z", fill := "#000000", opacity := 0.55 } ])
          , ("swelling", [ { d := "M2 20c0-5 1-8 3-10 0-4 3-7 7-7s7 3 7 7c2 2 3 5 3 10 0 1-1 1.500-2 1.500H4c-1 0-2-.500-2-1.500z", fill := "currentColor" }
                         , { d := "M6 10c0-4 3-5.500 6-5.500s6 1.500 6 5.500c-1.500-1.500-3-2-6-2s-4.500.500-6 2z", fill := "#f4eedc" }
                         , { d := "M9.500 12.500a1.600 1.600 0 1 0 .010 0zM14.500 12.500a1.600 1.600 0 1 0 .010 0z", fill := "#000000", opacity := 0.6 } ])
          , ("puffball", [ { d := "M5 13a7 7 0 0 1 14 0c0 3-3 5-7 5s-7-2-7-5z", fill := "currentColor" }
                         , { d := "M9 18h6l1 3.500H8z", fill := "currentColor", opacity := 0.7 }
                         , { d := "M11 6a1.200 1.200 0 1 0 .010 0z", fill := "#000000", opacity := 0.5 } ]) ] } }

end Look

end Charter.Games.SlimeParliament
