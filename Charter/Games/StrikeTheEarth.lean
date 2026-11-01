import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render
import Charter.Games.StrikeTheEarth.Meshes

/-!
# Strike the Earth

Rival dwarf clans dig under one doomed mountain. The score is `renown`, and only renown counts: a hall
that falls costs no points, and a workshop that falls pays some. So the fort can vote its way into
ruin, and the winner is whoever leaves the best legend. Rolls bring cave-ins, floods and the Thing Below.
Danger is a pile in the treasury that everyone can see. It rises each round, and each shaft raises it
more. A majority can end the game by law.

The look uses mesh files. `packs/strike-the-earth/gen.py` makes them and writes `Meshes.lean`.
-/

namespace Charter.Games.StrikeTheEarth

open HexGrid

/-! ## The map: wide at the viewer's side, narrow at the back, like a mountain seen from below -/

/-- The chamber first, because the laws' monuments stand on the first tile. -/
def hexes : List Hex :=
  [ ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨2, -1⟩, ⟨-2, 1⟩, ⟨2, 0⟩, ⟨-2, 2⟩
  , ⟨1, 1⟩, ⟨-1, 2⟩, ⟨0, 2⟩, ⟨-1, -1⟩, ⟨3, -1⟩, ⟨-2, 3⟩ ]

def tileResources : List Res :=
  [ "ember", "ore", "stone", "stone", "ember", "ore", "ore", "fungus"
  , "ember", "stone", "fungus", "fungus", "ore", "fungus", "stone", "ember" ]

/-- No 6 or 8 touches another 6 or 8, and no number touches itself. There is no 2, 7 or 12: those rolls
pay nobody and bring trouble. -/
def tileNumbers : List Nat :=
  [ 6, 6, 10, 3, 5, 9, 4, 11
  , 3, 4, 8, 9, 10, 11, 8, 5 ]

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

/-- The danger everyone shares. It sits in the treasury. -/
def danger : Expr := .holding .treasury (.lit "danger")

def pay (who : Party) (n : Nat) : Effect := .transfer .bank who (.lit "renown") (.lit n)
def raiseDanger (n : Nat) : Effect := .transfer .bank .treasury (.lit "danger") (.lit n)
def has (k : PieceKind) : Cond := .lt (.lit 0) (.count .each k)

/-- **The score.** Each renown is worth a point. Deeds pay it. A shaft also raises the danger, and so does
every round that passes. -/
def lawRenown : Law :=
  { title := "Renown is the score. Deeds earn it, and digging raises the danger"
    clauses :=
      [ .onBuild "hall" [pay .actor 1]
      , .onBuild "workshop" [pay .actor 2]
      , .onBuild "shaft" [pay .actor 1, raiseDanger 2]
      , .onRoundEnd [raiseDanger 1]
      , .setWorth "renown" 1 ] }

/-- **A cave-in.** A 7 brings down each clan's newest shaft, and at high danger its newest workshop too.
A clan is paid for what it loses. -/
def lawCaveIn : Law :=
  { title := "A 7 brings the roof down"
    clauses :=
      [ .onRoll
          [ .forEach (.and (.eq .rolled (.lit 7)) (.and (.le (.lit 3) danger) (has "shaft")))
              [.movePiece .each .bank "shaft", pay .each 2]
          , .forEach (.and (.eq .rolled (.lit 7)) (.and (.le (.lit 9) danger) (has "workshop")))
              [.movePiece .each .bank "workshop", pay .each 3] ] ] }

/-- **A flood.** A 2 or 3 takes a tunnel and fungus from each clan with no gate. The higher the danger, the
more fungus it takes. -/
def lawFlood : Law :=
  { title := "A 2 or 3 floods every clan with no gate"
    clauses :=
      [ .onRoll
          [ .forEach (.and (.le .rolled (.lit 3)) (.eq (.count .each "gate") (.lit 0)))
              [ .movePiece .each .bank "tunnel"
              , .transfer .each .bank (.lit "fungus") (.div danger 2)
              , pay .each 1 ] ] ] }

/-- **The Thing Below.** An 11 or 12 at danger 6 or more wakes it. It finds the clan with the most shafts,
and it eats that clan's newest workshop and shaft. It is a very good song. -/
def lawThing : Law :=
  { title := "An 11 or 12 wakes the Thing Below, and it eats the deepest clan"
    clauses :=
      [ .onRoll
          [ .forEach
              (.and (.le (.lit 11) .rolled) (.and (.le (.lit 6) danger)
                (.and (has "shaft") (.eq (.count .each "shaft") (.mostOver .yes (.count .each "shaft"))))))
              [.movePiece .each .bank "workshop", .movePiece .each .bank "shaft", pay .each 4] ] ] }

def foundingLaws : List Law := [lawRenown, lawCaveIn, lawFlood, lawThing]

/-! ## The game -/

def game : GameDef where
  name := "Strike the Earth"
  resources :=
    [ ⟨"stone", 30⟩, ⟨"ore", 30⟩, ⟨"fungus", 30⟩, ⟨"ember", 30⟩
    , ⟨"renown", 160⟩, ⟨"danger", 60⟩ ]
  pieces :=
    [ { name := "tunnel", cost := [("stone", 1), ("ember", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "hall", cost := [("stone", 1), ("fungus", 1)], points := 0
        placement := .spot, yield := 2, limit := 6 }
    , { name := "workshop", cost := [("ore", 2), ("ember", 2)], points := 0
        placement := .upgrade "hall", yield := 3, limit := 4 }
    , { name := "farm", cost := [("fungus", 2)], points := 0
        placement := .attach "hall", yield := 1, limit := 3 }
    , { name := "gate", cost := [("stone", 2)], points := 0
        placement := .attach "hall", yield := 0, limit := 2 }
    , { name := "shaft", cost := [("ore", 2), ("stone", 1)], points := 0
        placement := .attach "hall", yield := 2, limit := 3 }
    , { name := "epitaph", cost := [("renown", 2), ("danger", 1)], points := 5
        placement := .attach "hall", yield := 0, limit := 1 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 40
  rounds := 10
  bankRate := 4
  setupPieces := ["hall", "tunnel"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look -/

section Look
open Charter.Scene GpuCmd
open Meshes

/-- Six clan colours that stand out from dark rock and orange fire: ice, rose, lime, gold, violet, white. -/
def seats : List UInt32 := [0x38C6F4, 0xF0408C, 0x9CE63A, 0xF7DC3E, 0xAE7CFF, 0xF2F2EC]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- A pool of torchlight on the ground: two flat discs, the wider one fainter. -/
def pool (r : Float) (a : Float := 0.16) : List Part :=
  [ { mesh := mCyl, y := 0.003, sx := r, sy := 0.004, sz := r, rgb := withAlpha 0xFFB060 a }
  , { mesh := mCyl, y := 0.006, sx := r * 0.62, sy := 0.004, sz := r * 0.62, rgb := withAlpha 0xFFC880 a } ]

/-- Pale studs that differ by seat, so colour is not the only cue. -/
def tell (s : Nat) (h : Float) (out : Float := 0.13) : List Part :=
  let studs : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.05, 0.05]
    | _ => [-0.075, 0, 0.075]
  studs.map fun u => ball (0.7071 * (out + u)) h (0.7071 * (out - u)) 0.046 0xFAF4E0

def hallModel (_seed s _round : Nat) : List Part :=
  pool 0.36 ++ [m hallStone 0 0 0 0xFFFFFF 1.28, m hallRoof 0 0 0 (seat s) 1.28, m hallFire 0 0 0 0xFFFFFF 1.28] ++ tell s 0.175 0.13

def workshopModel (_seed s _round : Nat) : List Part :=
  pool 0.5 0.2 ++ [m shopStone 0 0 0 0xFFFFFF 1.12, m shopRoof 0 0 0 (seat s) 1.12, m shopFire 0 0 0 0xFFFFFF 1.12] ++ tell s 0.225 0.15

def tunnelModel (s : Nat) : List Part :=
  let marks : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.12, 0.12]
    | _ => [-0.22, 0, 0.22]
  m tunnel 0 0 0 (seat s) :: marks.map fun u => ball u 0.075 0 0.06 0xFAF4E0

/-- A link piece that a law made: a wider tunnel. -/
def wideTunnel (s : Nat) : List Part :=
  [{ m tunnel 0 0 0 (seat s) with sy := 1.5, sz := 1.8 }, ball 0 0.11 0 0.07 0xFAF4E0]

def farmModel (s : Nat) : List Part :=
  [m farmStalks 0 0 0, m farmCaps 0 0 0 (seat s)] ++ tell s 0.205 0

def gateModel (s : Nat) : List Part :=
  [m gateStone 0 0 0, m gateDoor 0 0 0 (seat s)] ++ tell s 0.34 0

def shaftModel (s : Nat) : List Part :=
  [m shaftFrame 0 0 0, m shaftPit 0 0 0, m shaftFlag 0 0 0 (seat s)] ++ tell s 0.075 0.1

def epitaphModel (s : Nat) : List Part :=
  [m epitaphStone 0 0 0, m epitaphCap 0 0 0 (seat s)] ++ tell s 0.05 0.08

/-- A piece that a law made has a stone in the seat's colour, with its name over it. -/
def madeModel (_name : String) (s : Nat) : List Part :=
  [m epitaphStone 0 0 0 (seat s)] ++ tell s 0.05 0.08

def tileMesh : Option Res → UInt32
  | some "stone" => tileStone
  | some "ore" => tileOre
  | some "fungus" => tileFungus
  | some "ember" => tileEmber
  | _ => tileChamber

def tileTop (res : Option Res) (seed : Nat) : List Part :=
  let turned : Float := pickFrom [0.0, pi / 3.0, -pi / 3.0, pi, 2.0 * pi / 3.0, -2.0 * pi / 3.0] seed 3
  match res with
  | none => [m tileChamber 0 0 0, m runes 0 0 0]
  | some "ember" => [m tileEmber 0 0 0 0xFFFFFF 1 turned, m seam 0 0 0 0xFFFFFF 1 turned]
  | _ => [m (tileMesh res) 0 0 0 0xFFFFFF 1 turned]

/-- Small things on a tile. The tall ones keep away from the number token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (lowOk : Bool) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n 0.44 0.72).filter fun (x, z, _) => keep x z && (lowOk || !hidesToken x z)).flatMap fun (x, z, i) => f x z i
  let k (i : Nat) (a b : Float) : Float := a + b * rnd seed i
  let r (i : Nat) : Float := 6.28 * rnd seed (i + 9)
  match res with
  | some "stone" => at_ 5 false fun x z i =>
      if i % 2 == 0 then [m stalag x (-0.01) z 0xFFFFFF (k i 0.8 0.6) (r i)] else [m rubble x 0 z 0xFFFFFF (k i 0.9 0.6) (r i)]
  | some "ore" => at_ 4 false fun x z i => [m oreChunk x (-0.005) z 0xFFFFFF (k i 0.9 0.7) (r i)]
  | some "fungus" => at_ 5 false fun x z i =>
      [m (if i % 3 == 0 then capViolet else capTeal) x (-0.005) z 0xFFFFFF (k i 0.8 0.7) (r i)]
  | some "ember" => at_ 3 true fun x z i => [m hotRock x (-0.005) z 0xFFFFFF (k i 0.8 0.8) (r i)]
  | _ => []

/-- A law's stone, by what the law is about. A law on worth or on ending the game also raises the broken
pillar, as `Scene.monumentOf` gives those the repeal's kind. -/
def lawStone : MonumentKind → List Part
  | .cost => [m lawCost 0 0 0 0xFFFFFF 1.2]
  | .points => [m lawPoints 0 0 0 0xFFFFFF 1.2]
  | .bank => [m lawBank 0 0 0 0xFFFFFF 1.2]
  | .harvest => [m lawHarvest 0 0 0 0xFFFFFF 1.2]
  | .build => [m lawBuild 0 0 0 0xFFFFFF 1.2]
  | .roundEnd => [m lawRound 0 0 0 0xFFFFFF 1.2]
  | .roll => [m lawRoll 0 0 0 0xFFFFFF 1.2]
  | .newPiece _ => [m lawPiece 0 0 0 0xFFFFFF 1.2]
  | .repeal => [m lawBroken 0 0 0 0xFFFFFF 1.2]

/-- A point on the table, by how far it is toward the viewer and to the viewer's right. -/
def onTable (a b : Float) : Float × Float := (0.7071 * (a + b), 0.7071 * (a - b))

/-- The mountain: its ground and back wall, its cut face with magma below, two rivers of fire that fall
over the edge, lit halls in the back wall, and braziers around the map. -/
def surround : List Cmd :=
  let still : List Part :=
    [ m wall 0 0 0, m ground 0 0 0, m farLeft 0 0 0, m farRight 0 0 0, m cutFace 0 0 0, m cutLeft 0 0 0, m cutRight 0 0 0, m magma 0 0 0, m river0 0 0 0, m river1 0 0 0, m fall0 0 0 0, m fall1 0 0 0 ]
  let halls := niches.map fun (x, y, z, k) => m niche x y z 0xFFFFFF k
  let fires := braziers.flatMap fun (x, z) =>
    [m brazierBody x 0.12 z 0xFFFFFF 1.3, m brazierFire x 0.12 z 0xFFFFFF 1.3]
  let spikes := [(-3.6, -2.2, 3.2), (-3.0, 2.4, 2.6), (-3.8, 1.5, 3.8), (-1.4, 4.0, 3.0), (-1.2, -4.5, 3.6), (1.2, -6.2, 2.8), (2.0, 6.3, 2.6)].map
    fun (a, b, k) =>
      let (x, z) := onTable a b
      m stalag x 0.1 z 0xFFFFFF k (a * b)
  (box 0 0 0 90 0.003 90 0x08060A).at 0 0 0 :: ((still ++ halls ++ fires ++ spikes).map (·.at 0 0 0))

/-- The treasury is a rift in the rock. Danger in it stands up as shards of fire, so everyone can see it
grow. -/
def reserve (total : Nat) : List Part :=
  let heap := (List.range (min total 40)).map fun i =>
    let a := 2.399963 * i.toFloat
    let r := 0.04 + 0.34 * Float.sqrt (i.toFloat / 40.0)
    m shard (r * Float.cos a) 0.19 (r * Float.sin a) 0xFFFFFF (1.15 - 0.012 * i.toFloat) a
  [m riftRim 0 0.11 0, m riftCore 0 0.11 0] ++ heap

def theme : Theme :=
  { tableColor := 0x08060A
    ground := fun
      | some "stone" => 0x6E7284
      | some "ore" => 0x5C4331
      | some "fungus" => 0x2A7C70
      | some "ember" => 0x3A1E18
      | _ => 0x7E7869
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := surround
    under := fun _ => []
    shape := fun k => if k == "hall" then some .settlement else if k == "workshop" then some .city else none
    smallModel := hallModel
    largeModel := workshopModel
    linkModel := fun k s => if k == "tunnel" then tunnelModel s else wideTunnel s
    harbours := false
    ownModel := fun k s =>
      if k == "farm" then some (farmModel s)
      else if k == "gate" then some (gateModel s)
      else if k == "shaft" then some (shaftModel s)
      else if k == "epitaph" then some (epitaphModel s)
      else none
    madeModel := madeModel
    -- Behind and beside a hall, never in front of its door.
    attachAngles := [-3.0 * pi / 4.0, -pi / 4.0, 3.0 * pi / 4.0]
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [{ mesh := mHex, y := 0.02, sx := 0.9, sy := 0.006, sz := 0.9, rgb := withAlpha 0xFFD27A 0.2 }]
    monumentModel := lawStone
    square := [m founder 0 0 0, m founderEyes 0 0 0]
    roadside := fun _ => []
    treasury := reserve
    flat := fun
      | some "stone" => 0x8A8FA2
      | some "ore" => 0xC98A3A
      | some "fungus" => 0x38B39E
      | some "ember" => 0xD9531E
      | _ => 0xA89F8C
    look :=
      { tagline := "Dig too deep. Vote for it. The song is all that stays."
        bodyFont := "book"
        displayFont := "slab"
        tokens :=
          [ ("walnut-0", "#08070b"), ("walnut-1", "#121017"), ("walnut-2", "#1d1a22"), ("walnut-3", "#2d2932"), ("brass", "#b8743a")
          , ("vellum", "#ece2cf"), ("vellum-2", "#dfd3bb"), ("vellum-3", "#c9bb9f")
          , ("ink", "#231a14"), ("ink-2", "#55463a"), ("ink-3", "#7c6c5c")
          , ("gold", "#ff9a3a"), ("gold-2", "#ffc26e"), ("gold-ink", "#2a1204")
          , ("wax", "#a92d12"), ("wax-2", "#d24a1c"), ("wax-0", "#7c1f0a"), ("pale", "#efe4d2"), ("pale-2", "#b3a696")
          , ("sign-ink", "#7a1f08"), ("act-hover", "#3a3340"), ("act-hover-2", "#2f2a35"), ("field", "#f6efe0")
          , ("bright", "#fff8ec"), ("err-ink", "#fff4ee"), ("tool-off", "#7a7280"), ("need", "#c9bfae")
          , ("good", "#2f6e4a"), ("stain", "#7a5a2a")
          , ("roll-0", "#4a2a20"), ("roll-1", "#6e3a22"), ("roll-2", "#92491f"), ("roll-3", "#a8561f"), ("roll-4", "#c06a25")
          , ("roll-5", "#d27f33"), ("roll-6", "#e39a4e"), ("roll-7", "#efb873"), ("roll-8", "#f7d7a4") ]
        marks := []
        quietPieces := ["tunnel"]
        icons :=
          [ ("stone", [ { d := "M3.500 17.500l3-8.500 6-3.500 6.500 5 1.500 6.500-4 3H7z", fill := "#8a8fa2", stroke := "#2a2c36", width := 1.4 }
                      , { d := "M8 11l4 2.500 3.500-1M12 13.500V19", stroke := "#2a2c36", width := 1.2 } ])
          , ("ore", [ { d := "M12 2.500l6.500 6-2 9.500-8.500 3-5-6.500 2.500-8.500z", fill := "#f0a83a", stroke := "#6b4414", width := 1.4 }
                    , { d := "M12 2.500L10.500 11l5.500 7M10.500 11l-7.500 3.500", stroke := "#6b4414", width := 1 } ])
          , ("fungus", [ { d := "M3 12.500a9 8 0 0 1 18 0c0 1-1 1.500-2 1.500H5c-1 0-2-.500-2-1.500z", fill := "#2fcdb0", stroke := "#0f4f44", width := 1.4 }
                       , { d := "M10 14h4l1 7H9z", fill := "#e6efe6", stroke := "#0f4f44", width := 1.2 } ])
          , ("ember", [ { d := "M12 2c1 4 6.500 6.500 6.500 12.500a6.500 6.500 0 0 1-13 0c0-3 2-4.500 2.500-7.500 2 1 3 2.500 3 4.500 1-3 1.500-6 1-9.500z", fill := "#ff7a1a", stroke := "#5c1e06", width := 1.3 }
                      , { d := "M12 21a3 3 0 0 0 3-3c0-2-2-3-3-5-1 2-3 3-3 5a3 3 0 0 0 3 3z", fill := "#ffd27a" } ])
          , ("renown", [ { d := "M12 2.500l2.900 6.300 6.800.800-5 4.700 1.300 6.800-6-3.400-6 3.400 1.300-6.800-5-4.700 6.800-.800z", fill := "#f2c94c", stroke := "#6b5010", width := 1.3 } ])
          , ("danger", [ { d := "M12 3l10 18H2z", fill := "#d9421a", stroke := "#3a0e04", width := 1.5 }
                       , { d := "M12 9v6M12 17.500v1.500", stroke := "#fff2dc", width := 2.2 } ])
          , ("tunnel", [ { d := "M3 21V11a9 9 0 0 1 18 0v10h-5V11a4 4 0 0 0-8 0v10z", fill := "currentColor" } ])
          , ("hall", [ { d := "M3.500 20.500v-8.500h17v8.500z", fill := "currentColor", opacity := 0.7 }
                     , { d := "M3 12a9 8.500 0 0 1 18 0z", fill := "currentColor" }
                     , { d := "M9.500 20.500v-4a2.500 2.500 0 0 1 5 0v4z", fill := "#ffb04a" } ])
          , ("workshop", [ { d := "M2.500 20.500v-8l9.500-5 9.500 5v8z", fill := "currentColor" }
                         , { d := "M16 9.500V3.500h3.500v8z", fill := "currentColor", opacity := 0.75 }
                         , { d := "M7.500 20.500v-5h9v5z", fill := "#ff8a24" } ])
          , ("farm", [ { d := "M4 12a6 5 0 0 1 12 0z", fill := "currentColor" }, { d := "M8.500 12h3l.500 8h-4z", fill := "#e6efe6" }
                     , { d := "M13 16a4.500 3.500 0 0 1 9 0z", fill := "currentColor", opacity := 0.8 }, { d := "M16.500 16h2l.300 5h-2.600z", fill := "#e6efe6" } ])
          , ("gate", [ { d := "M3 21V7h4v14zM17 21V7h4v14zM2 7V3h20v4z", fill := "#c4bcac", stroke := "#3a352c", width := 1 }
                     , { d := "M7.500 21V8h9v13z", fill := "currentColor" } ])
          , ("shaft", [ { d := "M4 21L11 4h2l7 17M7 14h10", stroke := "currentColor", width := 2.4 }
                      , { d := "M8 21a4 2.500 0 0 1 8 0z", fill := "#ff8a24" } ])
          , ("epitaph", [ { d := "M8.500 21L10 6l2-3.500L14 6l1.500 15z", fill := "currentColor" }
                        , { d := "M6 21h12v1.500H6z", fill := "currentColor", opacity := 0.7 }
                        , { d := "M10.500 10h3M10.300 13h3.400M10 16h4", stroke := "#000000", width := 1, opacity := 0.55 } ]) ] } }

end Look

end Charter.Games.StrikeTheEarth
