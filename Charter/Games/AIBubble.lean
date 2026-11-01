import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render
import Charter.Games.AIBubble.Meshes

/-!
# The AI Bubble

Rival labs build datacenters on a dark desert grid. Everyone knows the numbers do not add up, and nobody
can afford to be the first to stop. Hype is worth points until the crash. Capital is raised on hype. The
market for inference pays a fixed sum, however much of it the labs make. All labs at any table are
invented.

The look uses mesh files. `packs/ai-bubble/gen.py` makes them and writes `Meshes.lean`.
-/

namespace Charter.Games.AIBubble

open HexGrid

/-! ## The map: 19 hexes, with the trading floor in the middle -/

def hexes : List Hex := hexagon 2

/-- Resources in `hexes` order, after the middle. 8 power, 5 silicon, 5 concrete. Power is the most
common, because every datacenter burns it every round. -/
def tileResources : List Res :=
  [ "silicon", "power", "concrete", "power", "silicon", "concrete"
  , "power", "silicon", "power", "concrete", "power", "concrete", "silicon", "power", "power", "silicon", "power", "concrete" ]

def tileNumbers : List Nat :=
  [ 6, 12, 3, 10, 11, 4
  , 9, 4, 8, 10, 11, 6, 5, 2, 9, 8, 5, 3 ]

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

/-- The bubble is what the treasury holds of it. -/
def bubble : Expr := held .treasury "bubble"

/-- The dice plus a third of the bubble reach 20. -/
def pops : Cond := .le (.lit 20) (.add .rolled (.div bubble 3))

/-- **The crash.** One number says how close it is: the dice plus a third of the bubble. From 24 on the
bubble can pop on a 12, and each 3 more brings a lower roll in. From 54 on any roll pops it. It wipes out hype
and empties the bubble, and nothing else. The first clause sets the law's monument. -/
def lawCrash : Law :=
  { title := "Hype is worth a point each, until the crash"
    clauses :=
      [ .onRoll
          [ .forEach pops [.transfer .each .bank (.lit "hype") (held .each "hype")]
          , .when pops [.transfer .treasury .bank (.lit "bubble") bubble] ]
      , .setWorth "hype" 1 ] }

/-- What a seat turns into money this round: what it declared in capital, up to the hype it holds. -/
def raised : Expr := .min (.declared .each (.lit "capital")) (held .each "hype")

/-- **Raising money.** A seat declares a number in capital, and at the round's end it trades that much hype
for twice as much capital. That hype goes onto the bubble. So does each build. A rising bubble pays
everyone more hype, so everyone gains on paper from what everyone else does. -/
def lawRaise : Law :=
  { title := "Build or raise money, and the bubble grows"
    clauses :=
      [ .onBuild "datacenter"
          [ .transfer .bank .actor (.lit "hype") (.lit 2)
          , .transfer .bank .treasury (.lit "bubble") (.lit 1) ]
      , .onBuild "campus" [.transfer .bank .treasury (.lit "bubble") (.lit 2)]
      , .onRoundEnd [.forEach .yes
          [ .transfer .each .bank (.lit "hype") raised
          , .transfer .bank .each (.lit "capital") (.mul (.lit 2) raised)
          , .transfer .bank .treasury (.lit "bubble") raised
          , .transfer .bank .each (.lit "hype") (.add (.lit 1) (.div bubble 10)) ]] ] }

/-- All the inference held at this moment, by everyone. -/
def supply : Expr := .totalOver .yes (held .each "inference")

/-- **The market.** Whatever the dice pay a datacenter, it also makes that much inference. Customers pay a
fixed sum each round, split by share of supply. So the price of a token is that sum over the supply, and
every lab that builds lowers everyone's price. -/
def lawMarket : Law :=
  { title := "Customers pay 16 capital a round, split by share of inference"
    clauses :=
      [ .onHarvest [.transfer .bank .actor (.lit "inference") .harvestedAmount]
      , .onRoundEnd [.forEach .yes
          [ .transfer .bank .each (.lit "capital") (.divBy (.mul (.lit 16) (held .each "inference")) supply)
          , .transfer .each .bank (.lit "inference") (held .each "inference") ]] ] }

/-- What a seat owes in power each round. -/
def upkeep : Expr := .add (.count .each "datacenter") (.mul (.lit 2) (.count .each "campus"))

/-- **Upkeep.** It comes due whether or not anyone is buying, from the second round. A seat that cannot pay
it in full loses its newest datacenter. -/
def lawPower : Law :=
  { title := "Upkeep in power is due every round, or a datacenter goes dark"
    clauses :=
      [ .onRoundEnd
          [ .forEach (.lt (.lit 1) .round) [.transfer .each .bank (.lit "power") upkeep]
          , .forEach (.and (.lt (.lit 1) .round) (.lt (held .each "power") upkeep))
              [.movePiece .each .bank "datacenter"] ] ] }

def foundingLaws : List Law := [lawCrash, lawRaise, lawMarket, lawPower]

/-! ## The game -/

/-- `bubble` is in a campus's cost at 0 only so that the screen counts it as a good. The screen leaves a
resource no piece costs out of hands and off the treasury, and then the hype meter could not read it. -/
def game : GameDef where
  name := "The AI Bubble"
  resources :=
    [ ⟨"silicon", 90⟩, ⟨"power", 120⟩, ⟨"concrete", 90⟩, ⟨"capital", 800⟩
    , ⟨"inference", 300⟩, ⟨"hype", 300⟩, ⟨"bubble", 300⟩ ]
  pieces :=
    [ { name := "fibre", cost := [("concrete", 1), ("capital", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "datacenter", cost := [("concrete", 1), ("silicon", 1), ("power", 1), ("capital", 2)], points := 1
        placement := .spot, yield := 2, limit := 8 }
    , { name := "campus"
        cost := [("concrete", 2), ("silicon", 2), ("capital", 5), ("inference", 2), ("hype", 3), ("bubble", 0)]
        points := 3, placement := .upgrade "datacenter", yield := 3, limit := 4 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 25
  rounds := 10
  bankRate := 3
  setupPieces := ["datacenter", "fibre"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look -/

section Look
open Charter.Scene GpuCmd
open Meshes

/-- Hot colours that stand out from a cold, dark map: magenta, lime, orange and blue, then violet and white. -/
def seats : List UInt32 := [0xFF2E88, 0xB8FF2E, 0xFF8A1E, 0x3D8BFF, 0xB06BFF, 0xF2F6FF]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- Pale beacons on a roof, more of them for a later seat, so colour is not the only cue. -/
def tell (s : Nat) (x y z : Float) : List Part :=
  (List.range (s % 4 + 1)).map fun j => box (x + 0.05 * j.toFloat) y z 0.034 0.02 0.034 0xF4FAFF

def datacenterModel (_seed s _round : Nat) : List Part :=
  [m dcBody 0 0 0, m dcLed 0 0 0 (seat s)] ++ tell s 0.03 0.136 0.0

def campusModel (_seed s _round : Nat) : List Part :=
  [m campusBody 0 0 0, m campusLed 0 0 0 (seat s), m steam 0 0 0 (withAlpha 0xFFFFFF 0.42)] ++ tell s (-0.2) 0.24 0.12

def fibreModel (s : Nat) : List Part :=
  let marks : List Float := match s % 4 with
    | 0 => [-0.26]
    | 1 => [-0.26, 0.26]
    | 2 => [-0.3, -0.2, 0.26]
    | _ => [-0.3, -0.2, 0.2, 0.3]
  [m fibreBed 0 0 0, m fibreCore 0 0 0 (seat s)] ++ marks.map fun u => box u 0.024 0 0.03 0.006 0.05 0xF4FAFF

/-- A link piece that a law made: a thicker trunk line. -/
def trunkModel (s : Nat) : List Part :=
  [{ m fibreBed 0 0 0 with sz := 1.7 }, { m fibreCore 0 0 0 (seat s) with sz := 1.9, sy := 1.5 }]

/-- A piece that a law made. The name's hash picks the shape. -/
def madeModel (name : String) (s : Nat) : List Part :=
  let id := match hashText name % 3 with
    | 0 => madeA
    | 1 => madeB
    | _ => madeC
  [m id 0 0 0 (seat s)] ++ tell s 0.1 0 0.1

def tileTop (res : Option Res) (seed : Nat) : List Part :=
  let turned : Float := pickFrom [0.0, pi / 3.0, -pi / 3.0, pi, 2.0 * pi / 3.0, -2.0 * pi / 3.0] seed 3
  match res with
  | some "silicon" => [m tileSilicon 0 0 0 0xFFFFFF 1 turned]
  | some "power" => [m tilePower 0 0 0]
  | some "concrete" => [m tileConcrete 0 0 0 0xFFFFFF 1 turned]
  | _ => [m tileExchange 0 0 0]

/-- Small things on a tile. The tall ones keep away from the number token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (lowOk : Bool) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n 0.46 0.72).filter fun (x, z, _) => keep x z && (lowOk || !hidesToken x z)).flatMap fun (x, z, i) => f x z i
  match res with
  | some "silicon" => at_ 7 false fun x z i =>
      if i % 3 == 0 then [m rack x 0 z 0xFFFFFF (0.9 + 0.4 * rnd seed i) (6.28 * rnd seed (i + 9))]
      else [m pallet x 0 z 0xFFFFFF (0.9 + 0.5 * rnd seed i) (1.57 * rnd seed (i + 9))]
  | some "power" => at_ 5 false fun x z i =>
      if i % 2 == 0 then [m pylon x 0 z 0xFFFFFF (0.85 + 0.35 * rnd seed i) (1.57 * rnd seed (i + 9))]
      else [m transformer x 0 z 0xFFFFFF (1.0 + 0.3 * rnd seed i) (1.57 * rnd seed (i + 9))]
  | some "concrete" => at_ 5 false fun x z i =>
      if i % 3 == 0 then [m crane x 0 z 0xFFFFFF (0.95 + 0.3 * rnd seed i) (6.28 * rnd seed (i + 9))]
      else [m slabs x 0 z 0xFFFFFF (1.0 + 0.4 * rnd seed i) (1.57 * rnd seed (i + 9))]
  | _ => []

/-- What spreads out from a datacenter onto a tile: batteries on power, racks on silicon, chillers on
concrete. Each gets more as the piece grows and the game goes on. `cx, cz` points to the piece. -/
def growth (res : Option Res) (_seed count : Nat) (cx cz : Float) : List Part :=
  let (px, pz) := (0 - cz, cx)
  let spot (i : Nat) : Float × Float :=
    let along := 0.56 - 0.1 * (i / 2).toFloat
    let side := (if i % 2 == 0 then 0.17 else -0.17) * (1.0 + (i / 2).toFloat * 0.5)
    (cx * along + px * side, cz * along + pz * side)
  (List.range count).flatMap fun i =>
    let (x, z) := spot i
    let r := Float.atan2 (0 - cz) cx
    match res with
    | some "power" => [m battery x 0 z 0xFFFFFF 1 r]
    | some "silicon" => [m rack x 0 z 0xFFFFFF 0.8 r]
    | some "concrete" => [m chillers x 0 z 0xFFFFFF 1 r]
    | _ => []

/-- A law's monument, by what the law is about. A law of decrees, or one that sets a resource's worth or
ends the game, stands as a repeal does. -/
def monumentOf : MonumentKind → List Part
  | .cost => [m lawCost 0 0 0]
  | .points => [m lawPoints 0 0 0]
  | .bank => [m lawBank 0 0 0]
  | .harvest => [m lawHarvest 0 0 0]
  | .build => [m lawBuild 0 0 0]
  | .roundEnd => [m lawRound 0 0 0]
  | .roll => [m lawRoll 0 0 0]
  | .newPiece _ => [m lawPiece 0 0 0]
  | .repeal => [m lawRepeal 0 0 0]

/-- The desert floor, the grid on it, and the far side of the table. It covers the wooden table. -/
def surround : List Cmd :=
  [ (m desert 0 0 0).at 0 0 0, (m farHalls 0 0 0).at 0 0 0, (m farLights 0 0 0).at 0 0 0, (m farLine 0 0 0).at 0 0 0 ]

/-- A lit plate under each tile. It shows in the gaps, and draws the grid of the board. -/
def under (ts : List TileDef) : List Cmd :=
  ts.map fun t =>
    let (x, z) := t.hex.toPixel 1.0
    (m seam x 0.1 z 0x1BD4F2).at 0 0 0

/-- The hype meter stands where the treasury stands. One ring for each 3 on the bubble: cold at first,
then hotter from each level at which a lower roll can pop it. -/
def meter (total : Nat) : List Part :=
  let rings := (List.range (min (total / 3) 20)).map fun i =>
    let c : UInt32 := if i < 8 then 0x22E3FF else if i < 13 then 0xFFD21F else if i < 18 then 0xFF7A1F else 0xFF2E3C
    m meterRing 0 (0.24 + 0.105 * i.toFloat) 0 c
  [m meterBase 0 0 0, m meterGlass 0 0 0 (withAlpha 0xBDF4FF 0.1)] ++ rings

def theme : Theme :=
  { tableColor := 0x05080D
    ground := fun
      | some "silicon" => 0x07261F
      | some "power" => 0x241A0A
      | some "concrete" => 0x6F7780
      | _ => 0x070A10
    decor := decor
    growth := growth
    surround := surround
    under := under
    shape := fun k => if k == "datacenter" then some .settlement else if k == "campus" then some .city else none
    smallModel := datacenterModel
    largeModel := campusModel
    linkModel := fun k s => if k == "fibre" then fibreModel s else trunkModel s
    harbours := false
    madeModel := madeModel
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [{ mesh := mHex, y := 0.002, sx := 0.93, sy := 0.006, sz := 0.93, rgb := withAlpha 0xA8F6FF 0.24 }]
    monumentModel := monumentOf
    square := [m exchange 0 0 0, m exchangeLit 0 0 0 0x22E3FF]
    roadside := fun seed => [m relay (if seed % 2 == 0 then 0.1 else -0.1) 0 (if seed % 2 == 0 then 0.12 else -0.12)]
    treasury := meter
    flat := fun
      | some "silicon" => 0x13705A
      | some "power" => 0xD08A1A
      | some "concrete" => 0x8E98A3
      | _ => 0x10161F
    look :=
      { tagline := "Raise on hype. Build on the grid. Get out before the crash."
        bodyFont := "humanist"
        displayFont := "typewriter"
        tokens :=
          [ ("walnut-0", "#05080d"), ("walnut-1", "#0a1018"), ("walnut-2", "#111a25"), ("walnut-3", "#1b2836"), ("brass", "#2f6f86")
          , ("vellum", "#dde8ef"), ("vellum-2", "#cedce5"), ("vellum-3", "#b4c6d2")
          , ("ink", "#0c1720"), ("ink-2", "#3a4d5a"), ("ink-3", "#5c707e")
          , ("gold", "#22e3ff"), ("gold-2", "#8ff1ff"), ("gold-ink", "#03141a")
          , ("wax", "#b3123f"), ("wax-2", "#e0285a"), ("wax-0", "#8c0d30"), ("pale", "#d8e9f2"), ("pale-2", "#8fa8b8")
          , ("sign-ink", "#0a3f7a"), ("act-hover", "#16303d"), ("act-hover-2", "#122733"), ("field", "#eef5f9")
          , ("bright", "#f4fbff"), ("err-ink", "#fff0f3"), ("tool-off", "#5a6f7d"), ("need", "#a8bfcc")
          , ("good", "#067a55"), ("stain", "#1b6a84")
          , ("roll-0", "#2a4655"), ("roll-1", "#3a6072"), ("roll-2", "#4d7a8e"), ("roll-3", "#5b8a9e"), ("roll-4", "#6f9cb0")
          , ("roll-5", "#8ab3c5"), ("roll-6", "#a8cad9"), ("roll-7", "#bedbe7"), ("roll-8", "#dff3fb") ]
        marks := []
        quietPieces := ["fibre"]
        icons :=
          [ ("silicon", [ { d := "M7 7h10v10H7z", fill := "#16c78c", stroke := "#063d2c", width := 1.4 }
                        , { d := "M10 3v4M14 3v4M10 17v4M14 17v4M3 10h4M3 14h4M17 10h4M17 14h4", stroke := "#16c78c", width := 1.6 }
                        , { d := "M10 10h4v4h-4z", fill := "#063d2c" } ])
          , ("power", [ { d := "M13.500 2L5 13.500h5.500L9.500 22l9-12h-5.700z", fill := "#ffb21f", stroke := "#5a3a05", width := 1.2 } ])
          , ("concrete", [ { d := "M3 9l9-5 9 5v7l-9 5-9-5z", fill := "#aeb8c2", stroke := "#333b44", width := 1.3 }
                         , { d := "M3 9l9 5 9-5M12 14v7", stroke := "#333b44", width := 1.3 } ])
          , ("capital", [ { d := "M12 2.500a9.500 9.500 0 1 0 .010 0z", fill := "#f3d36b", stroke := "#5e4c10", width := 1.3 }
                        , { d := "M12 6.500v11M8 9.500h8M8 14.500h8", stroke := "#5e4c10", width := 2 } ])
          , ("inference", [ { d := "M12 2l8.700 5v10L12 22l-8.700-5V7z", fill := "#22e3ff", stroke := "#043d4a", width := 1.3 }
                          , { d := "M12 6.500l1.700 3.800 3.800 1.700-3.800 1.700L12 17.500l-1.700-3.800L6.500 12l3.800-1.700z", fill := "#03232b" } ])
          , ("hype", [ { d := "M3 10v4l3 .500 11 5V4.500l-11 5z", fill := "#ff4fa0", stroke := "#5e0f38", width := 1.3 }
                     , { d := "M20 8c1.300 2.500 1.300 5.500 0 8", stroke := "#ff4fa0", width := 2 }
                     , { d := "M7 15l1.500 5h2.500l-1-4", fill := "#ff4fa0", stroke := "#5e0f38", width := 1.2 } ])
          , ("bubble", [ { d := "M12 2.500a9.500 9.500 0 1 0 .010 0z", fill := "#bdf4ff", stroke := "#1a7f96", width := 1.6, opacity := 0.75 }
                       , { d := "M7 10a5.500 5.500 0 0 1 4.500-4.500", stroke := "#ffffff", width := 2 } ])
          , ("fibre", [ { d := "M3 20C8 18 8 13 12 12s5-5 9-8", stroke := "currentColor", width := 2.8 }
                      , { d := "M3 18a2.200 2.200 0 1 0 .010 0zM21 2a2.200 2.200 0 1 0 .010 0z", fill := "currentColor" } ])
          , ("datacenter", [ { d := "M2 8h20v12H2z", fill := "currentColor" }
                           , { d := "M5 12h2.500v5H5zM9.500 12H12v5H9.500zM14 12h2.500v5H14zM18 12h2v5h-2z", fill := "#000000", opacity := 0.6 } ])
          , ("campus", [ { d := "M1.500 12H14v9H1.500zM3 6h9v5H3z", fill := "currentColor" }
                       , { d := "M15.500 21c1.200-4 1.200-7 .300-11h6.400c-.900 4-.900 7 .300 11z", fill := "currentColor" }
                       , { d := "M4 15h2v3H4zM8 15h2v3H8zM5 8h5v1.500H5z", fill := "#000000", opacity := 0.6 } ]) ] } }

end Look

end Charter.Games.AIBubble
