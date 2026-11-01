import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render
import Charter.Games.PirateRepublic.Meshes

/-!
# The Pirate Republic

Nassau, 1715. Pirates really did elect and depose their captains and vote on shares. Here each tile is an
island in the shallows, wharves stand on the corners, and sloops lie in the channels between. Each round
every seat holds one ballot and can sell it. Whoever alone declares the most ballots they hold takes the
captain's hat. The hat takes a double share of plunder, and it can levy rum. At the end of round 5 the
Navy comes, and each seat must take the King's pardon, fight or burn.
-/

namespace Charter.Games.PirateRepublic

open HexGrid

/-! ## The map: an open bay facing the viewer -/

/-- Nassau first, because the laws' monuments stand on the first tile. The one hex left out is the bay. -/
def hexes : List Hex :=
  [ ⟨0, 0⟩
  , ⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, -1⟩
  , ⟨2, 0⟩, ⟨0, 2⟩, ⟨-1, 2⟩, ⟨-2, 2⟩, ⟨-2, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨0, -2⟩, ⟨1, -2⟩, ⟨2, -2⟩, ⟨2, -1⟩ ]

def tileResources : List Res :=
  [ "plunder", "rum", "powder", "timber", "rum", "powder"
  , "timber", "timber", "powder", "rum", "plunder", "timber", "powder", "plunder", "rum", "timber", "rum" ]

def tileNumbers : List Nat :=
  [ 9, 8, 4, 8, 10, 6
  , 6, 5, 10, 3, 5, 11, 9, 3, 4, 12, 11 ]

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

/-! ## Small words for the laws -/

def held (p : Party) (r : Res) : Expr := .holding p (.lit r)
def said (p : Party) (r : Res) : Expr := .declared p (.lit r)
def pay (a b : Party) (r : Res) (n : Expr) : Effect := .transfer a b (.lit r) n

/-- A seat's votes: what it declared, up to the ballots it really holds. -/
def votes (p : Party) : Expr := .min (said p "ballot") (held p "ballot")
/-- The most votes any seat has. -/
def topVotes : Expr := .mostOver .yes (votes .each)
def hasHat : Cond := .lt (.lit 0) (held .each "hat")
def noHat : Cond := .eq (held .each "hat") (.lit 0)

/-! ## The founding laws -/

/-- **The vote.** One seat alone must have the most votes, or the hat stays where it is. Then each seat is
brought back to 1 ballot. The chest holds the spare hat and ballots, so the bank cannot sell
them. -/
def lawVote : Law :=
  { title := "The crew votes for a captain each round"
    clauses :=
      [ .onRoundEnd
          [ .when (.and (.lt (.lit 0) topVotes) (.eq (.totalOver (.eq (votes .each) topVotes) (.lit 1)) (.lit 1)))
              [ .forEach (.and (.lt (votes .each) topVotes) hasHat) [pay .each .treasury "hat" (held .each "hat")]
              , .forEach (.and (.eq (votes .each) topVotes) noHat) [pay .treasury .each "hat" (.lit 1)] ]
          , .forEach (.lt (.lit 1) (held .each "ballot")) [pay .each .treasury "ballot" (.sub (held .each "ballot") (.lit 1))]
          , .forEach (.eq (held .each "ballot") (.lit 0)) [pay .treasury .each "ballot" (.lit 1)] ]
      , .onRoll [pay .bank .treasury "hat" (held .bank "hat"), pay .bank .treasury "ballot" (held .bank "ballot")] ] }

/-- **The double share.** Whenever the dice pay anyone plunder, the hat gets the same from the bank. -/
def lawShare : Law :=
  { title := "Plunder is worth a point, and the hat takes a double share"
    clauses :=
      [ .onHarvest [.when (.harvestedIs "plunder") [.forEach hasHat [.transfer .bank .each .harvested .harvestedAmount]]]
      , .setWorth "plunder" 1 ] }

/-- The rum levy the hat has declared, up to 3. -/
def levy : Expr := .min (.lit 3) (.mostOver hasHat (said .each "rum"))

/-- **The levy.** The captain's one choice. It goes through the bank, because at a round's end a law can
name only one seat at a time. -/
def lawLevy : Law :=
  { title := "The captain may levy up to 3 rum from each of the crew"
    clauses :=
      [ .onRoundEnd
          [ .forEach noHat [pay .each .bank "rum" levy]
          , .forEach hasHat [pay .bank .each "rum" (.totalOver noHat (.min levy (held .each "rum")))] ] ] }

def tookPardon : Cond := .lt (.lit 0) (said .each "pardon")
def stoodAndFought : Cond := .and (.le (.lit 3) (said .each "powder")) (.le (.lit 3) (held .each "powder"))

/-- **The Navy.** It comes once, at the end of round 5. Each seat chooses by what it declares that round. -/
def lawNavy : Law :=
  { title := "The Navy comes at the end of round 5: take the pardon, fight or burn"
    clauses :=
      [ .onRoll [pay .bank .treasury "pardon" (held .bank "pardon")]
      , .setWorth "pardon" 3
      , .onHarvest [.when (.and (.harvestedIs "plunder") (.lt (.lit 0) (held .actor "pardon")))
          [.transfer .actor .bank .harvested .harvestedAmount]]
      , .onRoundEnd [.when (.eq .round (.lit 5))
          [ .forEach tookPardon [pay .treasury .each "pardon" (.lit 1), pay .each .bank "plunder" (.div (held .each "plunder") 2)]
          , .forEach (.and (.not tookPardon) stoodAndFought) [pay .each .bank "powder" (.lit 3)]
          , .forEach (.and (.not tookPardon) (.not stoodAndFought)) [.movePiece .each .bank "wharf"] ]] ] }

def foundingLaws : List Law := [lawVote, lawShare, lawLevy, lawNavy]

/-! ## The game -/

def game : GameDef where
  name := "The Pirate Republic"
  resources :=
    [ ⟨"rum", 30⟩, ⟨"powder", 30⟩, ⟨"timber", 30⟩, ⟨"plunder", 40⟩
    , ⟨"ballot", 12⟩, ⟨"hat", 2⟩, ⟨"pardon", 4⟩ ]
  pieces :=
    [ { name := "sloop", cost := [("timber", 1), ("rum", 1)], points := 0
        placement := .link, yield := 0, limit := 12 }
    , { name := "wharf", cost := [("timber", 1), ("rum", 1), ("powder", 1)], points := 1
        placement := .spot, yield := 1, limit := 6 }
    , { name := "fort", cost := [("powder", 2), ("rum", 2)], points := 2
        placement := .upgrade "wharf", yield := 2, limit := 4 }
    , { name := "flagship", cost := [("hat", 1), ("ballot", 1), ("plunder", 2)], points := 4
        placement := .attach "wharf", yield := 0, limit := 1 }
    , { name := "privateer", cost := [("pardon", 1), ("powder", 2), ("timber", 2)], points := 3
        placement := .attach "wharf", yield := 0, limit := 1 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 18
  rounds := 10
  bankRate := 4
  setupPieces := ["wharf", "sloop"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look -/

section Look
open Charter.Scene GpuCmd
open Meshes

/-- Crews that stand out against the sea and the sand: blood red, marigold, bone, violet, orange and black. -/
def seats : List UInt32 := [0xE8232B, 0xFFC21F, 0xF7F2E2, 0xA442F0, 0xFF7A1F, 0x24262C]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- Pale kegs that differ by seat, so colour is not the only cue. -/
def tell (s : Nat) (x y z : Float) : List Part :=
  let kegs : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.05, 0.05]
    | _ => [-0.07, 0, 0.07]
  kegs.map fun u => ball (x + u) y (z - u) 0.05 0xF8F4E4

/-- Black bands on a sloop's sail, by seat. They rock with the sail. -/
def sloopModel (s : Nat) : List Part :=
  let marks := match s % 4 with
    | 0 => []
    | 1 => [m sloopMarks1 0 0 0]
    | 2 => [m sloopMarks2 0 0 0]
    | _ => [m sloopMarks3 0 0 0]
  [m sloopHull 0 0 0, m sloopSail 0 0 0 (seat s)] ++ marks

/-- A link piece that a law made: a boom of logs across the channel. -/
def boomModel (s : Nat) : List Part :=
  [m boom 0 0 0, m boomMark 0 0 0 (seat s)]

def wharfModel (_seed s _round : Nat) : List Part :=
  [m wharfBody 0 0 0, m wharfTint 0 0 0 (seat s), m wharfLight 0 0 0] ++ tell s 0.12 0.05 0.12

def fortModel (_seed s _round : Nat) : List Part :=
  [m fortBody 0 0 0, m fortTint 0 0 0 (seat s)] ++ tell s 0.12 0.15 0.12

def flagshipModel (s : Nat) : List Part :=
  [m flagshipBody 0 0 0 0xFFFFFF 0.85, m flagshipTint 0 0 0 (seat s) 0.85] ++ tell s 0 0.07 0

def privateerModel (s : Nat) : List Part :=
  [m privateerBody 0 0 0 0xFFFFFF 0.85, m privateerTint 0 0 0 (seat s) 0.85] ++ tell s 0 0.05 0

/-- A piece that a law made. The name's hash picks the shape. -/
def madeModel (name : String) (s : Nat) : List Part :=
  let id := match hashText name % 3 with
    | 0 => madeHull
    | 1 => madeTower
    | _ => madeMagazine
  [m id 0 0 0 (seat s)] ++ tell s 0 0.3 0

def tileTop (res : Option Res) (seed : Nat) : List Part :=
  let turned : Float := pickFrom [0.0, pi / 3.0, -pi / 3.0] seed 3
  match res with
  | some "rum" => [m tileRum 0 0 0 0xFFFFFF 1 turned]
  | some "powder" => [m tilePowder 0 0 0 0xFFFFFF 1 turned]
  | some "timber" => [m tileTimber 0 0 0 0xFFFFFF 1 (pickFrom [0.0, pi / 3.0, -pi / 3.0, pi, 2.0 * pi / 3.0, -2.0 * pi / 3.0] seed 3)]
  | some "plunder" => [m tilePlunder 0 0 0 0xFFFFFF 1 turned]
  | _ => [m tileNassau 0 0 0]

/-- Small things on a tile. The tall ones keep away from the number token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (lo hi : Float) (lowOk : Bool) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n lo hi).filter fun (x, z, _) => keep x z && (lowOk || !hidesToken x z)).flatMap fun (x, z, i) => f x z i
  match res with
  | some "timber" => at_ 10 0.32 0.6 false fun x z i => [m palm x 0 z 0xFFFFFF (0.85 + 0.75 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "rum" => at_ 8 0.32 0.58 false fun x z i => [m (if i % 3 == 0 then kegs else cane) x 0 z 0xFFFFFF (0.9 + 0.5 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "powder" => at_ 7 0.34 0.6 true fun x z i => [m (if i % 3 == 0 then kegs else rock) x 0 z 0xFFFFFF (0.8 + 0.8 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "plunder" => at_ 6 0.3 0.62 true fun x z i => [m coin x (-0.01) z 0xFFFFFF (0.8 + 0.5 * rnd seed i)] ++ (if i == 0 then [m chest (-0.42) 0 (-0.42) 0xFFFFFF 1.2 0.5] else [])
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
def seaAt (u v : Float) : Float × Float := (0.7071 * (u - v), -0.7071 * (u + v))

/-- The deep sea, islets, glints on the water, fins, and the Royal Navy waiting on the horizon. -/
def surround : List Cmd :=
  let glints := (List.range 44).map fun i =>
    let a := 2.399963 * i.toFloat
    let r := 5.9 + 6.0 * rnd 71 i
    (m glint (r * Float.cos a) 0.012 (r * Float.sin a) 0xFFFFFF (0.8 + 1.2 * rnd 72 i) a).at 0 0 0
  let islets := [(-8.2, 3.4, 1.6), (-9.4, -1.8, 1.1), (8.6, 4.2, 1.2), (-6.4, 5.7, 0.9), (9.8, -0.8, 0.8)].flatMap fun (u, v, k) =>
    let (x, z) := seaAt u v
    [(m islet x 0.012 z 0xFFFFFF k).at 0 0 0, (m palm x (0.012 + 0.12 * k) z 0xFFFFFF (1.5 * k) 0.7).at 0 0 0,
     (m palm (x + 0.2 * k) (0.012 + 0.08 * k) (z - 0.15 * k) 0xFFFFFF (1.2 * k) 2.1).at 0 0 0]
  let fins := [(-5.0, -4.2), (6.4, -4.8), (-7.0, 1.0)].map fun (u, v) =>
    let (x, z) := seaAt u v
    (m fin x 0.012 z 0xFFFFFF 2.2 (u + v)).at 0 0 0
  let (nx, nz) := seaAt 5.6 3.1
  [ (box 0 0 0 90 0.003 90 0x041F33).at 0 0 0
  , (m sea 0 0 0).at 0 0 0
  , (m navy nx 0.012 nz 0xFFFFFF 1.35 (-0.55)).at 0 0 0 ] ++ glints ++ islets ++ fins

/-- A lighter shelf of water around the archipelago, so it reads as one body. -/
def under (ts : List Charter.Games.TileDef) : List Cmd :=
  ts.map fun t =>
    let (x, z) := t.hex.toPixel 1.0
    .draw mLand { pos := vec3 x 0.012 z, scale := vec3 1.22 0.098 1.22 } 0x0C7D99 0

/-- The treasury is a sea chest on a sandbar. Gold heaps up beside it. -/
def reserve (total : Nat) : List Part :=
  let heap := (List.range (min total 40)).map fun i =>
    let a := 2.399963 * i.toFloat
    let r := 0.05 + 0.33 * Float.sqrt (i.toFloat / 40.0)
    m coin (0.12 + r * Float.cos a) (0.085 + 0.012 * (i % 4).toFloat) (0.26 + r * Float.sin a * 0.7) 0xFFFFFF 1.5 a
  [m sandbar 0 0 0, m sandbarFlag 0 0 0] ++ heap

def theme : Theme :=
  { tableColor := 0x041F33
    ground := fun
      | some "rum" => 0xA6C63C
      | some "powder" => 0x2E2E34
      | some "timber" => 0x2A7A3A
      | some "plunder" => 0x1E50B4
      | _ => 0xD9BC82
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := surround
    under := under
    shape := fun k => if k == "wharf" then some .settlement else if k == "fort" then some .city else none
    smallModel := wharfModel
    largeModel := fortModel
    linkModel := fun k s => if k == "sloop" then sloopModel s else boomModel s
    harbours := false
    ownModel := fun k s =>
      if k == "flagship" then some (flagshipModel s)
      else if k == "privateer" then some (privateerModel s)
      else none
    madeModel := madeModel
    -- Out to sea from a wharf, never across the number token.
    attachAngles := [-3.0 * pi / 4.0, -pi / 4.0, 3.0 * pi / 4.0]
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [m hotRing 0 (-0.02) 0]
    monumentModel := lawMonument
    square := [m squareMast 0 0 0, m squareFlag 0 0 0]
    roadside := fun _ => []
    treasury := reserve
    flat := fun
      | some "rum" => 0xB9D44A
      | some "powder" => 0x3A3A42
      | some "timber" => 0x35904A
      | some "plunder" => 0x2A6FD8
      | _ => 0xD9BC82
    look :=
      { tagline := "Elect a captain. Break a promise. Depose the liar. The constitution holds."
        bodyFont := "book"
        displayFont := "slab"
        tokens :=
          [ ("walnut-0", "#07131c"), ("walnut-1", "#0d1d2a"), ("walnut-2", "#16293a"), ("walnut-3", "#23394d"), ("brass", "#b0822c")
          , ("vellum", "#efe2bf"), ("vellum-2", "#e3d3a8"), ("vellum-3", "#cdb985")
          , ("ink", "#21160c"), ("ink-2", "#553f26"), ("ink-3", "#7d6543")
          , ("gold", "#f2bd2c"), ("gold-2", "#ffdf72"), ("gold-ink", "#231703")
          , ("wax", "#a81d24"), ("wax-2", "#cf343b"), ("wax-0", "#7f1218"), ("pale", "#e8dfc8"), ("pale-2", "#a9b4b3")
          , ("sign-ink", "#7a1016"), ("act-hover", "#2c4358"), ("act-hover-2", "#223647"), ("field", "#f7edd2")
          , ("bright", "#fff8e4"), ("err-ink", "#fff3f2"), ("tool-off", "#6e7f88"), ("need", "#c9c3ab")
          , ("good", "#16704f"), ("stain", "#7a5a22")
          , ("roll-0", "#4c3a22"), ("roll-1", "#6b5433"), ("roll-2", "#8a7148"), ("roll-3", "#99805a"), ("roll-4", "#a78f6a")
          , ("roll-5", "#bca882"), ("roll-6", "#cfbd96"), ("roll-7", "#e3d3a8"), ("roll-8", "#f4e8c6") ]
        marks := []
        quietPieces := ["sloop"]
        icons :=
          [ ("rum", [ { d := "M10 2.500h4v5c0 1.500 3 2.500 3 6v7a1.500 1.500 0 0 1-1.500 1.500h-7A1.500 1.500 0 0 1 7 20.500v-7c0-3.500 3-4.500 3-6z", fill := "#8a4a1c", stroke := "#3a1e0a", width := 1.3 }
                    , { d := "M7.500 13.500h9v5h-9z", fill := "#efe2bf" }
                    , { d := "M10 2.500h4v2h-4z", fill := "#d9b47a" } ])
          , ("powder", [ { d := "M6 6c0-1.500 12-1.500 12 0 2 4 2 8 0 12 0 1.500-12 1.500-12 0-2-4-2-8 0-12z", fill := "#6a4122", stroke := "#2a1608", width := 1.3 }
                       , { d := "M4.800 9.500h14.400M4.800 14.500h14.400", stroke := "#2a1608", width := 1.6 }
                       , { d := "M12 5c1-2 3-3 5-2.500", stroke := "#e8562a", width := 1.6 } ])
          , ("timber", [ { d := "M3 8.500 17.500 5l3 9.500L6 18z", fill := "#a8743c", stroke := "#4a2c12", width := 1.3 }
                       , { d := "M17.500 5a2.200 5 -16 0 1 3 9.500", fill := "#d8b47a", stroke := "#4a2c12", width := 1.2 }
                       , { d := "M6 10l9-2.200M7 14l9-2.200", stroke := "#4a2c12", width := 1 } ])
          , ("plunder", [ { d := "M12 3a9 9 0 1 0 .010 0z", fill := "#f2bd2c", stroke := "#6e4c08", width := 1.4 }
                        , { d := "M12 6.500a5.500 5.500 0 1 0 .010 0z", stroke := "#6e4c08", width := 1.1 }
                        , { d := "M10 9.500c0-1 4-1 4 0 0 1-.500 1.500-1 2v1h-2v-1c-.500-.500-1-1-1-2zM9.500 15l5-1M9.500 14l5 1", fill := "#6e4c08", stroke := "#6e4c08", width := 0.8 } ])
          , ("ballot", [ { d := "M5 3h14v18H5z", fill := "#f7edd2", stroke := "#553f26", width := 1.3 }
                       , { d := "M8 8l8 8M16 8l-8 8", stroke := "#a81d24", width := 2.4 } ])
          , ("hat", [ { d := "M2 15c3-8 7-8 10-5 3-3 7-3 10 5-2 2.500-6 3-10 3s-8-.500-10-3z", fill := "#17181c", stroke := "#f2bd2c", width := 1.2 }
                    , { d := "M10.500 10.500a1.800 1.800 0 1 0 3 0c-.500-1-2.500-1-3 0zM9.500 14l5-1.500M9.500 12.500l5 1.500", fill := "#f7f2e2", stroke := "#f7f2e2", width := 0.9 } ])
          , ("pardon", [ { d := "M6 4h11c1.500 0 2 1 2 2v12c0 1.500-1 2.500-2.500 2.500H7c1.500 0 2-1 2-2.500V6c0-1-1-2-3-2z", fill := "#f7edd2", stroke := "#553f26", width := 1.3 }
                       , { d := "M11.500 8h5M11.500 11h5", stroke := "#553f26", width := 1.1 }
                       , { d := "M14 13a2.800 2.800 0 1 0 .010 0z", fill := "#a81d24" } ])
          , ("sloop", [ { d := "M2.500 15h19l-2.500 4.500H5.500z", fill := "currentColor" }
                      , { d := "M12 2v12", stroke := "currentColor", width := 1.6 }
                      , { d := "M13.500 3c4 2.500 5 6.500 5 10h-5zM10.500 5c-3 2-4.500 5-4.500 8h4.500z", fill := "currentColor" } ])
          , ("wharf", [ { d := "M2 13h20v2.500H2z", fill := "currentColor" }
                      , { d := "M5 15.500V21M12 15.500V21M19 15.500V21", stroke := "currentColor", width := 2 }
                      , { d := "M7 13V8l5-4 5 4v5z", fill := "currentColor", opacity := 0.75 } ])
          , ("fort", [ { d := "M3 21V9h3v2.500h3V9h6v2.500h3V9h3v12z", fill := "currentColor" }
                     , { d := "M12 9V2.500", stroke := "currentColor", width := 1.6 }
                     , { d := "M12.500 2.500h6l-2 2 2 2h-6z", fill := "currentColor" }
                     , { d := "M10 21v-5a2 2 0 0 1 4 0v5z", fill := "#000000", opacity := 0.55 } ])
          , ("flagship", [ { d := "M2 15.500h20l-3 5H5z", fill := "currentColor" }
                         , { d := "M7 3v12M12 2v13M17 3v12", stroke := "currentColor", width := 1.3 }
                         , { d := "M4.500 5h5v3.500h-5zM4.500 9.500h5v4h-5zM9.500 4h5v4h-5zM9.500 9h5v5h-5zM14.500 5h5v3.500h-5zM14.500 9.500h5v4h-5z", fill := "#17181c", stroke := "currentColor", width := 0.7 } ])
          , ("privateer", [ { d := "M3 16h18l-2.500 4.500h-13z", fill := "currentColor" }
                          , { d := "M8.500 4v12M15.500 4v12", stroke := "currentColor", width := 1.3 }
                          , { d := "M5.500 5.500h6v8h-6zM12.500 5.500h6v8h-6z", fill := "#f7f2e2", stroke := "currentColor", width := 0.9 } ]) ] } }

end Look

end Charter.Games.PirateRepublic
