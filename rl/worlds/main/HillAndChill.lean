import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render
import Charter.Games.HillAndChill.Meshes

/-!
# Hill and Chill

Friends share a house on a hill, and every night they try to go out to dinner. Each round a seat can
declare that it is down, which commits it and costs it a ride and its share of the bill. Dinner only happens if more than half the
table is down. A seat that is not down is a "could be down", and that pays a little clout every round,
whatever happens. If too few commit, the ones who did pay the bill anyway, as a no-show fee. And if
everyone is down, nobody can agree on a place, so that falls through too. So somebody has to flake for
anybody to eat, nobody eats unless the table can trust each other, and the table talk is the group chat. All friends at any table are invented.

The look uses mesh files. `packs/hill-and-chill/gen.py` makes them and writes `Meshes.lean`.
-/

namespace Charter.Games.HillAndChill

open HexGrid

/-! ## The map: the house on the hill in the middle, and places to eat all around it -/

def hexes : List Hex := hexagon 2

/-- Resources in `hexes` order, after the middle: 5 gas, 4 cash, 4 boba and 5 takeout. -/
def tileResources : List Res :=
  [ "gas", "takeout", "boba", "cash", "gas", "takeout"
  , "boba", "cash", "gas", "takeout", "cash", "boba", "gas", "takeout", "boba", "cash", "takeout", "gas" ]

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

/-! ## Small words for the laws -/

def held (p : Party) (r : Res) : Expr := .holding p (.lit r)
def said (p : Party) (r : Res) : Expr := .declared p (.lit r)
def pay (a b : Party) (r : Res) (n : Expr) : Effect := .transfer a b (.lit r) n

/-- A seat is down when it has declared down this round. -/
def isDown : Cond := .le (.lit 1) (said .each "down")

/-- How many seats are down. -/
def downCount : Expr := .totalOver isDown (.lit 1)

/-- How many seats there are. -/
def tableSize : Expr := .totalOver .yes (.lit 1)

/-- How many seats must be down for dinner: more than half the table. -/
def needed : Expr := .add (.div tableSize 2) (.lit 1)

/-- Dinner happens when enough seats are down, but not all of them: when the whole house is down, nobody
can agree on a place. -/
def dinnerOn : Cond := .and (.le needed downCount) (.lt downCount tableSize)

/-- What each diner gets: 3 lore for each seat that was needed, shared by everyone who came. So a table
of exactly enough gets 3 each, and at a large table one more guest leaves less for everyone. -/
def share : Expr := .divBy (.mul (.lit 3) needed) downCount

/-! ## The founding laws -/

/-- **Could be down.** Every seat that is not down gets 1 clout at each round's end, whatever happens to
dinner. The house keeps the clout in the treasury, so the bank cannot sell it. -/
def lawMaybe : Law :=
  { title := "Could be down: 1 clout a round for not committing"
    clauses :=
      [ .onRoll [pay .bank .treasury "clout" (held .bank "clout")]
      , .onRoundEnd [.forEach (.not isDown) [pay .treasury .each "clout" (.lit 1)]]
      , .setWorth "clout" 1 ] }

/-- **Dinner.** Each seat holds one down card, so that it can declare down. At the round's end each seat
that is down pays the ride and its share of the bill, 1 gas and 1 cash, as far as it can, whether or not
dinner happens. The restaurant keeps the cash in the treasury: if too few came, it is the no-show fee.
If more than half the table is down, but not all of it, dinner happens, and they share the lore, 3 for
each seat that was needed. If everyone is down, nobody can agree on a place, and dinner falls through.
The house keeps the lore in the treasury, so the bank cannot sell it. -/
def lawDinner : Law :=
  { title := "Dinner happens if more than half the table is down, but not everyone"
    clauses :=
      [ .onRoll
          [ pay .bank .treasury "lore" (held .bank "lore")
          , .forEach (.eq (held .each "down") (.lit 0)) [pay .bank .each "down" (.lit 1)]
          , .forEach (.lt (.lit 1) (held .each "down")) [pay .each .bank "down" (.sub (held .each "down") (.lit 1))] ]
      , .onRoundEnd
          [ .forEach isDown [pay .each .bank "gas" (.lit 1), pay .each .treasury "cash" (.lit 1)]
          , .forEach (.and isDown dinnerOn) [pay .treasury .each "lore" share] ]
      , .setWorth "lore" 1 ] }

/-- **Hosting.** A potluck feeds everyone, not only the host. -/
def lawPotluck : Law :=
  { title := "Hosting a potluck gives every seat 1 lore"
    clauses := [.onBuild "potluck" [.forEach .yes [pay .treasury .each "lore" (.lit 1)]]] }

def foundingLaws : List Law := [lawMaybe, lawDinner, lawPotluck]

/-! ## The game -/

/-- Lore, clout and down are in a potluck's cost at 0 only so that the screen counts them as goods. The
screen leaves a resource no piece costs out of hands, and then nobody could see or declare them. -/
def game : GameDef where
  name := "Hill and Chill"
  resources :=
    [ ⟨"gas", 40⟩, ⟨"cash", 40⟩, ⟨"boba", 40⟩, ⟨"takeout", 40⟩
    , ⟨"down", 12⟩, ⟨"lore", 160⟩, ⟨"clout", 80⟩ ]
  pieces :=
    [ { name := "chat", cost := [("gas", 1), ("boba", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "booth", cost := [("takeout", 1), ("boba", 1), ("cash", 1)], points := 1
        placement := .spot, yield := 1, limit := 6 }
    , { name := "potluck"
        cost := [("takeout", 2), ("cash", 2), ("lore", 0), ("clout", 0), ("down", 0)]
        points := 2, placement := .upgrade "booth", yield := 2, limit := 4 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 20
  rounds := 8
  bankRate := 3
  setupPieces := ["booth", "chat"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look -/

section Look
open Charter.Scene GpuCmd
open Meshes

/-- Friends who stand out on a dusky hill: coral, sky blue, lime, violet, then gold and white. -/
def seats : List UInt32 := [0xFF5A4E, 0x3FA9F5, 0x9BE03A, 0xB06BFF, 0xFFC21F, 0xF4F1EA]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- Pale napkins that differ by seat, so colour is not the only cue. -/
def tell (s : Nat) (x y z : Float) : List Part :=
  let dots : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.045, 0.045]
    | _ => [-0.07, 0, 0.07]
  dots.map fun u => box (x + u) y z 0.03 0.012 0.03 0xFFF8EC

def boothModel (_seed s _round : Nat) : List Part :=
  [m boothBody 0 0 0, m boothTint 0 0 0 (seat s)] ++ tell s 0 0.165 0.0

def potluckModel (_seed s _round : Nat) : List Part :=
  [m potluckBody 0 0 0, m potluckTint 0 0 0 (seat s)] ++ tell s 0 0.104 0.09

/-- The group chat: bubbles in the seat's colour, and pale stones at its foot that differ by seat. -/
def chatModel (s : Nat) : List Part :=
  let marks : List Float := match s % 4 with
    | 0 => []
    | 1 => [0.12]
    | 2 => [-0.12, 0.12]
    | _ => [-0.36, -0.12, 0.12]
  [m chatBody 0 0 0, m chatTint 0 0 0 (seat s)] ++ marks.map fun u => box u 0.012 0 0.05 0.016 0.05 0xFFF8EC

/-- A link piece that a law made: a louder group chat. -/
def loudChat (s : Nat) : List Part :=
  [m chatBody 0 0 0, { m chatTint 0 0 0 (seat s) with sx := 1.0, sy := 1.4, sz := 1.8 }]

/-- A piece that a law made. The name's hash picks the shape. -/
def madeModel (name : String) (s : Nat) : List Part :=
  let id := match hashText name % 3 with
    | 0 => madeCart
    | 1 => madePicnic
    | _ => madeMic
  [m id 0 0 0 (seat s)] ++ tell s 0 0.27 0.1

def tileTop (res : Option Res) (_seed : Nat) : List Part :=
  match res with
  | some "gas" => [m tileGas 0 0 0]
  | some "cash" => [m tileCash 0 0 0]
  | some "boba" => [m tileBoba 0 0 0]
  | some "takeout" => [m tileTakeout 0 0 0]
  | _ => [m tileHill 0 0 0]

/-- Small things on a tile. The tall ones keep away from the number token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (lowOk : Bool) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n 0.42 0.7).filter fun (x, z, _) => keep x z && (lowOk || !hidesToken x z)).flatMap fun (x, z, i) => f x z i
  let tint : List UInt32 := [0xE84A3A, 0x3FA9F5, 0xF2F2F2, 0xFFC21F, 0x5A6ACF]
  match res with
  | some "gas" => at_ 5 true fun x z i =>
      if i % 3 == 0 then [m cone x 0 z 0xFFFFFF 1.2]
      else [m car x 0 z (pickFrom tint seed i) 1 (1.57 * rnd seed (i + 9))]
  | some "cash" => at_ 6 false fun x z i =>
      if i % 3 == 0 then [m lamp x 0 z 0xFFFFFF 1 (6.28 * rnd seed (i + 9))]
      else [m tree x 0 z 0xFFFFFF (0.8 + 0.5 * rnd seed i)]
  | some "boba" => at_ 6 true fun x z i =>
      if i % 2 == 0 then [m cup x 0 z 0xFFFFFF (1.0 + 0.4 * rnd seed i)]
      else [m flowers x 0 z 0xFFFFFF (1.0 + 0.5 * rnd seed i)]
  | some "takeout" => at_ 6 false fun x z i =>
      if i % 3 == 0 then [m picnic x 0 z 0xFFFFFF 1 (1.57 * rnd seed (i + 9))]
      else [m palm x 0 z 0xFFFFFF (0.8 + 0.5 * rnd seed i) (6.28 * rnd seed (i + 9))]
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

/-- The hill and the town lights below it. The ground covers the wooden table. -/
def surround : List Cmd :=
  [ (m hillside 0 0 0).at 0 0 0
  , (m townLights 0 0 0).at 0 0 0 ]

/-- A grassy rise under every tile, so the board reads as one hilltop. -/
def under (ts : List TileDef) : List Cmd :=
  ts.map fun t =>
    let (x, z) := t.hex.toPixel 1.0
    .draw mLand { pos := vec3 x 0.0 z, scale := vec3 1.2 0.13 1.2 } 0x4E7A3E 0

/-- The treasury is the restaurant's host stand. It keeps the no-show fees, and the house's lore and clout. -/
def reserve (total : Nat) : List Part :=
  let heap := (List.range (min total 40)).map fun i =>
    let a := 2.399963 * i.toFloat
    let r := 0.05 + 0.25 * Float.sqrt (i.toFloat / 40.0)
    m coin (0.12 + r * Float.cos a) (0.03 + 0.008 * (i % 3).toFloat) (0.28 + r * Float.sin a * 0.5) 0xFFFFFF 1.4 a
  m hostStand 0 0 0 :: heap

def theme : Theme :=
  { tableColor := 0x141024
    ground := fun
      | some "gas" => 0x3A3A44
      | some "cash" => 0x7AA84F
      | some "boba" => 0xF0C4D4
      | some "takeout" => 0xC9A26A
      | _ => 0x5E8F45
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := surround
    under := under
    shape := fun k => if k == "booth" then some .settlement else if k == "potluck" then some .city else none
    smallModel := boothModel
    largeModel := potluckModel
    linkModel := fun k s => if k == "chat" then chatModel s else loudChat s
    harbours := false
    madeModel := madeModel
    attachAngles := [-3.0 * pi / 4.0, -pi / 4.0, 3.0 * pi / 4.0]
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [m hotRing 0 (-0.0) 0]
    monumentModel := lawMonument
    square := [m squareHouse 0 0 0, m squareLights 0 0 0]
    roadside := fun _ => []
    treasury := reserve
    flat := fun
      | some "gas" => 0x55555F
      | some "cash" => 0x7AA84F
      | some "boba" => 0xE8A8C0
      | some "takeout" => 0xD4A35E
      | _ => 0x5E8F45
    look :=
      { tagline := "Could be down."
        bodyFont := "humanist"
        displayFont := "rounded"
        tokens :=
          [ ("walnut-0", "#0e0b1a"), ("walnut-1", "#161229"), ("walnut-2", "#221c3b"), ("walnut-3", "#322a52"), ("brass", "#c88a4a")
          , ("vellum", "#f6ead8"), ("vellum-2", "#efdcc4"), ("vellum-3", "#dcc2a2")
          , ("ink", "#24182e"), ("ink-2", "#55405e"), ("ink-3", "#7d6884")
          , ("gold", "#ffb347"), ("gold-2", "#ffd27a"), ("gold-ink", "#2a1606")
          , ("wax", "#d8406a"), ("wax-2", "#f0608a"), ("wax-0", "#a82a50"), ("pale", "#ece2f2"), ("pale-2", "#b3a6c4")
          , ("sign-ink", "#7a1a44"), ("act-hover", "#3a3060"), ("act-hover-2", "#2e264e"), ("field", "#fcf2e4")
          , ("bright", "#fff8ee"), ("err-ink", "#fff2f6"), ("tool-off", "#7c7290"), ("need", "#d4c4b4")
          , ("good", "#2a7a4a"), ("stain", "#8a5a3a")
          , ("roll-0", "#4c3858"), ("roll-1", "#6a5276"), ("roll-2", "#8a6e8e"), ("roll-3", "#9a7e98"), ("roll-4", "#aa8ea2")
          , ("roll-5", "#c2a6b0"), ("roll-6", "#d6bcbe"), ("roll-7", "#e8d2cc"), ("roll-8", "#f8e8de") ]
        marks := []
        quietPieces := ["chat"]
        icons :=
          [ ("gas", [ { d := "M5 21V5a2 2 0 0 1 2-2h6a2 2 0 0 1 2 2v16z", fill := "#e84a3a", stroke := "#5a1a14", width := 1.3 }
                    , { d := "M7 6h6v4H7z", fill := "#fff4e0" }
                    , { d := "M15 9l3 2v7a1.500 1.500 0 0 0 3 0V8l-2-3", stroke := "#5a1a14", width := 1.5 } ])
          , ("cash", [ { d := "M2.500 6.500h19v11h-19z", fill := "#6ccf7a", stroke := "#1e5a2a", width := 1.3 }
                     , { d := "M12 9a3 3 0 1 0 .010 0z", stroke := "#1e5a2a", width := 1.3 }
                     , { d := "M5 9v6M19 9v6", stroke := "#1e5a2a", width := 1.2 } ])
          , ("boba", [ { d := "M6 7h12l-1.500 14h-9z", fill := "#e8d4b8", stroke := "#5a3a2a", width := 1.3 }
                     , { d := "M5 5.500h14v2H5z", fill := "#f29bb8", stroke := "#5a3a2a", width := 1 }
                     , { d := "M13 5.500 15 1.500", stroke := "#d8406a", width := 1.8 }
                     , { d := "M9 18a1 1 0 1 0 .010 0zM12 19a1 1 0 1 0 .010 0zM15 18a1 1 0 1 0 .010 0zM10.500 16a1 1 0 1 0 .010 0zM13.500 16a1 1 0 1 0 .010 0z", fill := "#2a1a14" } ])
          , ("takeout", [ { d := "M5 9h14l-1.500 12h-11z", fill := "#f6f0e4", stroke := "#5a3a2a", width := 1.3 }
                        , { d := "M5 9l2-5h10l2 5", fill := "#f6f0e4", stroke := "#5a3a2a", width := 1.3 }
                        , { d := "M9 4.500 12 9l3-4.500", stroke := "#5a3a2a", width := 1.1 }
                        , { d := "M9 14h6v3H9z", fill := "#d8402a" } ])
          , ("down", [ { d := "M3 11h4v10H3z", fill := "#ffb347", stroke := "#2a1606", width := 1.2 }
                     , { d := "M7 11l4-7c1.500 0 2.500 1 2 3l-1 3h6c1.500 0 2.500 1.500 2 3l-2 6c-.500 1.500-1.500 2-3 2H7z", fill := "#ffd27a", stroke := "#2a1606", width := 1.3 } ])
          , ("lore", [ { d := "M3 6h18v13H3z", fill := "#f6ead8", stroke := "#24182e", width := 1.3 }
                     , { d := "M5 8h14v8H5z", fill := "#3a3060" }
                     , { d := "M5 16l4-4 3 3 2-2 5 3z", fill := "#9be03a" }
                     , { d := "M16 9.500a1.300 1.300 0 1 0 .010 0z", fill := "#fff2c0" } ])
          , ("clout", [ { d := "M12 2.500l2.800 6 6.500.700-4.900 4.400 1.400 6.400L12 16.800 6.200 20l1.400-6.400L2.700 9.200l6.500-.700z", fill := "#b06bff", stroke := "#2e1a4a", width := 1.3 }
                      , { d := "M12 7v6M12 15v.500", stroke := "#ffffff", width := 1.8 } ])
          , ("chat", [ { d := "M3 5h13a2 2 0 0 1 2 2v6a2 2 0 0 1-2 2H9l-4 4v-4H3z", fill := "currentColor" }
                     , { d := "M7 10a1 1 0 1 0 .010 0zM10.500 10a1 1 0 1 0 .010 0zM14 10a1 1 0 1 0 .010 0z", fill := "#000000", opacity := 0.55 } ])
          , ("booth", [ { d := "M3 9h4v12H3zM17 9h4v12h-4z", fill := "currentColor" }
                      , { d := "M7 13h10v2H7zM11 15h2v6h-2z", fill := "currentColor", opacity := 0.7 } ])
          , ("potluck", [ { d := "M2 13h20v2.500H2z", fill := "currentColor" }
                        , { d := "M4 15.500V21M20 15.500V21", stroke := "currentColor", width := 2 }
                        , { d := "M6 13a3 3 0 0 1 6 0zM13 13a3.500 2.500 0 0 1 7 0z", fill := "currentColor", opacity := 0.75 }
                        , { d := "M3 4c4 3 14 3 18 0", stroke := "currentColor", width := 1.2 } ]) ] } }

end Look

end Charter.Games.HillAndChill
