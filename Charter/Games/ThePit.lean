import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render
import Charter.Games.ThePit.Meshes

/-!
# The Pit

Chicago, 1886. Farms on the prairie send wheat to the Board of Trade, and traders shout in the octagonal
pit in the middle of its floor. There is no new machinery here. The market is made of parts every game
already has:

* **The spot price.** At each round's end, customers buy all the wheat held, for a fixed pot of gold
  split by share. So more wheat means a lower price, and the price comes out of what everyone does.
* **Futures.** A future is a deal: one signer pays wheat each round, and the other pays gold. The engine
  makes each payer put up everything they could owe before the deal starts. So nobody can sell wheat
  they do not have, and nobody can default.
* **The auction.** Each round, a membership of the Board goes to the highest bid. A bid is a public
  number a seat declares, and only gold in a seat's own hand backs it. Gold in a deal's deposit does
  not. So every future ties up capital.
* **The vault fee.** Gold in a hand pays a quarter each round. Gold in a deposit pays nothing, so a future
  is also a shelter, and sheltered gold cannot bid.
* **The opening bell.** Every seat starts with gold and wheat, into a glutted first market. Wheat sold at
  once fetches little; wheat sold forward can wait for a bigger pot.

Wheat in a hand is always sold at the round's end. Wheat in a deposit waits. So a future is also the
only way to keep wheat for a later round, when the pot is bigger.

The look uses mesh files. `packs/the-pit/gen.py` makes them and writes `Meshes.lean`.
-/

namespace Charter.Games.ThePit

open HexGrid

/-! ## The map: 19 hexes, with the Board of Trade in the middle -/

def hexes : List Hex := hexagon 2

/-- Resources in `hexes` order, after the middle: the inner ring, then the outer ring. 7 wheat,
6 lumber and 5 iron. -/
def tileResources : List Res :=
  [ "wheat", "lumber", "iron", "wheat", "lumber", "iron"
  , "wheat", "lumber", "iron", "wheat", "lumber", "wheat", "iron", "lumber", "wheat", "iron", "lumber", "wheat" ]

def tileNumbers : List Nat :=
  [ 6, 4, 5, 9, 8, 10
  , 10, 3, 11, 8, 9, 5, 6, 11, 3, 4, 12, 2 ]

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

/-! ## The founding laws -/

/-- What customers pay in all at this round's end: 4 gold, and 2 more each round. 6 in round 1, 24 in
round 10. -/
def pot : Expr := .add (.lit 4) (.mul (.lit 2) .round)

/-- All the wheat held at this moment, by everyone. Wheat in a deposit is not held. -/
def supply : Expr := .totalOver .yes (held .each "wheat")

/-- **The spot market.** All wheat in hand is sold at the round's end, and the pot is split by share.
The price of a wheat is the pot over the supply, so every seat that sells more lowers everyone's price.
If nobody holds wheat, nobody is paid. -/
def lawSpot : Law :=
  { title := "Customers buy all the wheat at each round's end, for a pot that grows each round"
    clauses :=
      [ .onRoundEnd [.forEach .yes
          [ pay .bank .each "gold" (.divBy (.mul pot (held .each "wheat")) supply)
          , pay .each .bank "wheat" (held .each "wheat") ]] ] }

/-- **The opening bell.** On the first roll of the game, every seat gets 8 gold and 4 wheat. The bell
in the treasury marks that it has rung. So round 1 opens with 16 wheat or more against a pot of 6: wheat
sold at once fetches very little, and wheat sold forward can wait for a bigger pot. -/
def lawBell : Law :=
  { title := "The opening bell: every trader starts with 8 gold and 4 wheat"
    clauses :=
      [ .onRoll
          [ .forEach (.eq (held .treasury "bell") (.lit 0)) [pay .bank .each "gold" (.lit 8), pay .bank .each "wheat" (.lit 4)]
          , .when (.eq (held .treasury "bell") (.lit 0)) [pay .bank .treasury "bell" (.lit 1)] ] ] }

/-- A seat's bid: the gold it declared, up to the gold in its own hand. -/
def bid (p : Party) : Expr := .min (said p "gold") (held p "gold")
/-- The highest bid. -/
def topBid : Expr := .mostOver .yes (bid .each)
/-- The highest bid below the top one, or 0. -/
def nextBid : Expr := .mostOver (.lt (bid .each) topBid) (bid .each)
/-- The memberships for sale this round: those on the desk, less one kept for each round still to come.
So a membership not sold in one round is sold in the next, and in round 10 all that are left are sold. -/
def lots : Expr := .sub (held .treasury "membership") (.sub (.lit 10) .round)
/-- One seat alone has the highest bid, and it is above 0. -/
def oneWinner : Cond :=
  .and (.lt (.lit 0) topBid) (.eq (.totalOver (.eq (bid .each) topBid) (.lit 1)) (.lit 1))

/-- The seat that wins this round's auction. -/
def wins : Cond := .and oneWinner (.eq (bid .each) topBid)

/-- **The auction.** The highest bid wins the lot, and pays 1 more than the next-highest bid. So a seat
can bid all it is willing to pay, and the order of turns matters less. A tie at the top sells nothing, and
the lot rolls over into the next round's. The Board keeps the memberships in the treasury, so the bank
cannot sell them. -/
def lawAuction : Law :=
  { title := "Each round, the highest bid buys the Board's memberships for sale"
    clauses :=
      [ .onRoundEnd [.forEach wins
          [ pay .each .bank "gold" (.add nextBid (.lit 1))
          , pay .treasury .each "membership" lots ]]
      , .onRoll [pay .bank .treasury "membership" (held .bank "membership")]
      , .setWorth "membership" 3 ] }

/-- **The vault fee.** Gold must work. At each round's end, every seat pays the bank a quarter of the gold in
its hand, rounded down. The auction's winner pays its price first, and the fee on what is left. Gold in a
deal's deposit is not in the hand, so it pays no fee. -/
def lawFee : Law :=
  { title := "Idle gold pays a quarter to the bank each round"
    clauses :=
      [ .onRoundEnd
          [ .forEach wins [pay .each .bank "gold" (.div (.sub (held .each "gold") (.add nextBid (.lit 1))) 4)]
          , .forEach (.not wins) [pay .each .bank "gold" (.div (held .each "gold") 4)] ] ] }

def foundingLaws : List Law := [lawSpot, lawBell, lawAuction, lawFee]

/-! ## The game -/

/-- `membership` is in an elevator's cost at 0 only so that the screen counts it as a good. The screen
leaves a resource that no piece costs out of hands and trades. -/
def game : GameDef where
  name := "The Pit"
  resources :=
    [ ⟨"wheat", 200⟩, ⟨"lumber", 120⟩, ⟨"iron", 120⟩, ⟨"gold", 600⟩, ⟨"membership", 10⟩, ⟨"bell", 1⟩ ]
  pieces :=
    [ { name := "rail", cost := [("lumber", 1), ("iron", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "farm", cost := [("lumber", 1), ("iron", 1), ("wheat", 1), ("gold", 1)], points := 1
        placement := .spot, yield := 1, limit := 6 }
    , { name := "elevator", cost := [("iron", 2), ("wheat", 2), ("gold", 2), ("membership", 0)], points := 2
        placement := .upgrade "farm", yield := 2, limit := 4 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 24
  rounds := 10
  bankRate := 3
  setupPieces := ["farm", "rail"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look -/

section Look
open Charter.Scene GpuCmd
open Meshes

/-- Firms that stand out against wheat, pine and rust: crimson, cobalt, cream, violet, then teal and
black. -/
def seats : List UInt32 := [0xD7263D, 0x2457E6, 0xF4F0E2, 0x8A3FE0, 0x16B8B0, 0x22201E]
def seat (i : Nat) : UInt32 := seats[i % 6]!

/-- One mesh in a model. A painted mesh is drawn in white. A white mesh is drawn in the seat's colour. -/
def m (id : UInt32) (x y z : Float) (rgb : UInt32 := 0xFFFFFF) (k : Float := 1) (rot : Float := 0) : Part :=
  { mesh := id, x, y, z, rot, sx := k, sy := k, sz := k, rgb }

/-- Brass knobs on a ridge, more of them for a later seat, so colour is not the only cue. -/
def tell (s : Nat) (x y z : Float) : List Part :=
  let knobs : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.045, 0.045]
    | _ => [-0.065, 0, 0.065]
  knobs.map fun u => ball (x + u) y z 0.034 0xF0C860

def farmModel (_seed s _round : Nat) : List Part :=
  ([m farmBody 0 0 0, m farmRoof 0 0 0 (seat s)] ++ tell s (-0.03) 0.19 0.01).map (·.scaled 1.3)

def elevatorModel (_seed s _round : Nat) : List Part :=
  [m elevatorBody 0 0 0, m elevatorPaint 0 0 0 (seat s)] ++ tell s (-0.04) 0.66 0.0

def railModel (s : Nat) : List Part :=
  let marks : List Float := match s % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.2, 0.2]
    | _ => [-0.3, 0, 0.3]
  [m railBed 0 0 0, m railTies 0 0 0 (seat s)] ++ marks.map fun u => box u 0.034 0 0.03 0.012 0.03 0xF0C860

/-- A link piece that a law made: a double track. -/
def doubleTrack (s : Nat) : List Part :=
  [{ m railBed 0 0 0 with sz := 1.8 }, { m railTies 0 0 0 (seat s) with sz := 1.8 }]

/-- A piece that a law made. The name's hash picks the shape. -/
def madeModel (name : String) (s : Nat) : List Part :=
  let id := match hashText name % 3 with
    | 0 => madeA
    | 1 => madeB
    | _ => madeC
  [m id 0 0 0 (seat s)] ++ tell s 0 0.38 0

def tileTop (res : Option Res) (seed : Nat) : List Part :=
  let turned : Float := pickFrom [0.0, pi / 3.0, -pi / 3.0, pi, 2.0 * pi / 3.0, -2.0 * pi / 3.0] seed 3
  match res with
  | some "wheat" => [m tileWheat 0 0 0 0xFFFFFF 1 (pickFrom [0.0, pi / 3.0, -pi / 3.0] seed 3)]
  | some "lumber" => [m tileLumber 0 0 0 0xFFFFFF 1 turned]
  | some "iron" => [m tileIron 0 0 0 0xFFFFFF 1 turned]
  | _ => [m tileFloor 0 0 0]

/-- Small things on a tile. The tall ones keep away from the number token. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (lowOk : Bool) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n 0.44 0.74).filter fun (x, z, _) => keep x z && (lowOk || !hidesToken x z)).flatMap fun (x, z, i) => f x z i
  match res with
  | some "wheat" => at_ 6 false fun x z i => [m shock x 0 z 0xFFFFFF (0.9 + 0.4 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "lumber" => at_ 9 false fun x z i =>
      if i % 4 == 0 then [m logs x 0 z 0xFFFFFF (0.9 + 0.3 * rnd seed i) (6.28 * rnd seed (i + 9))]
      else [m pine x 0 z 0xFFFFFF (0.85 + 0.7 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | some "iron" => at_ 6 false fun x z i =>
      if i % 3 == 0 then [m furnace x 0 z 0xFFFFFF (0.9 + 0.3 * rnd seed i)]
      else [m ore x 0 z 0xFFFFFF (0.8 + 0.6 * rnd seed i) (6.28 * rnd seed (i + 9))]
  | _ => []

/-- A law's monument, by what the law is about. A law that sets a worth or ends the game stands as a
repeal does: a gavel. -/
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

/-- The prairie, Lake Michigan, the city with the Board of Trade's tower, and a wheat train coming in. -/
def surround : List Cmd :=
  [ (m prairie 0 0 0).at 0 0 0, (m city 0 0 0).at 0 0 0, (m smoke 0 0 0 (withAlpha 0x6A625A 0.45)).at 0 0 0
  , (m train 0 0 0).at 0 0 0 ]

/-- The treasury is the secretary's desk. A certificate lies on it for each membership not yet sold. -/
def deskWithCertificates (total : Nat) : List Part :=
  let certs := (List.range (min total 12)).map fun i =>
    m certificate (0.02 * (i % 3).toFloat - 0.06) (0.14 + 0.007 * i.toFloat) (0.02 - 0.01 * (i % 2).toFloat) 0xFFFFFF 1 (0.12 * (i % 4).toFloat)
  m desk 0 0 0 :: certs

def theme : Theme :=
  { tableColor := 0x2A2012
    ground := fun
      | some "wheat" => 0x8C6A2A
      | some "lumber" => 0x24402A
      | some "iron" => 0x5C2E1E
      | _ => 0x5A3A20
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := surround
    under := fun _ => []
    shape := fun k => if k == "farm" then some .settlement else if k == "elevator" then some .city else none
    smallModel := farmModel
    largeModel := elevatorModel
    linkModel := fun k s => if k == "rail" then railModel s else doubleTrack s
    harbours := false
    madeModel := madeModel
    seats := seats
    meshDefs := defs
    meshTriangles := triangles
    tileTop := tileTop
    hotParts := [{ mesh := mHex, y := 0.002, sx := 0.93, sy := 0.006, sz := 0.93, rgb := withAlpha 0xFFE08A 0.3 }]
    monumentModel := monumentOf
    square := [m pit 0 0 0]
    roadside := fun _ => []
    treasury := deskWithCertificates
    flat := fun
      | some "wheat" => 0xD9AE45
      | some "lumber" => 0x3A6A40
      | some "iron" => 0x9A4A2C
      | _ => 0x7A5434
    look :=
      { tagline := "Every future is fully funded. Greed finds another way."
        bodyFont := "book"
        displayFont := "slab"
        tokens :=
          [ ("walnut-0", "#160f08"), ("walnut-1", "#21170d"), ("walnut-2", "#2e2114"), ("walnut-3", "#40301e"), ("brass", "#a8823a")
          , ("vellum", "#f1e7cc"), ("vellum-2", "#e5d7b3"), ("vellum-3", "#cfbd8d")
          , ("ink", "#1f170e"), ("ink-2", "#4f3f2a"), ("ink-3", "#77644a")
          , ("gold", "#e8bb4d"), ("gold-2", "#f6d985"), ("gold-ink", "#251a06")
          , ("wax", "#2f5a3c"), ("wax-2", "#3e7650"), ("wax-0", "#20402a"), ("pale", "#ece2c8"), ("pale-2", "#b0a283")
          , ("sign-ink", "#1d3a7a"), ("act-hover", "#3b2c1c"), ("act-hover-2", "#332517"), ("field", "#f8f0da")
          , ("bright", "#fffaea"), ("err-ink", "#fff4ef"), ("tool-off", "#7c6c54"), ("need", "#cdbf9c")
          , ("good", "#2f6b3c"), ("stain", "#7a5a24")
          , ("roll-0", "#4a3a24"), ("roll-1", "#685234"), ("roll-2", "#876d48"), ("roll-3", "#977c56"), ("roll-4", "#a68c66")
          , ("roll-5", "#bba67e"), ("roll-6", "#cfbc93"), ("roll-7", "#e5d7b3"), ("roll-8", "#f6ecd0") ]
        marks := []
        quietPieces := ["rail"]
        icons :=
          [ ("wheat", [ { d := "M12 22V7", stroke := "#7a5a18", width := 1.6 }
                      , { d := "M12 6c-2-1-2-3.500 0-4.500 2 1 2 3.500 0 4.500zM12 10.500c-2.500 0-4-2-4-4 2.500 0 4 2 4 4zM12 10.500c2.500 0 4-2 4-4-2.500 0-4 2-4 4zM12 15c-2.500 0-4-2-4-4 2.500 0 4 2 4 4zM12 15c2.500 0 4-2 4-4-2.500 0-4 2-4 4z", fill := "#e8bb4d", stroke := "#7a5a18", width := 1 } ])
          , ("lumber", [ { d := "M3 9h15v8H3z", fill := "#b8834a", stroke := "#4a2c12", width := 1.3 }
                       , { d := "M18 9a2.500 4 0 0 1 0 8 2.500 4 0 0 1 0-8z", fill := "#e0b67a", stroke := "#4a2c12", width := 1.2 }
                       , { d := "M18 11.500a1 1.500 0 0 1 0 3", stroke := "#4a2c12", width := 0.9 }
                       , { d := "M6 11.500h8M5 14.500h9", stroke := "#4a2c12", width := 0.9 } ])
          , ("iron", [ { d := "M4 17l3-8h10l3 8z", fill := "#6a6e76", stroke := "#22252a", width := 1.3 }
                     , { d := "M7 9l1.500-3h7L17 9", fill := "#8e98a3", stroke := "#22252a", width := 1.2 }
                     , { d := "M6 14h12", stroke := "#a8462a", width := 1.4 } ])
          , ("gold", [ { d := "M12 3a9 9 0 1 0 .010 0z", fill := "#e8bb4d", stroke := "#6e4c08", width := 1.4 }
                     , { d := "M12 6.500a5.500 5.500 0 1 0 .010 0z", stroke := "#6e4c08", width := 1.1 }
                     , { d := "M12 8.500v7M10 10c0-1 4-1 4 .500S10 12 10 13.500s4 1.500 4 .500", stroke := "#6e4c08", width := 1.3 } ])
          , ("membership", [ { d := "M4 4h16v16H4z", fill := "#f1e7cc", stroke := "#4f3f2a", width := 1.3 }
                           , { d := "M7 8h10M7 11h7", stroke := "#4f3f2a", width := 1.1 }
                           , { d := "M15 14a3 3 0 1 0 .010 0z", fill := "#8e1f2a" }
                           , { d := "M13.500 19l1.500-2 1.500 2", stroke := "#8e1f2a", width := 1.2 } ])
          , ("bell", [ { d := "M12 3c-3.500 0-5.500 2.500-5.500 6v4L4 17h16l-2.500-4V9c0-3.500-2-6-5.500-6z", fill := "#e8bb4d", stroke := "#6e4c08", width := 1.3 }
                     , { d := "M10 19a2 2 0 0 0 4 0", fill := "#6e4c08" } ])
          , ("rail", [ { d := "M4 4l4 16M20 4l-4 16", stroke := "currentColor", width := 1.8 }
                     , { d := "M5 7h14M5.700 11h12.600M6.500 15h11M7.300 19h9.400", stroke := "currentColor", width := 2.2 } ])
          , ("farm", [ { d := "M3 20V11l6-5 6 5v9z", fill := "currentColor" }
                     , { d := "M16 20v-9a3 2 0 0 1 6 0v9z", fill := "currentColor", opacity := 0.75 }
                     , { d := "M7.500 20v-4h3v4z", fill := "#000000", opacity := 0.55 } ])
          , ("elevator", [ { d := "M6 21V8l4-4 4 4v13z", fill := "currentColor" }
                         , { d := "M8.500 4.500V2h3v2.500", fill := "currentColor" }
                         , { d := "M14 21v-6h7v6z", fill := "currentColor", opacity := 0.75 }
                         , { d := "M8 11h4v2H8z", fill := "#000000", opacity := 0.55 } ]) ] } }

end Look

end Charter.Games.ThePit
