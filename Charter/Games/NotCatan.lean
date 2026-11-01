import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render

/-!
# Not Catan: as near to a famous board game as `GameDef` and the rule language get

The map, prices, piece limits, target, bank rate, stock and setup are exact. A few founding laws add
what the rule language can say well, and each law's title says what it does. The gaps are the point:
`docs/process/not-catan.md` lists every feature, what was tried and what is missing from the language.
`Charter/Games/NotCatanTests.lean` plays each law and each rejected idea.
-/

namespace Charter.Games.NotCatan

open HexGrid

/-- The goods, in the order a law looks at them. -/
def goods : List Res := ["timber", "grain", "ore", "wool", "brick"]

/-- The inner hexes, then the outer hexes, in `hexagon 2` order. The desert is in the middle, because
the laws' monuments stand on the first tile. -/
def hexes : List Hex := hexagon 2

/-- Resources in `hexes` order, after the desert. 4 timber, 4 grain, 4 wool, 3 brick, 3 ore. -/
def tileResources : List Res :=
  [ "timber", "wool", "brick", "grain", "wool", "grain"
  , "brick", "ore", "timber", "grain", "ore", "wool", "brick", "timber", "grain", "timber", "ore", "wool" ]

/-- Dice numbers in `hexes` order, after the desert: one 2, one 12, and two of each other number but 7.
No 6 or 8 touches another 6 or 8, and no number touches itself. -/
def tileNumbers : List Nat :=
  [ 6, 12, 3, 10, 11, 4
  , 9, 4, 8, 10, 11, 6, 5, 2, 9, 8, 5, 3 ]

/-- Every hex of the map, the desert first. -/
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

/-- All the goods a seat holds. Laurels do not count. -/
def handOf (p : Party) : Expr :=
  .add (held p "timber") (.add (held p "grain") (.add (held p "ore") (.add (held p "wool") (held p "brick"))))

/-! ## The founding laws

Each law is one definition here: its title, then its clauses. The list at the end is the order they
stand in. A majority can repeal any of them. -/

/-- **A 7.** It fires at the roll, for every seat at once. It takes half of each good, rounded down, not
half of the hand by the seat's own choice. -/
def lawSeven : Law :=
  { title := "A 7 costs big hands half"
    clauses :=
      [ .onRoll [.forEach (.and (.eq .rolled (.lit 7)) (.lt (.lit 7) (handOf .each)))
          (goods.map fun r => .transfer .each .bank (.lit r) (.div (held .each r) 2))] ] }

/-- **Rough copy of a knight.** A law cannot name one victim or pick at random. So a new knight takes 1
ore from every seat ahead of the builder. -/
def lawKnight : Law :=
  { title := "A new knight takes ore from each seat ahead"
    clauses :=
      [ .onBuild "knight" [.forEach (.and (.lt (.points .actor) (.points .each)) (.lt (.lit 0) (held .each "ore")))
          [.transfer .each .actor (.lit "ore") (.lit 1)]] ] }

/-- **Rough copy of the two big awards.** A law cannot give points, and pieces never move. So the third
knight or the sixth road pays enough laurels for a wreath, worth 2 points for good. There are laurels
for only two wreaths, and a spent wreath's laurels go to the treasury. A loophole: while the bank holds
laurels, a seat can buy them at the bank's rate. -/
def lawLaurels : Law :=
  { title := "The third knight or sixth road earns a wreath"
    clauses :=
      [ .onBuild "knight" [.when (.eq (.count .actor "knight") (.lit 2)) [.transfer .bank .actor (.lit "laurel") (.lit 3)]]
      , .onBuild "road" [.when (.eq (.count .actor "road") (.lit 5)) [.transfer .bank .actor (.lit "laurel") (.lit 3)]]
      , .onBuild "wreath" [.transfer .bank .treasury (.lit "laurel") (.lit 3)] ] }

/-- **Rough copy of the rule for a short bank.** After a harvest that leaves the bank with none of a
good, everyone paid that good on that roll gives it back. It is wrong when the payment emptied the bank
exactly, and it misses a short payment that left a remainder. -/
def lawEmptyBank : Law :=
  { title := "A harvest that empties the bank pays nobody"
    clauses :=
      [ .onHarvest [.when (.eq (.holding .bank .harvested) (.lit 0))
          [.transfer .actor .bank .harvested .harvestedAmount]] ] }

/-- The founding laws, in force from the first turn. -/
def foundingLaws : List Law :=
  [lawSeven, lawKnight, lawLaurels, lawEmptyBank]

/-! ## The game -/

/-- Not Catan: first to 10 points. A game cannot run for ever, so it stops at 30 rounds. -/
def game : GameDef where
  name := "Not Catan"
  resources :=
    [ ⟨"timber", 19⟩, ⟨"grain", 19⟩, ⟨"ore", 19⟩, ⟨"wool", 19⟩, ⟨"brick", 19⟩
    , ⟨"laurel", 6⟩ ]
  pieces :=
    [ { name := "road", cost := [("timber", 1), ("brick", 1)], points := 0
        placement := .link, yield := 0, limit := 15 }
    , { name := "settlement", cost := [("timber", 1), ("brick", 1), ("grain", 1), ("wool", 1)]
        points := 1, placement := .spot, yield := 1, limit := 5 }
    , { name := "city", cost := [("grain", 2), ("ore", 3)], points := 2
        placement := .upgrade "settlement", yield := 2, limit := 4 }
    , { name := "knight", cost := [("ore", 1), ("wool", 1), ("grain", 1)], points := 0
        placement := .attach "settlement", yield := 0, limit := 5 }
    , { name := "relic", cost := [("ore", 3), ("wool", 3), ("grain", 3)], points := 1
        placement := .attach "settlement", yield := 0, limit := 2 }
    , { name := "wreath", cost := [("laurel", 3)], points := 2
        placement := .attach "settlement", yield := 0, limit := 2 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 10
  rounds := 30
  bankRate := 4
  lawFee := [("grain", 1), ("wool", 1)]
  setupPieces := ["settlement", "road"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look

The Island's terrain and towns. The Island's piers are left out, since they would look like ports the
game does not have. The small pieces stand beside a town and stay smaller than it, so the towns still
read first. -/

open Scene in
/-- A foot soldier in the owner's colour, with a spear. -/
def knightModel (seat : Nat) : List Part :=
  [ cyl 0 0 0 0.065 0.018 stoneDark, cone 0 0.018 0 0.06 0.16 (seatColor seat)
  , ball 0 0.17 0 0.06 plaster, box 0.055 0 0 0.008 0.24 0.008 ink, cone 0.055 0.24 0 0.014 0.035 stone ]

open Scene in
/-- A small gold needle on a plinth. -/
def relicModel (_seat : Nat) : List Part :=
  [ box 0 0 0 0.1 0.025 0.1 marble, pyr 0 0.025 0 0.042 0.22 gold ]

open Scene in
/-- A green ring on a post, with the owner's colour in the middle. -/
def wreathModel (seat : Nat) : List Part :=
  [ box 0 0 0 0.08 0.02 0.08 marble, cyl 0 0.02 0 0.012 0.13 stoneDark
  , cyl 0 0.15 0 0.085 0.018 0x4F8042, cyl 0 0.16 0 0.05 0.016 (seatColor seat) ]

def theme : Scene.Theme :=
  { Scene.islandTheme with
    harbours := false
    ownModel := fun k seat =>
      if k == "knight" then some (knightModel seat)
      else if k == "relic" then some (relicModel seat)
      else if k == "wreath" then some (wreathModel seat)
      else none
    look :=
      { marks := Scene.islandMarks ++
          [("laurel", "laurel"), ("knight", "knight"), ("relic", "relic"), ("wreath", "wreath")] } }

end Charter.Games.NotCatan
