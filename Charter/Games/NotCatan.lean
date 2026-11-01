import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render

/-!
# Not Catan: as near to a famous board game as `GameDef` and the rule language get

The map, prices, piece limits, target, bank rate, stock and setup are exact. Everything else is a rough
copy made with founding laws, and each law's title says what it stands for. The gaps are the point:
`docs/process/not-catan.md` lists every feature, what was tried and what is missing from the language.
`Charter/Games/NotCatanTests.lean` plays each law and each rejected idea.

**How a law can see a 7.** A law cannot read the dice. But the map can hold a region that no tile
draws: `alarmRegion` pays one more resource, `alarm`, on a 7, to every piece on every corner. So a law
that reacts to a harvest of `alarm` reacts to a 7. The first law sends the alarm straight on to the
treasury, so no hand ever keeps it, and a treasury with alarm in it means "a 7 came up this round".
This is a counter, not a good: no piece costs it, so the screen and the Claude seats leave it out of
hands and trades (`markRes` in `Server/Spec.lean`).
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

/-- The region no tile draws: on a 7, it pays `alarm` to every piece on every corner. -/
def alarmRegion : Region := { res := "alarm", number := 7, spots := List.range spots.length }

/-! ## Small words for the laws -/

def held (p : Party) (r : Res) : Expr := .holding p (.lit r)

/-- All the goods a seat holds. Alarm and laurels do not count. -/
def handOf (p : Party) : Expr :=
  .add (held p "timber") (.add (held p "grain") (.add (held p "ore") (.add (held p "wool") (held p "brick"))))

/-- A 7 came up this round. -/
def alarmIsUp : Cond := .lt (.lit 0) (held .treasury "alarm")

/-! ## The founding laws -/

/-- **Rough copy of discarding on a 7.** The check comes at the end of the round, not at the roll, so a
seat whose turn is still to come can spend first. It takes half of each good, rounded down, not half of
the hand by the seat's own choice. The law also moves each payment of alarm to the treasury, and clears
it at the round's end. -/
def lawAlarm : Law :=
  { title := "A 7 rings the alarm: big hands lose half"
    clauses :=
      [ .onHarvest [.when (.harvestedIs "alarm") [.transfer .actor .treasury (.lit "alarm") .harvestedAmount]]
      , .onRoundEnd
          [ .forEach (.and alarmIsUp (.lt (.lit 7) (handOf .each)))
              (goods.map fun r => .transfer .each .bank (.lit r) (.div (held .each r) 2))
          , .transfer .treasury .bank (.lit "alarm") (held .treasury "alarm") ] ] }

/-- **Rough copy of the blocked hex.** No law can see which hex paid, and no seat can choose one. So
for the rest of a round with a 7, every seat at 5 points or more hands its harvests back. It hits the
leaders' whole income for a short time, not one hex for a long time. -/
def lawThief : Law :=
  { title := "The thief takes what the leaders harvest"
    clauses :=
      [ .onHarvest [.when (.and alarmIsUp (.and (.not (.harvestedIs "alarm")) (.le (.lit 5) (.points .actor))))
          [.transfer .actor .bank .harvested .harvestedAmount]] ] }

/-- One card from `each` to the builder, if `each` has none of `before`: the next good it holds. -/
def takeOneOf (before : List Res) : List Res → List Effect
  | [] => []
  | r :: rs =>
    let test : Cond := before.foldr (fun b acc => .and (.eq (held .each b) (.lit 0)) acc) (.lt (.lit 0) (held .each r))
    .when test [.transfer .each .actor (.lit r) (.lit 1)] :: takeOneOf (before ++ [r]) rs

/-- **Rough copy of the knight's theft.** A law cannot name one victim or pick at random. So a knight
takes one good from every seat ahead of the builder: ore if it has any, otherwise grain, otherwise wool.
A hand of only timber and brick is safe. -/
def lawKnight : Law :=
  { title := "A new knight robs every seat ahead"
    clauses :=
      [ .onBuild "knight" [.forEach (.lt (.points .actor) (.points .each)) (takeOneOf [] ["ore", "grain", "wool"])] ] }

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

/-- **Rough copy of the starting hand.** Setup pays nothing and no law runs in it. So at a round's end,
a seat that still has only its first two towns and an empty hand gets 3 goods. They are the same goods
for everyone, and they do not depend on where it settled. -/
def lawFirstHand : Law :=
  { title := "An empty first hand gets three goods"
    clauses :=
      [ .onRoundEnd [.forEach
          (.and (.eq (handOf .each) (.lit 0)) (.le (.add (.count .each "settlement") (.count .each "city")) (.lit 2)))
          [ .transfer .bank .each (.lit "timber") (.lit 1)
          , .transfer .bank .each (.lit "brick") (.lit 1)
          , .transfer .bank .each (.lit "grain") (.lit 1) ]] ] }

/-- One step of a harbor: 3 of `a` to the bank and 1 of `b` back, for a seat with a harbor and 4 more
`a` than `b`. -/
def harborStep (a b : Res) : Effect :=
  .when (.and (.lt (.lit 0) (.count .actor "harbor")) (.lt (.add (held .actor b) (.lit 3)) (held .actor a)))
    [.transfer .actor .bank (.lit a) (.lit 3), .transfer .bank .actor (.lit b) (.lit 1)]

/-- **Rough copy of a port.** A law cannot see a trade, and the bank has one rate for everyone. So a
harbor makes a swap by itself, when the dice pay its owner: 3 of a good it has too much of for 1 of the
next good along the line timber, brick, wool, grain, ore. The seat does not choose the good, and a harbor
can stand on any settlement. -/
def lawHarbor : Law :=
  { title := "A harbor swaps a surplus by itself"
    clauses :=
      [ .onHarvest
          [ harborStep "timber" "brick", harborStep "brick" "wool", harborStep "wool" "grain"
          , harborStep "grain" "ore" ] ] }

/-- The founding laws, in force from the first turn. A majority can repeal any of them. -/
def foundingLaws : List Law :=
  [lawAlarm, lawThief, lawKnight, lawLaurels, lawEmptyBank, lawFirstHand, lawHarbor]

/-! ## The game -/

/-- Not Catan: first to 10 points. A game cannot run for ever, so it stops at 30 rounds. -/
def game : GameDef where
  name := "Not Catan"
  resources :=
    [ ⟨"timber", 19⟩, ⟨"grain", 19⟩, ⟨"ore", 19⟩, ⟨"wool", 19⟩, ⟨"brick", 19⟩
    , ⟨"alarm", 200⟩, ⟨"laurel", 6⟩ ]
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
        placement := .attach "settlement", yield := 0, limit := 2 }
    , { name := "harbor", cost := [("timber", 1), ("brick", 1)], points := 0
        placement := .attach "settlement", yield := 0, limit := 2 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles ++ [alarmRegion] }
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

open Scene in
/-- A short jetty with a crane and a crate in the owner's colour. -/
def harborModel (seat : Nat) : List Part :=
  [ box 0 0 0 0.16 0.018 0.09 timberDark, box (-0.05) 0.018 0 0.014 0.14 0.014 timberDark
  , box (-0.01) 0.15 0 0.1 0.012 0.012 timberDark, box 0.045 0.018 0 0.04 0.04 0.04 (seatColor seat) ]

def theme : Scene.Theme :=
  { Scene.islandTheme with
    harbours := false
    ownModel := fun k seat =>
      if k == "knight" then some (knightModel seat)
      else if k == "relic" then some (relicModel seat)
      else if k == "wreath" then some (wreathModel seat)
      else if k == "harbor" then some (harborModel seat)
      else none
    look :=
      { marks := Scene.islandMarks ++
          [ ("laurel", "laurel"), ("alarm", "alarm"), ("knight", "knight"), ("relic", "relic")
          , ("wreath", "wreath"), ("harbor", "harbor") ] } }

end Charter.Games.NotCatan
