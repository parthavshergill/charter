import Charter.Engine
import Charter.Games.NotCatan

/-!
# Not Catan, played

The first part checks the parts that are exact. The second plays each founding law through
`Engine.step`. The third tries the ideas that are not in the pack, and shows why each is left out.
`docs/process/not-catan.md` reads these results.

The tables here are built by hand, with the pieces and hands each test needs. Whole games are in
`scripts/smoke.py` and `make sim`.
-/

namespace Charter.Games.NotCatan.Tests

open Charter Charter.Engine

abbrev G : GameDef := game
abbrev St := State game

def fresh (seats : Nat := 4) : St := initialState game seats 1 [2]

/-! ## The parts that are exact -/

def countOf (x : Res) : Nat := (tileResources.filter (· == x)).length
def numberCount (n : Nat) : Nat := (tileNumbers.filter (· == n)).length

#guard hexes.length == 19 && tiles.length == 19
#guard [countOf "timber", countOf "wool", countOf "grain", countOf "brick", countOf "ore"] == [4, 4, 4, 3, 3]
#guard (tiles.filter (·.res.isNone)).length == 1 && (tiles.head?.bind (·.res)).isNone
#guard (List.range 13).map numberCount == [0, 0, 1, 2, 2, 2, 2, 0, 2, 2, 2, 2, 1]
#guard spots.length == 54 && links.length == 72

/-- Two tiles share a side. -/
def touching (a b : TileDef) : Bool := (a.hex.neighbors).contains b.hex

-- No 6 or 8 touches another, and no two tiles with the same number or resource touch.
#guard tiles.all fun a => tiles.all fun b =>
  !touching a b ||
    (a.number != b.number && a.res != b.res &&
      !([some 6, some 8].contains a.number && [some 6, some 8].contains b.number))

#guard (game.resources.filter (goods.contains ·.name)).all (·.stock == 19)
#guard game.bankRate == 4 && game.targetPoints == 10 && game.diceCount == 2 && game.diceSides == 6
#guard game.setupPieces == ["settlement", "road"]
#guard (game.pieces.find? (·.name == "road")).map (fun d => (d.cost, d.limit, d.points)) ==
  some ([("timber", 1), ("brick", 1)], 15, 0)
#guard (game.pieces.find? (·.name == "settlement")).map (fun d => (d.cost, d.limit, d.points)) ==
  some ([("timber", 1), ("brick", 1), ("grain", 1), ("wool", 1)], 5, 1)
#guard (game.pieces.find? (·.name == "city")).map (fun d => (d.cost, d.limit, d.points)) ==
  some ([("grain", 2), ("ore", 3)], 4, 2)

/-! ## Setup cannot get stuck, unless a seat chooses a place with no free link

At 4 seats, the last setup turn sees at most 7 settlements and 7 roads. A settlement blocks at most 4
spots, so at least 54 - 28 = 26 spots are free. A free spot with no free link has all its links taken,
and that needs 2 or more road ends, and the 7 roads have 14 ends. So at most 7 free spots are shut, and
a seat always has a spot with a free link. The same count holds at 3 seats. -/

#guard (List.range game.map.spotCount).all fun v => 2 ≤ ((fresh).neighbours v).length ∧ ((fresh).neighbours v).length ≤ 3
#guard 7 * 4 + 7 < game.map.spotCount

def placeAt (p : Seat) (k : PieceKind) (v : Nat) : Event := .move p (.place k (.spot v))
def placeOn (p : Seat) (k : PieceKind) (a b : Nat) : Event := .move p (.place k (.link (a, b)))
def endT (p : Seat) : Event := .move p .endTurn

/-- The Island's blocked road, which works here too, since the two maps have the same shape. Three
seats spend their roads around seat 0, and seat 0 then chooses a spot with no free link. It loses that
free road. It had other spots to choose, and the game does not stall. -/
def blockedRoadGame : List Event :=
  [ placeAt 0 "settlement" 25, placeOn 0 "road" 24 25, endT 0
  , placeAt 1 "settlement" 7, placeOn 1 "road" 24 7, endT 1
  , placeAt 2 "settlement" 11, placeOn 2 "road" 28 11, endT 2
  , placeAt 3 "settlement" 27, placeOn 3 "road" 26 27, endT 3
  , placeAt 3 "settlement" 42, placeOn 3 "road" 25 26, endT 3
  , placeAt 2 "settlement" 46, placeOn 2 "road" 28 29, endT 2
  , placeAt 1 "settlement" 50, placeOn 1 "road" 29 24, endT 1
  , placeAt 0 "settlement" 29 ]

#guard match (replay game 4 1 [2] blockedRoadGame).toOption with
  | some s => (legalMoves game s 0).all (· == .endTurn) && (step game s (endT 0)).toOption.isSome
  | none => false

/-! ## A table to test on -/

/-- No region, for reading past the end of the list. -/
def noRegion : Region := ⟨"", 0, []⟩

/-- A corner of the `i`th producing tile. -/
def cornerOf (i j : Nat) : Nat := ((game.map.regions.getD i noRegion).spots).getD j 0

/-- Corners far apart: seat `i` has a settlement on tile `i`. -/
def townOf (seat : Seat) : Nat := cornerOf (seat * 3) 0

def towns (seats : List Seat := [0, 1, 2, 3]) : List Piece :=
  seats.map fun p => ⟨p, "settlement", .spot (townOf p)⟩

/-- Hand a seat some goods from the bank. -/
def give (s : St) (p : Seat) (b : Bundle) : St :=
  { s with books := (s.books.postAll (b.map fun x => ⟨.bank, .player p, x.1, x.2, .trade⟩)).getD s.books }

def table (pieces : List Piece := towns) : St :=
  { fresh with phase := .actions, pieces := pieces }

/-- The next roll is this number. -/
def rolling (s : St) (r : Nat) : St :=
  { s with rollsMade := ((List.range 500).find? (fun k => rollAt game s.seed k == r)).getD 0 }

def afterTurn (s : St) : Option St := (step game s .forceEndTurn).toOption

def holds (s : St) (p : Seat) (r : Res) : Nat := s.balance (.player p) r
def handSize (s : St) (p : Seat) : Nat := (goods.map (holds s p)).sum

/-! ## The founding laws, played -/

-- Every law passes `lawProblems` at the seats the pack supports, in order. `game_valid` says the same.
#guard (foundingLaws.foldl (fun (acc : Bool × List (Nat × Law) × Nat) L =>
    ((acc.1 && (lawProblems game { fresh with laws := acc.2.1 } L).isEmpty), enact acc.2.1 acc.2.2 L, acc.2.2 + 1))
  (true, [], 0)).1

-- The pack leaves room for a table's own laws and pieces.
#guard foundingLaws.length == 4 && game.pieces.length == 6 && game.resources.length == 6
#guard plannedTotal game.startingLaws 4 == 28 && plannedTotal game.startingLaws 6 == 40

/-- Seat 0 holds 9 goods, seat 1 holds 7, seat 2 holds 8 of one good. All have towns, and no hex has a 7. -/
def rich : St :=
  give (give (give (table) 0 [("timber", 3), ("grain", 3), ("ore", 3)]) 1 [("timber", 7)]) 2 [("wool", 8)]

-- No hex pays on a 7: the bank's harvest is empty, whoever has towns on the map.
#guard !tiles.any (·.number == some 7) && !game.map.regions.any (·.number == 7)
#guard (baseHarvest (rolling rich 7) 7).isEmpty

-- The 7 law fires at the roll, with no hex paying. A hand of 9 loses half of each good, rounded down. A hand
-- of 7 loses nothing. A hand of 8 in one good loses 4. It happens on the first turn of the round, not at its end.
#guard match afterTurn (rolling rich 7) with
  | some s =>
    s.lastRoll == some 7 && s.round == 1 &&
      [holds s 0 "timber", holds s 0 "grain", holds s 0 "ore"] == [2, 2, 2] &&
      holds s 1 "timber" == 7 && holds s 2 "wool" == 4 &&
      handSize s 3 == 0
  | none => false

-- What was taken is in the bank, and in the journal as the law's payment.
#guard match afterTurn (rolling rich 7) with
  | some s => s.balance .bank "wool" == 19 - 4 && s.balance .treasury "wool" == 0
  | none => false

-- Half of each good, rounded down, is not half of the hand: (2,2,2,1,1) loses 3 of 8, not 4.
#guard match afterTurn (rolling (give (table) 0
    [("timber", 2), ("grain", 2), ("ore", 2), ("wool", 1), ("brick", 1)]) 7) with
  | some s => handSize s 0 == 5
  | none => false

-- Laurels do not count toward the hand, and the law does not take them.
#guard match afterTurn (rolling (give (table) 0 [("timber", 7), ("laurel", 3)]) 7) with
  | some s => holds s 0 "timber" == 7 && holds s 0 "laurel" == 3
  | none => false

-- Any other roll costs nobody anything. A 12 pays a hex that no test town stands on.
#guard match afterTurn (rolling (give (give (table []) 0 [("timber", 9)]) 2 [("wool", 8)]) 12) with
  | some s => holds s 0 "timber" == 9 && holds s 2 "wool" == 8
  | none => false

/-- Seat 0 is behind seats 1 and 2 and level with seat 3, and it can pay for a knight. -/
def knightTable : St :=
  give (give (give (give
    (table (towns ++ [⟨1, "city", .spot 90⟩, ⟨2, "city", .spot 91⟩]))
    0 [("ore", 1), ("wool", 1), ("grain", 1)]) 1 [("ore", 2), ("wool", 2)]) 2 [("brick", 1)]) 3 [("ore", 1)]

def buildKnight (s : St) : Option St := (step game s (placeAt 0 "knight" (townOf 0))).toOption

-- A knight takes 1 ore from each seat ahead. A seat ahead with no ore pays nothing, and a seat level with
-- the builder loses nothing.
#guard match buildKnight knightTable with
  | some s => holds s 0 "ore" == 1 && holds s 1 "ore" == 1 && holds s 1 "wool" == 2 &&
      holds s 2 "brick" == 1 && holds s 3 "ore" == 1
  | none => false

/-- Seat 0 has 2 knights, and can pay for a third. -/
def twoKnights : St :=
  give (table ((towns) ++ [⟨0, "settlement", .spot (cornerOf 2 3)⟩, ⟨0, "knight", .spot (townOf 0)⟩,
      ⟨0, "knight", .spot (cornerOf 2 3)⟩, ⟨0, "settlement", .spot (cornerOf 4 3)⟩]))
    0 [("ore", 1), ("wool", 1), ("grain", 1)]

-- The third knight pays 3 laurels. A wreath then costs them, and is worth 2 points.
#guard match (step game twoKnights (placeAt 0 "knight" (cornerOf 4 3))).toOption with
  | some s =>
    holds s 0 "laurel" == 3 &&
    match (step game s (placeAt 0 "wreath" (townOf 0))).toOption with
    | some t => holds t 0 "laurel" == 0 && t.balance .treasury "laurel" == 3 && t.balance .bank "laurel" == 3 &&
        t.pointsOf 0 == s.pointsOf 0 + 2
    | none => false
  | none => false

-- There are laurels for two wreaths only. The third seat to earn them gets none.
#guard match (step game { twoKnights with
      books := (twoKnights.books.postAll [⟨.bank, .treasury, "laurel", 6, .trade⟩]).getD twoKnights.books }
    (placeAt 0 "knight" (cornerOf 4 3))).toOption with
  | some s => holds s 0 "laurel" == 0
  | none => false

-- A loophole we did not close: a seat can buy laurels from the bank at the bank's rate.
#guard match (step game (give (table) 0 [("ore", 4)]) (.move 0 (.bankTrade "ore" "laurel"))).toOption with
  | some s => holds s 0 "laurel" == 1
  | none => false

/-- What the first tile pays, and its number. -/
def firstTile : Region := game.map.regions.getD 0 noRegion

-- A harvest that empties the bank pays nobody. Seats 0 and 1 are paid 1 each, from a bank that holds 2.
def lowBank (n : Nat) : St :=
  let t := table [⟨0, "settlement", .spot (cornerOf 0 0)⟩, ⟨1, "settlement", .spot (cornerOf 0 2)⟩]
  { t with books := (t.books.postAll [⟨.bank, .treasury, firstTile.res, 19 - n, .trade⟩]).getD t.books }

-- Wrong, and a known gap: the bank could pay both of them, and the law still takes it back.
#guard match afterTurn (rolling (lowBank 2) firstTile.number) with
  | some s => holds s 0 firstTile.res == 0 && holds s 1 firstTile.res == 0
  | none => false
-- Right: the bank is short, and it pays nobody. By itself, the engine would pay neither too, since 1 of 2 rounds down.
#guard match afterTurn (rolling (lowBank 1) firstTile.number) with
  | some s => holds s 0 firstTile.res == 0 && holds s 1 firstTile.res == 0
  | none => false
-- A bank with enough pays as usual.
#guard match afterTurn (rolling (lowBank 3) firstTile.number) with
  | some s => holds s 0 firstTile.res == 1 && holds s 1 firstTile.res == 1
  | none => false

/-! ## What is not in the pack, and why

Each idea here is a real law. `problems` runs the real check. -/

def problems (L : Law) (seats : Nat := 4) : List String := lawProblems game (fresh seats) L

def withLaw (s : St) (L : Law) : St := { s with laws := s.laws ++ [(99, L)] }

/-! ### Cut to make the laws panel shorter

Both of these work. An earlier version of the pack had them. In the two stopped Claude games, the first never
fired and nobody built the second, and each took several long lines on the screen. -/

/-- Setup pays nothing and no law runs in it. So at a round's end, a seat with only its first two towns and an
empty hand gets 3 goods. They are the same goods for everyone. -/
def firstHand : Law :=
  { title := "An empty first hand gets three goods"
    clauses :=
      [ .onRoundEnd [.forEach
          (.and (.eq (handOf .each) (.lit 0)) (.le (.add (.count .each "settlement") (.count .each "city")) (.lit 2)))
          [ .transfer .bank .each (.lit "timber") (.lit 1)
          , .transfer .bank .each (.lit "brick") (.lit 1)
          , .transfer .bank .each (.lit "grain") (.lit 1) ]] ] }

#guard (problems firstHand).isEmpty

def firstHandTable : St :=
  withLaw (give (table ([⟨0, "settlement", .spot 90⟩, ⟨0, "settlement", .spot 91⟩, ⟨1, "settlement", .spot 92⟩,
      ⟨2, "settlement", .spot 93⟩, ⟨2, "settlement", .spot 94⟩, ⟨2, "settlement", .spot 95⟩])) 1 [("ore", 1)]) firstHand

#guard match afterTurn (rolling { firstHandTable with turnIndex := 3 } 2) with
  | some s => handSize s 0 == 3 && holds s 0 "timber" == 1 && handSize s 1 == 1 && handSize s 2 == 0
  | none => false

/-- 3 of `a` to the bank and 1 of `b` back, for a seat with a harbor and 4 more `a` than `b`. -/
def harborStep (a b : Res) : Effect :=
  .when (.and (.lt (.lit 0) (.count .actor "harbor")) (.lt (.add (held .actor b) (.lit 3)) (held .actor a)))
    [.transfer .actor .bank (.lit a) (.lit 3), .transfer .bank .actor (.lit b) (.lit 1)]

/-- A port as far as a law can say it. A law cannot see a trade, and the bank has one rate for everyone. So a
harbor swaps by itself when the dice pay its owner. The seat does not choose the good, and a harbor can stand
on any settlement. -/
def harborLaw : Law :=
  { title := "A harbor swaps a surplus by itself"
    clauses :=
      [ .newPiece { name := "harbor", cost := [("timber", 1), ("brick", 1)], points := 0
                    placement := .attach "settlement", yield := 0, limit := 2 }
      , .onHarvest
          [ harborStep "timber" "brick", harborStep "brick" "wool", harborStep "wool" "grain"
          , harborStep "grain" "ore" ] ] }

#guard (problems harborLaw).isEmpty

def harborTable (hasHarbor : Bool) : St :=
  withLaw (give (table ([⟨0, "settlement", .spot (cornerOf 0 0)⟩] ++
    if hasHarbor then [⟨0, "harbor", .spot (cornerOf 0 0)⟩] else [])) 0 [("wool", 5)]) harborLaw

#guard match afterTurn (rolling (harborTable true) firstTile.number) with
  | some s => holds s 0 "wool" == 2 && holds s 0 "grain" == 1
  | none => false
#guard match afterTurn (rolling (harborTable false) firstTile.number) with
  | some s => holds s 0 "wool" == 5 && holds s 0 "grain" == 0
  | none => false

/-! ### A port with its own rate

The bank has one rate, for everyone, and a law cannot see a trade. So a cheaper rate for one seat cannot be
said. A law can only change the rate for all. -/

def threeForOne : Law := { title := "Everyone trades at 3", clauses := [.setBankRate 3] }
#guard (problems threeForOne).isEmpty

/-! ### A card that does one of several things

A seat cannot choose a good when it plays a card, and a law cannot draw at random. A piece for each choice
would use up the pieces: a game has at most 8 kinds, and the pack uses 6. So a "card" can only do a fixed
thing, or a thing that depends on what the bank holds, which every seat can see coming. -/

def piece (name : String) (cost : Bundle) : Clause :=
  .newPiece { name, cost, points := 0, placement := .attach "settlement", yield := 0, limit := 2 }

/-- A monopoly on one fixed good. -/
def monopolyOnOre : Law :=
  { title := "Everyone's ore"
    clauses := [piece "decree" [("ore", 1), ("wool", 1), ("grain", 1)],
      .onBuild "decree" [.forEach .yes [.transfer .each .actor (.lit "ore") (held .each "ore")]]] }

/-- Two free goods, always the same two. -/
def plentyFixed : Law :=
  { title := "Two free goods"
    clauses := [piece "almanac" [("ore", 1), ("wool", 1), ("grain", 1)],
      .onBuild "almanac" [.transfer .bank .actor (.lit "ore") (.lit 1), .transfer .bank .actor (.lit "grain") (.lit 1)]] }

/-- The goods for two roads. -/
def freeRoads : Law :=
  { title := "Two roads' worth"
    clauses := [piece "survey" [("ore", 1), ("wool", 1), ("grain", 1)],
      .onBuild "survey" [.transfer .bank .actor (.lit "timber") (.lit 2), .transfer .bank .actor (.lit "brick") (.lit 2)]] }

/-- A card whose effect depends on the bank's ore, as a stand-in for a draw. Every seat can count it first. -/
def bankDraw : Law :=
  let rest : Expr := .sub (held .bank "ore") (.mul (.div (held .bank "ore") 3) (.lit 3))
  { title := "A draw from the bank's ore"
    clauses := [piece "card" [("ore", 1), ("wool", 1), ("grain", 1)],
      .onBuild "card"
        [ .when (.eq rest (.lit 0)) [.transfer .bank .actor (.lit "timber") (.lit 2), .transfer .bank .actor (.lit "brick") (.lit 2)]
        , .when (.eq rest (.lit 1)) [.forEach .yes [.transfer .each .actor (.lit "wool") (held .each "wool")]]
        , .when (.eq rest (.lit 2)) [.transfer .bank .actor (.lit "ore") (.lit 1), .transfer .bank .actor (.lit "grain") (.lit 1)] ]] }

#guard (problems monopolyOnOre).isEmpty && (problems plentyFixed).isEmpty && (problems freeRoads).isEmpty && (problems bankDraw).isEmpty

-- It works when played: seat 0 takes all of everyone's ore.
#guard match (step game (give (give (withLaw (table) monopolyOnOre) 0 [("ore", 1), ("wool", 1), ("grain", 1)]) 1 [("ore", 4)])
    (placeAt 0 "decree" (townOf 0))).toOption with
  | some s => holds s 0 "ore" == 4 && holds s 1 "ore" == 0
  | none => false

-- Only two more kinds of piece fit, so three of these cards cannot all pass.
#guard (lawProblems game { fresh with laws := game.startingLaws ++ [(90, monopolyOnOre), (91, plentyFixed)] } freeRoads).contains
  "there would be too many kinds of piece"

/-! ### An award that moves

Points come from pieces. Pieces never move, no law can remove one, and `setPoints` changes a kind for
everyone. So a seat cannot lose an award to a rival. This law gives every wreath 0 points, for everyone. -/

def wreathsWorthNothing : Law := { title := "No more wreaths", clauses := [.setPoints "wreath" 0] }
#guard (problems wreathsWorthNothing).isEmpty

/-! ### What the law language cannot say at all

There is no text to check for these. `Trigger` has no trade. A law can read the total rolled, but `Expr` has
no round, and a harvest does not say which hex paid. `Party` has no way to name a seat. `Cond` has no "for all
seats". `Effect` moves resources and nothing else: it cannot move or remove a piece, skip a seat's harvest, or
ask a seat to choose. `Placement` has no way to restrict a piece to the coast. Hands are public, so no card can
be secret. -/

end Charter.Games.NotCatan.Tests
