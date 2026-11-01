import Charter.Words
import Charter.Games.HexMap

/-!
# Omertà

A crime family shares one city. Fronts are shops on the street corners, and a racket runs in the back
room of a front. Rackets pay the family every round, and the more rackets run, the faster the district
attorney's reward for a witness grows. The reward sits in the treasury, where everyone can watch it grow.

A seat that runs a racket through a round's end gets dirt. On your turn you can talk: declare your dirt.
At the next roll of the dice you take the whole reward, or half of it at the round's end if you were last. Then the police
close every racket of yours, and every other seat that runs a racket loses its newest one.

The engine has no hidden information and no secret moves, so the oath is spoken across the table. The
board only keeps score of who kept it.

## Turn order

A seat declares only on its own turn, and the order of seats never changes. So a law that pays at the
round's end lets the last seat see everyone's choice and talk with no risk. Here the reward goes to the
first seat that talks, at the next roll, before anyone else can answer. The reward also grows on every
roll, not only at the round's end. So the first seat of a round gets the first chance, and a later seat
gets a larger reward, and neither is safe. The last seat sees everything, so a talk at the round's end
pays only half, and the rest waits in the treasury.
-/

namespace Charter.Games.Omerta

open HexGrid

/-! ## The map: a round city of 18 blocks around the piazza -/

/-- The piazza first, because the laws' monuments stand on the first tile. Then the inner ring and the
outer ring. -/
def hexes : List Hex :=
  [ ⟨0, 0⟩
  , ⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, -1⟩
  , ⟨2, 0⟩, ⟨1, 1⟩, ⟨0, 2⟩, ⟨-1, 2⟩, ⟨-2, 2⟩, ⟨-2, 1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩, ⟨0, -2⟩, ⟨1, -2⟩, ⟨2, -2⟩, ⟨2, -1⟩ ]

def tileResources : List Res :=
  [ "wine", "cement", "fish", "wine", "cement", "fish"
  , "fish", "wine", "cement", "fish", "wine", "cement", "fish", "wine", "cement", "fish", "wine", "cement" ]

def tileNumbers : List Nat :=
  [ 6, 9, 4, 8, 10, 5
  , 3, 11, 8, 4, 12, 9, 10, 3, 11, 6, 5, 2 ]

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
def rackets (p : Party) : Expr := .count p "racket"

/-- The reward: all the cash in the treasury. -/
def reward : Expr := held .treasury "cash"

/-- This seat talks now: it has declared dirt this round and still holds some. Once it has talked, its
dirt is gone, so it cannot be paid twice. -/
def talksNow : Cond := .and (.lt (.lit 0) (said .each "dirt")) (.lt (.lit 0) (held .each "dirt"))

/-- How many seats talk now. -/
def talkers : Expr := .totalOver talksNow (.lit 1)

def runsRacket : Cond := .lt (.lit 0) (rackets .each)

/-- Close one racket of this seat: its newest. -/
def closeOne : Effect := .movePiece .each .bank "racket"

/-- What happens when someone talks. Whoever talks takes their share of `pot`, hands over their dirt and
loses every racket. Everyone else loses their newest racket. A seat can hold at most 4 rackets. -/
def theRaid (pot : Expr) : List Effect :=
  [ .forEach talksNow
      [ pay .treasury .each "cash" (.divBy pot talkers)
      , pay .each .treasury "dirt" (held .each "dirt")
      , closeOne, closeOne, closeOne, closeOne ]
  , .when (.lt (.lit 0) talkers)
      [ .forEach (.and (.not talksNow) runsRacket) [closeOne] ] ]

/-! ## The founding laws -/

/-- How many rackets run in the whole city. -/
def allRackets : Expr := .totalOver .yes (rackets .each)

/-- **The take.** At each round's end each racket pays its owner 2 cash, and each seat that runs a racket
and holds no dirt gets 1 dirt. A seat that talks at that moment gets neither. Cash is worth a point. -/
def lawTake : Law :=
  { title := "Each racket pays 2 cash a round, and a seat that runs one gets dirt"
    clauses :=
      [ .onRoundEnd
          [ .forEach (.and runsRacket (.not talksNow)) [pay .bank .each "cash" (.mul (rackets .each) (.lit 2))]
          , .forEach (.and (.and runsRacket (.not talksNow)) (.eq (held .each "dirt") (.lit 0))) [pay .treasury .each "dirt" (.lit 1)] ]
      , .setWorth "cash" 1 ] }

/-- **The heat.** On every roll the reward grows by 1 cash for every 4 rackets running in the city. Dirt is
kept in the treasury, and every roll sweeps the bank's dirt there, so nobody can buy it from the bank.
There are only 6 dirt in the game, so the treasury's heap is nearly all reward. A seat holds at most 1,
so with 4 seats the treasury always has enough to hand out. -/
def lawHeat : Law :=
  { title := "The more rackets run, the faster the reward grows"
    clauses := [.onRoll [pay .bank .treasury "cash" (.div allRackets 4), pay .bank .treasury "dirt" (held .bank "dirt")]] }

/-- **Talking.** It acts on every roll, which comes right after a seat's turn, and pays the whole reward.
It acts again at the round's end, which comes right after the last seat's turn, and pays half. -/
def lawTalk : Law :=
  { title := "Whoever talks first takes the reward, and the police close the rackets"
    clauses := [.onRoll (theRaid reward), .onRoundEnd (theRaid (.div reward 2))] }

def foundingLaws : List Law := [lawTake, lawHeat, lawTalk]

/-! ## The game -/

def game : GameDef where
  name := "Omertà"
  resources :=
    [ ⟨"wine", 30⟩, ⟨"cement", 30⟩, ⟨"fish", 30⟩, ⟨"cash", 400⟩, ⟨"dirt", 6⟩ ]
  pieces :=
    [ { name := "street", cost := [("cement", 1), ("fish", 1)], points := 0
        placement := .link, yield := 0, limit := 12 }
    , { name := "front", cost := [("wine", 1), ("cement", 1), ("fish", 1)], points := 1
        placement := .spot, yield := 1, limit := 5 }
    , { name := "club", cost := [("cement", 2), ("cash", 2), ("dirt", 1)], points := 2
        placement := .upgrade "front", yield := 2, limit := 3 }
    , { name := "racket", cost := [("wine", 2), ("fish", 1)], points := 1
        placement := .attach "front", yield := 0, limit := 4 } ]
  map :=
    { spotCount := spots.length
      links := links
      regions := regionsOf tiles }
  diceCount := 2
  diceSides := 6
  targetPoints := 40
  rounds := 8
  bankRate := 4
  setupPieces := ["front", "street", "racket"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

end Charter.Games.Omerta
