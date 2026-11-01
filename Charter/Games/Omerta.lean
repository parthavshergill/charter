import Charter.Words
import Charter.Games.HexMap

/-!
# Omertà

A crime family shares one city. Fronts are shops on the street corners, and a racket runs in the back
room of a front. Rackets pay the family every round, and the more rackets run, the faster the district
attorney's reward for a witness grows. The reward sits in the treasury, where everyone can watch it grow.

Anyone who has seen a racket built holds dirt. On your turn you can talk: declare your dirt. At the next
roll of the dice, or at the round's end if you were last, you take the whole reward. Then the police
close every racket of yours, and every other seat that runs a racket loses its newest one.

The engine has no hidden information and no secret moves, so the oath is spoken across the table. The
board only keeps score of who kept it.

## Turn order

A seat declares only on its own turn, and the order of seats never changes. So a law that pays at the
round's end lets the last seat see everyone's choice and talk with no risk. Here the reward goes to the
first seat that talks, at the next roll, before anyone else can answer. The reward also grows on every
roll, not only at the round's end. So the first seat of a round gets the first chance, and a later seat
gets a larger reward, and neither is safe.
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
  , 3, 11, 8, 4, 12, 9, 10, 3, 6, 11, 5, 2 ]

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

/-- What happens when someone talks. Whoever talks shares the reward, hands over their dirt and loses
every racket. Everyone else loses their newest racket. A seat can hold at most 4 rackets. -/
def theRaid : List Effect :=
  [ .forEach talksNow
      [ pay .treasury .each "cash" (.divBy reward talkers)
      , pay .each .treasury "dirt" (held .each "dirt")
      , closeOne, closeOne, closeOne, closeOne ]
  , .when (.lt (.lit 0) talkers)
      [ .forEach (.and (.not talksNow) runsRacket) [closeOne] ] ]

/-! ## The founding laws -/

/-- How many rackets run in the whole city. -/
def allRackets : Expr := .totalOver .yes (rackets .each)

/-- **The take.** Each racket pays its owner 2 cash at the round's end, unless someone talks at that
moment. Cash is worth a point. -/
def lawTake : Law :=
  { title := "Each racket pays 2 cash a round, and cash is worth a point"
    clauses :=
      [ .onRoundEnd [.when (.eq talkers (.lit 0)) [.forEach runsRacket [pay .bank .each "cash" (.mul (rackets .each) (.lit 2))]]]
      , .setWorth "cash" 1 ] }

/-- **The heat.** On every roll the reward grows by 1 cash for every 3 rackets running in the city. A new
racket gives its builder 1 dirt. Dirt is kept in the treasury, and every roll sweeps the bank's dirt
there, so nobody can buy it from the bank. -/
def lawHeat : Law :=
  { title := "The more rackets run, the faster the reward grows"
    clauses :=
      [ .onRoll [pay .bank .treasury "cash" (.div allRackets 3), pay .bank .treasury "dirt" (held .bank "dirt")]
      , .onBuild "racket" [pay .treasury .actor "dirt" (.lit 1)] ] }

/-- **Talking.** It acts on every roll, which comes right after a seat's turn, and at the round's end,
which comes right after the last seat's turn. -/
def lawTalk : Law :=
  { title := "Whoever talks first takes the reward, and the police close the rackets"
    clauses := [.onRoll theRaid, .onRoundEnd theRaid] }

def foundingLaws : List Law := [lawTake, lawHeat, lawTalk]

/-! ## The game -/

def game : GameDef where
  name := "Omertà"
  resources :=
    [ ⟨"wine", 30⟩, ⟨"cement", 30⟩, ⟨"fish", 30⟩, ⟨"cash", 400⟩, ⟨"dirt", 40⟩ ]
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
  targetPoints := 30
  rounds := 8
  bankRate := 4
  setupPieces := ["front", "street"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

end Charter.Games.Omerta
