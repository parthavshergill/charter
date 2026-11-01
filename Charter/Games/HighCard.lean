import Charter.Words
import Charter.Games.HexMap
import Charter.Scene.Render

/-!
# High Card

A small game that shows hidden information. Each turn's roll is a card that only its owner sees. Seats
bet chips on their cards, in secret. At the round's end, the highest card among the seats that bet wins
back up to twice its bet. Chips are points.

The engine holds every card. What keeps a card secret is the server's `GameSpec.secrecy` for this game,
in `Server/Spec.lean`: cards are hidden goods, declarations are sealed, and the roll is hidden. Nothing in
this file is secret, and nothing here differs from any other game.

The map is only a table to sit at. No hex has a number, so the dice pay nobody, and a roll shows no one
where it landed.
-/

namespace Charter.Games.HighCard

open HexGrid

/-! ## The table -/

def hexes : List Hex := hexagon 1

/-- Colours for the hexes. These are not resources of this game. -/
def tileLooks : List Res := ["grain", "timber", "ore", "wool", "brick", "grain"]

def tiles : List TileDef :=
  match hexes with
  | [] => []
  | center :: rest =>
    { hex := center, res := none, number := none } ::
      (rest.zip tileLooks).map fun x => { hex := x.1, res := some x.2, number := none }

def spots : List Vertex := spotsOf tiles
def edges : List Edge := sidesOf tiles
def links : List (Nat × Nat) := linksOf tiles

/-! ## Small words for the laws -/

def held (p : Party) (r : Res) : Expr := .holding p (.lit r)
def pay (a b : Party) (r : Res) (n : Expr) : Effect := .transfer a b (.lit r) n

/-- What a seat really bets: what it declared in chips, up to what it holds. -/
def bet (p : Party) : Expr := .min (.declared p (.lit "chips")) (held p "chips")
/-- This seat bet something. -/
def bets : Cond := .lt (.lit 0) (bet .each)
/-- The highest card among the seats that bet. -/
def best : Expr := .mostOver bets (held .each "card")
/-- Every chip bet this round. -/
def pot : Expr := .totalOver .yes (bet .each)

/-! ## The founding laws -/

/-- **The deal.** Each roll gives the seat whose turn it starts a card as high as the dice, and 2 chips. -/
def lawDeal : Law :=
  { title := "Each roll deals a card"
    clauses := [.onRoll [pay .bank .actor "card" .rolled, pay .bank .actor "chips" (.lit 2)]] }

/-- **Chips are points.** -/
def lawChips : Law :=
  { title := "Chips are points"
    clauses := [.setWorth "chips" 1] }

/-- **The showdown.** At the round's end every seat pays what it bet into the pot. The highest card among
the seats that bet wins the pot, up to twice its own bet, from the bank. Then every card goes back. -/
def lawShowdown : Law :=
  { title := "The highest card takes the pot"
    clauses :=
      [ .onRoundEnd
          [ .forEach bets [pay .each .treasury "chips" (bet .each)]
          , .forEach (.and bets (.eq (held .each "card") best))
              [pay .bank .each "chips" (.min pot (.mul (.lit 2) (bet .each)))]
          , .forEach .yes [pay .each .bank "card" (held .each "card")] ] ] }

def foundingLaws : List Law := [lawDeal, lawChips, lawShowdown]

/-- High Card: the most chips after 6 rounds. -/
def game : GameDef where
  name := "High Card"
  resources := [⟨"chips", 400⟩, ⟨"card", 200⟩]
  pieces :=
    [ { name := "settlement", cost := [("chips", 30)], points := 0
        placement := .spot, yield := 0, limit := 1 } ]
  map := { spotCount := spots.length, links := links, regions := [] }
  diceCount := 2
  diceSides := 6
  targetPoints := 200
  rounds := 6
  bankRate := 4
  setupPieces := ["settlement"]
  foundingLaws := foundingLaws

theorem game_valid : game.Valid := by decide +kernel

/-! ## The look

The Island's look, with its own words on the scroll. -/

def theme : Scene.Theme :=
  { Scene.islandTheme with
    look := { Scene.islandTheme.look with
      tagline := "Every rule is public. Your card is not, and that is a theorem."
      marks := Scene.islandMarks ++ [("chips", "crystal"), ("card", "laurel")] } }

end Charter.Games.HighCard
