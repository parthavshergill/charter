import Charter.Words

/-!
# Two tiny example games

These are real, checked values, so `GameDef.Valid` is known to accept games. The full-game witnesses
in `Charter/Constitution/Examples.lean` play them to the end.
-/

namespace Charter

/-- A very small settlers-style game: three regions around a ring of ten spots. Two seats can
always place both setup pieces in both setup passes, wherever earlier seats went. -/
def tinySettlers : GameDef where
  name := "Tiny Settlers"
  resources := [⟨"grain", 24⟩, ⟨"timber", 24⟩, ⟨"brick", 24⟩]
  pieces :=
    [ { name := "road", cost := [("timber", 1), ("brick", 1)], points := 0
        placement := .link, yield := 0, limit := 12 }
    , { name := "settlement", cost := [("timber", 1), ("brick", 1), ("grain", 1)], points := 1
        placement := .spot, yield := 1, limit := 3 }
    , { name := "city", cost := [("grain", 3)], points := 2
        placement := .upgrade "settlement", yield := 2, limit := 2 } ]
  map :=
    { spotCount := 10
      links := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 0)]
      regions :=
        [ ⟨"grain", 1, [0, 1, 2, 6, 7]⟩, ⟨"timber", 2, [2, 3, 4, 7, 8]⟩
        , ⟨"brick", 3, [4, 5, 0, 8, 9]⟩ ] }
  diceCount := 1
  diceSides := 3
  targetPoints := 4
  rounds := 10
  bankRate := 4
  lawFee := [("grain", 1)]
  setupPieces := ["settlement", "road"]

/-- The same engine with a different structure: two resources, a new upgrade path, and two
separate rings of spots. Three seats can always place both setup pieces in both setup passes,
wherever earlier seats went. -/
def tinySpace : GameDef where
  name := "Tiny Space"
  resources := [⟨"helium", 30⟩, ⟨"alloy", 30⟩]
  pieces :=
    [ { name := "lane", cost := [("alloy", 1)], points := 0
        placement := .link, yield := 0, limit := 10 }
    , { name := "outpost", cost := [("helium", 1), ("alloy", 2)], points := 1
        placement := .spot, yield := 1, limit := 4 }
    , { name := "station", cost := [("helium", 4)], points := 3
        placement := .upgrade "outpost", yield := 3, limit := 1 } ]
  map :=
    { spotCount := 14
      links :=
        [ (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 0)
        , (10, 11), (11, 12), (12, 13), (13, 10) ]
      regions :=
        [ ⟨"helium", 2, [0, 1, 4, 5, 8, 10, 11]⟩, ⟨"alloy", 4, [2, 3, 6, 7, 9, 12, 13]⟩ ] }
  diceCount := 2
  diceSides := 2
  targetPoints := 5
  rounds := 12
  bankRate := 3
  lawFee := [("alloy", 1)]
  setupPieces := ["outpost", "lane"]

theorem tinySettlers_valid : tinySettlers.Valid := by decide
theorem tinySpace_valid : tinySpace.Valid := by decide

/-- A game with no resources is rejected. -/
theorem noResources_invalid : ¬ ({ tinySettlers with resources := [] } : GameDef).Valid := by
  decide

/-- A map whose link leaves the map is rejected. -/
theorem badLink_invalid :
    ¬ ({ tinySettlers with
          map := { tinySettlers.map with links := [(0, 99)] } } : GameDef).Valid := by
  decide

/-- Tiny Settlers that starts with a founding law: cities cost 2 grain, not 3. -/
def tinyFounded : GameDef :=
  { tinySettlers with
    name := "Tiny Founded"
    foundingLaws := [{ title := "Cheap cities", clauses := [.setCost "city" [("grain", 2)]] }] }

theorem tinyFounded_valid : tinyFounded.Valid := by decide +kernel

/-- A law that pays each seat from each seat, three levels deep. That is 8 payments at 2 seats and 216
at 6, which is over the limit of 64. -/
def tooManyPayments : Law :=
  { title := "Everyone pays everyone"
    clauses := [.onRoundEnd [.forEach .yes [.forEach .yes [.forEach .yes
      [.transfer .each .treasury (.lit "grain") (.lit 1)]]]]] }

/-- A game whose founding law asks for too many payments at 6 seats is rejected, even though the law
is within the limit at 2 seats. -/
theorem tooManyPayments_invalid :
    ¬ ({ tinySettlers with foundingLaws := [tooManyPayments] } : GameDef).Valid := by
  decide +kernel

end Charter
