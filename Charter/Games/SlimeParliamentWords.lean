import Charter.Games.SlimeParliament

/-!
# Slime Parliament's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.SlimeParliament

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawPuffball, "053de151",
      "When a player builds a puffball, it bursts: every player gets 1 pollen from the bank.")
  , (lawSwelling, "d7d1da8c",
      "When a player builds a swelling, that player gives 1 oatmeal to each player with fewer points.")
  , (lawDew, "45763737",
      "At the end of each round, each player with more than 5 dew pays half of it, rounded down, to the treasury.")
  , (lawRot, "c3a55922",
      "Each time a player is paid rot at a harvest, that player also gets 1 pollen from the bank.") ]

end Charter.Games.SlimeParliament
