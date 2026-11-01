import Charter.Games.StrikeTheEarth

/-!
# Strike the Earth's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.StrikeTheEarth

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawRenown, "bc34fc9b",
      "Each renown is worth 1 point. A hall pays its builder 1 renown, a workshop 2, and a shaft 1. A shaft also adds 2 danger, and every round's end adds 1.")
  , (lawCaveIn, "195bea39",
      "On a 7, if danger is 3 or more, each clan with a shaft loses its newest shaft and gets 2 renown. If danger is 9 or more, each clan with a workshop also loses its newest workshop and gets 3 renown.")
  , (lawFlood, "99b9d24c",
      "On a 2 or 3, each clan with no gate loses its newest tunnel, pays the bank fungus equal to half the danger, and gets 1 renown.")
  , (lawThing, "5ad9818a",
      "On an 11 or 12, if danger is 6 or more, each clan with the most shafts loses its newest workshop and its newest shaft, and gets 4 renown.") ]

end Charter.Games.StrikeTheEarth
