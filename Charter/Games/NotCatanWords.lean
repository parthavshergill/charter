import Charter.Games.NotCatan

/-!
# Not Catan's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

**To change a law.** The second item of each entry is the start of that law's fingerprint. If a law
changes, its old words stop showing, and `ServerTests.lean` fails until the entry is fixed. So read the new
law, edit its words, and paste in the fingerprint the failing test prints. A law's title is not part of
its fingerprint.
-/

namespace Charter.Games.NotCatan

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawSeven, "a9590482",
      "On a roll of 7, each player with more than 7 goods pays the bank half of each good, rounded down.")
  , (lawKnight, "64cbfe29",
      "When a player builds a knight, each player with more points than the builder and at least 1 ore gives the builder 1 ore.")
  , (lawLaurels, "c71d32ee",
      "A player's third knight or sixth road earns 3 laurel from the bank, and 3 laurel buy a wreath. When a wreath is built, 3 laurel go from the bank to the treasury, so only two wreaths can exist.")
  , (lawEmptyBank, "d8cf99f2",
      "If a harvest leaves the bank with none of a good, each player paid that good on that roll gives the payment back.") ]

end Charter.Games.NotCatan
