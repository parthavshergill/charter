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
  [ (lawAlarm, "0bb43069",
      "When a 7 comes up, at the end of that round each player with more than 7 goods pays the bank half of each good, rounded down. The law tracks the 7 with a counter called alarm.")
  , (lawThief, "a1c4b2a7",
      "For the rest of a round with a 7, each player with 5 or more points gives each harvest payment back to the bank.")
  , (lawKnight, "489f3941",
      "When a player builds a knight, each player with more points than the builder gives the builder 1 good: ore if they have it, else grain, else wool. A player with none of these gives nothing.")
  , (lawLaurels, "c71d32ee",
      "A player's third knight or sixth road earns 3 laurel from the bank, and 3 laurel buy a wreath. When a wreath is built, 3 laurel go from the bank to the treasury, so only two wreaths can exist.")
  , (lawEmptyBank, "d8cf99f2",
      "If a harvest leaves the bank with none of a good, each player paid that good on that roll gives the payment back.")
  , (lawFirstHand, "f0be2dd8",
      "At the end of each round, each player with no goods and at most 2 settlements and cities gets 1 timber, 1 brick and 1 grain from the bank.")
  , (lawHarbor, "323909de",
      "Each time a player with a harbor gets a harvest payment, the law swaps for them: 3 of a good for 1 of the next, if they hold at least 4 more of the first. The order is timber, brick, wool, grain, ore.") ]

end Charter.Games.NotCatan
