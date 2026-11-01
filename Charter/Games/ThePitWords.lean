import Charter.Games.ThePit

/-!
# The Pit's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.ThePit

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawSpot, "f858a384",
      "At each round's end, customers buy all the wheat in every hand. They pay 4 gold plus 2 for each round so far, split by how much wheat each seat sells. More wheat means a lower price for everyone. Wheat in a deal's deposit is not sold, so it waits for a later round.")
  , (lawBumper, "2d3900ed",
      "Whenever the dice pay anyone wheat, the bank pays them as much again.")
  , (lawAuction, "301f1e94",
      "Each membership in your hand is worth 3 points. One is for sale each round. To bid, declare a number of gold on your turn. At the round's end the highest bid wins and pays 1 more than the next-highest bid. A bid counts only up to the gold in your own hand before this round's wheat is sold, so gold in a deal's deposit cannot bid. A tie sells nothing, and the membership is added to the next round's sale. In round 10, all that are left are sold.") ]

end Charter.Games.ThePit
