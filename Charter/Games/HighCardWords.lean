import Charter.Games.HighCard

/-!
# High Card's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed.
-/

namespace Charter.Games.HighCard

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawDeal, "2ed33706",
      "Each roll gives the seat whose turn it starts a card as high as the dice show, and 2 chips. Only that seat sees the roll and the card.")
  , (lawChips, "e2f4eeee",
      "Each chip a seat holds is worth 1 point. The most points after round 6 wins.")
  , (lawShowdown, "28861139",
      "To bet, declare chips on your turn. Nobody else sees the number until the round ends. At the round's end each seat pays what it bet, up to what it holds, into the pot. The highest card among the seats that bet wins the whole pot, up to twice its own bet, paid by the bank. A tie pays each tied seat. Then every card goes back to the bank.") ]

end Charter.Games.HighCard
