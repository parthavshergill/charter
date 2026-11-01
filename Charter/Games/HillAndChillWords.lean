import Charter.Games.HillAndChill

/-!
# Hill and Chill's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.HillAndChill

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawMaybe, "5e20fb43",
      "Anyone who is not down at the round's end gets 1 clout, whether or not dinner happens. Each clout you hold is worth 1 point.")
  , (lawDinner, "8389b921",
      "Everyone holds one down card. To commit to dinner, declare 1 down on your turn. Being down costs the ride and your share of the bill, 1 gas and 1 cash, whether or not dinner happens. If more than half the table is down, but not everyone, dinner happens, and the diners share the memories: 3 lore for each seat that was needed. At a table of four, that is exactly three diners, 3 lore each. If too few are down, the restaurant keeps the cash as a no-show fee. If everyone is down, nobody can agree on a place, and that falls through too. Each lore you hold is worth 1 point.")
  , (lawPotluck, "b69ed2fe",
      "Whoever hosts a potluck feeds the whole house: every seat gets 1 lore.") ]

end Charter.Games.HillAndChill
