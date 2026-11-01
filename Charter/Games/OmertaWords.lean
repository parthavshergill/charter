import Charter.Games.Omerta

/-!
# Omertà's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.Omerta

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawTake, "1a97eb87",
      "The family pays its own. At each round's end every racket pays the one who runs it 2 cash, and each cash is a point. But if somebody talks at that moment, nobody gets paid.")
  , (lawHeat, "81f44819",
      "The district attorney is watching. On every roll the reward on the desk grows by 1 cash for every 3 rackets running in the city. Open a racket and you get 1 dirt. That is the only way to get dirt: the bank never sells it.")
  , (lawTalk, "c5b72fb9",
      "Declare dirt on your turn and you have talked. At the next roll, or at the round's end if you were last, you take the whole reward and hand over all your dirt. The police close every racket you run, and every other seat that runs one loses its newest.") ]

end Charter.Games.Omerta
