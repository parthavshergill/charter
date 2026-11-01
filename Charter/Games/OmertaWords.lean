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
  [ (lawTake, "b4fd8bd1",
      "The family pays its own. At each round's end every racket pays the one who runs it 2 cash, and each cash is a point. Run a racket through a round's end and you also get 1 dirt, if you hold none: you have seen things. Nobody holds more than 1. A rat who talks at that moment gets nothing.")
  , (lawHeat, "4493470a",
      "The district attorney is watching. On every roll the reward on the desk grows by 1 cash for every 4 rackets running in the city. There are only 6 dirt in town, kept on the DA's desk, and the bank never sells it.")
  , (lawTalk, "3c5c7378",
      "Declare dirt on your turn and you have talked. At the next roll you take the whole reward. Talk last in a round and the DA pays at the round's end, and only half. You hand over all your dirt, the police close every racket you run, and every other seat that runs one loses its newest.") ]

end Charter.Games.Omerta
