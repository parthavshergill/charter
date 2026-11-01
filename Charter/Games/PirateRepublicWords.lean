import Charter.Games.PirateRepublic

/-!
# The Pirate Republic's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.PirateRepublic

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawVote, "dd6e8870",
      "At each round's end, the seat that alone declared the most ballots it really holds takes the hat. A tie leaves the hat where it is. Then every seat is brought back to exactly 1 ballot, whatever it traded.")
  , (lawShare, "ab1b030b",
      "Each plunder a seat holds is worth 1 point. Whenever the dice pay anyone plunder, whoever holds the hat gets the same amount from the bank.")
  , (lawLevy, "f544c3e4",
      "Whoever holds the hat can declare rum, up to 3. At the round's end each other seat pays that much rum, as far as it can, and the captain gets it all.")
  , (lawNavy, "523cebbe",
      "At the end of round 5 the Navy comes. Declare pardon: you lose half your plunder and get a pardon worth 3 points, and plunder no longer pays you. Or declare and hold 3 powder: you pay it and drive them off. Anyone else loses their newest wharf.") ]

end Charter.Games.PirateRepublic
