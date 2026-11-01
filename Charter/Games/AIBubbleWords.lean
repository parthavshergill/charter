import Charter.Games.AIBubble

/-!
# The AI Bubble's founding laws, in the pack's own words

The screen shows these above each founding law, labelled as the pack's words. They are a person's words,
and no proof or test says that they are right. The law's source below them is what counts. This file has
no effect on `game` or on `game_valid`.

The second item of each entry is the start of that law's fingerprint. If a law changes, its old words stop
showing, and `ServerTests.lean` fails until the entry is fixed. So read the new law, edit its words, and
paste in the fingerprint the failing test prints. A law's title is not part of its fingerprint.
-/

namespace Charter.Games.AIBubble

/-- Each founding law, the start of its fingerprint, and what the pack says it does. -/
def foundingWords : List (Law × String × String) :=
  [ (lawCrash, "6724467d",
      "Each hype you hold is worth 1 point. On any roll, if the dice plus a third of the bubble come to 20 or more, the market crashes: all hype goes to the bank, and the bubble empties.")
  , (lawRaise, "be9b8d79",
      "To raise money, declare a number in capital. At the round's end, that much of your hype becomes twice as much capital, and it goes onto the bubble. A datacenter pays its builder 2 hype and adds 1 to the bubble, and a campus adds 2. Each round every lab gets 1 hype, plus 1 for each 10 on the bubble.")
  , (lawMarket, "3babd706",
      "What the dice pay a datacenter, it also makes in inference. At the round's end all inference is sold, and customers pay 16 capital in all, split by share. So every lab that builds lowers everyone's price.")
  , (lawPower, "70dce3b4",
      "From round 2, each round costs 1 power per datacenter and 2 per campus. A lab that cannot pay it all loses its newest datacenter.") ]

end Charter.Games.AIBubble
