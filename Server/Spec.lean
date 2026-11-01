import Charter.Games.Island
import Charter.Games.NotCatan
import Charter.Games.NotCatanWords
import Charter.Games.SlimeParliamentWords
import Charter.Games.AIBubbleWords
import Charter.Games.StrikeTheEarthWords
import Charter.Games.PirateRepublicWords
import Charter.Games.Omerta.Look
import Charter.Scene.OfState
import Charter.Scene.LookCheck
import Server.GameFacts

/-!
# The games this server can run

A game's definition is chosen when a table is created, and its id goes in the table's first log entry,
so a replay runs the same definition. Each entry has a proof of `G.Valid`, which every theorem in
`Charter/Constitution.lean` assumes and which the engine does not check. So a server that takes its
definitions from this list cannot run an invalid one. The layout says how the board is drawn. It has
no effect on the rules.

A data file format for games is later work. For now a new game is a Lean definition added here.

## Adding an extension pack

A pack is one new file and one entry here, and nothing else changes:

1. Write `Charter/Games/MyPack.lean`, with the map, a `GameDef`, its founding laws if it has any, and
   `theorem my_valid : my.Valid := by decide +kernel`. If `decide` says no, `#eval` the `lawProblems` of
   each law to learn why. `Charter/Games/NotCatan.lean` is the example with the most in it.
2. Import it here, write a `GameSpec` below, and add that to `gameSpecs`. The lobby, the seats, the log,
   replay and the scene all read from that list. Import the file in `Charter.lean` too, so that
   `make audit` builds it.
3. If the pack has founding laws, write what they do in plain words, as in
   `Charter/Games/NotCatanWords.lean`, and put them in `foundingWords`.

A pack's name and sentence are what a player reads when choosing it, so keep the sentence short and
plain. `Server/PreviewCheck.lean` plays every pack with bots, and `ServerTests.lean` checks its layout.
The build check at the end of this file names anything a pack lacks a look for. A pack's look is its
`Theme`, in Lean. `docs/process/reskins.md` says how to make a new one.
-/

namespace CharterServer
open Charter

/-- A game a table can play: its definition, the proof that it is valid, how to draw it, and what a
player reads when choosing it. -/
structure GameSpec where
  id : String
  /-- The name in the lobby. -/
  name : String
  /-- One short plain sentence: what is different about this game. -/
  blurb : String
  G : GameDef
  valid : G.Valid
  layout : Scene.Layout
  /-- The fewest and the most seats this game supports. `G.Valid` holds from 2 to 6 seats whatever
  these say. They are about how the game plays. -/
  minSeats : Nat := Charter.minSeats
  maxSeats : Nat := Charter.maxSeats
  /-- This game can use the sample laws in `Rules.sampleLaws`, which name the Island's goods and pieces. -/
  samples : Bool := false
  /-- What a Claude seat or the clerk needs to know about this game and the screen does not say. -/
  guide : String := ""
  /-- What the pack says its founding laws do: the law, the start of its fingerprint, and the words. See
  `Describe.packWords`. Laws of a pack with none of these show their source with a short note. -/
  foundingWords : List (Law × String × String) := []
  /-- The folder, under the server's root, that holds this pack's mesh files. -/
  meshFolder : String := ""

def islandSpec : GameSpec :=
  { id := "island"
    name := "Tutorial Island"
    blurb := "The base game: settle an island, then change its rules."
    G := Games.Island.island
    valid := Games.Island.island_valid
    layout :=
      { tiles := Games.Island.tiles, spots := Games.Island.spots, edges := Games.Island.edges
        links := Games.Island.links, theme := Scene.islandTheme, word := "the island" }
    samples := true }

def notCatanSpec : GameSpec :=
  { id := "not-catan"
    name := "Not Catan"
    blurb := "A race to 10 on 19 hexes, where a 7 costs big hands half."
    G := Games.NotCatan.game
    valid := Games.NotCatan.game_valid
    layout :=
      { tiles := Games.NotCatan.tiles, spots := Games.NotCatan.spots, edges := Games.NotCatan.edges
        links := Games.NotCatan.links, theme := Games.NotCatan.theme, word := "the map" }
    minSeats := 3
    maxSeats := 4
    samples := true
    guide := "Laurel is not harvested. It pays for a wreath, and there are laurels for only two wreaths in the game."
    foundingWords := Games.NotCatan.foundingWords }

def slimeSpec : GameSpec :=
  { id := "slime-parliament"
    name := "Slime Parliament"
    blurb := "Rival slime moulds spread along a damp log and pass laws about oatmeal. The biggest wear wigs."
    G := Games.SlimeParliament.game
    valid := Games.SlimeParliament.game_valid
    layout :=
      { tiles := Games.SlimeParliament.tiles, spots := Games.SlimeParliament.spots, edges := Games.SlimeParliament.edges
        links := Games.SlimeParliament.links, theme := Games.SlimeParliament.theme, word := "the log" }
    minSeats := 2
    maxSeats := 4
    meshFolder := "packs/slime-parliament/meshes"
    foundingWords := Games.SlimeParliament.foundingWords
    guide := "You are a slime mould on a damp log. Oatmeal, dew, rot and pollen are the goods. A tendril costs oatmeal and dew. A node costs oatmeal, dew and rot. A swelling replaces a node. A puffball attaches to a node, costs pollen and oatmeal, and gives every seat pollen. The founding laws say more." }

def bubbleSpec : GameSpec :=
  { id := "ai-bubble"
    name := "The AI Bubble"
    blurb := "Rival labs raise money on promises and build datacenters. Hype is worth points until the crash."
    G := Games.AIBubble.game
    valid := Games.AIBubble.game_valid
    layout :=
      { tiles := Games.AIBubble.tiles, spots := Games.AIBubble.spots, edges := Games.AIBubble.edges
        links := Games.AIBubble.links, theme := Games.AIBubble.theme, word := "the grid" }
    minSeats := 3
    maxSeats := 4
    meshFolder := "packs/ai-bubble/meshes"
    foundingWords := Games.AIBubble.foundingWords
    guide := "You run a rival AI lab on a dark desert grid. Silicon, power and concrete come from the map. Capital comes from selling inference and from raising money. The founding laws bind, and they say all of this: Hype in your hand is worth 1 point each. When the dice pay your pieces, you also get that much inference. At each round's end, all inference held is sold, and customers pay 16 capital in all, split by each lab's share of what was sold. More supply means a lower price for everyone. At each round's end from round 2, you pay 1 power per datacenter and 2 per campus. If you hold less than that, you pay what you have and your newest datacenter is destroyed. To raise money, use declare on your turn with res capital and n the amount of hype to sell. At the round's end, that hype, up to what you hold, goes to the bank, you get twice as much capital, and it goes onto the bubble. The declaration clears each round. Building a datacenter pays you 2 hype and adds 1 to the bubble. A campus adds 2. The bubble is what the treasury holds of it. At each round's end every lab also gets 1 hype, plus 1 more for each 10 on the bubble. The crash: on any roll, if the dice plus a third of the bubble, rounded down, come to 20 or more, all hype in every hand goes to the bank and the bubble empties. Pieces and capital survive. A bubble of 24 can pop on a 12, 27 on an 11 or more, 39 on a 7 or more, 54 on anything. The first lab to 25 points, hype included, wins at once, even with the bubble still up. Otherwise the most points after round 10 wins. Regulation: 3 of 4 seats can call the crash early, or change anything else, by law. For example (law \"Emergency audit\" (now (for-each-player true (transfer each bank hype (holding each hype))) (transfer treasury bank bubble (holding treasury bubble)))) wipes all hype at once. Adding (end-game) to it ends the game on the spot, and a law can also repeal any founding law. So each vote on a regulation is a vote on who gets out in time. Deals can carry circular investment between labs: payments each round, or payments when a seat builds, in any resource." }
def pirateSpec : GameSpec :=
  { id := "pirate-republic"
    name := "The Pirate Republic"
    blurb := "Nassau, 1715. Elect a captain, make promises, and depose the captain when they break them."
    G := Games.PirateRepublic.game
    valid := Games.PirateRepublic.game_valid
    layout :=
      { tiles := Games.PirateRepublic.tiles, spots := Games.PirateRepublic.spots, edges := Games.PirateRepublic.edges
        links := Games.PirateRepublic.links, theme := Games.PirateRepublic.theme, word := "the Bahamas" }
    minSeats := 3
    maxSeats := 4
    meshFolder := "packs/pirate-republic/meshes"
    foundingWords := Games.PirateRepublic.foundingWords
    guide := "You are a pirate of Nassau. Rum, powder and timber are goods, and each plunder is worth 1 point. From round 2 each seat starts each round with 1 ballot, and ballots can be traded. To stand for captain, declare a number of ballot on your turn. The seat that alone declared the most ballots it really holds at the round's end takes the hat, and a tie leaves the hat where it is. A ballot can be bought from another seat with an offer on your turn, so one bought ballot beats a lone declaration. The hat gets a copy of all plunder the dice pay anyone. Whoever holds the hat can declare rum, up to 3, and each other seat pays that much to the captain at the round's end. In round 5 declare pardon, or declare and hold 3 powder, or lose your newest wharf at the round's end. A fort is not a wharf." }

def strikeSpec : GameSpec :=
  { id := "strike-the-earth"
    name := "Strike the Earth"
    blurb := "Rival dwarf clans dig under one doomed mountain. Disaster pays in renown, and a majority can let the fort fall."
    G := Games.StrikeTheEarth.game
    valid := Games.StrikeTheEarth.game_valid
    layout :=
      { tiles := Games.StrikeTheEarth.tiles, spots := Games.StrikeTheEarth.spots, edges := Games.StrikeTheEarth.edges
        links := Games.StrikeTheEarth.links, theme := Games.StrikeTheEarth.theme, word := "the mountain" }
    minSeats := 2
    maxSeats := 4
    meshFolder := "packs/strike-the-earth/meshes"
    foundingWords := Games.StrikeTheEarth.foundingWords
    guide := "You lead a dwarf clan under a doomed mountain. Stone, ore, fungus and ember are the goods. In setup you place a hall and a tunnel for free, twice, so place both each time: ending a setup turn early gives up the rest, and a new hall must touch your own tunnel. A farm, gate, shaft or epitaph stands on a hall, and not on a workshop. Renown is the score: each is worth 1 point while you hold it, and most pieces are worth 0 points. So a hall or workshop that falls costs you no points, and a law may even pay you for it. An epitaph is the only piece with points. It costs 2 renown and 1 danger, and no hex pays danger, so you buy it from the bank. The bank also sells renown at its rate. Danger is the danger in the treasury. It is shared, it only rises unless a law lowers it, and the founding laws read it. A law cannot name who proposed it or who voted for it, but a law can pay whoever passes a test, so a reckless law can carry its own reward. Any seat can propose a law that ends the game: (law \"The fort falls\" (end-game)). If a majority passes it, the game ends at once and the most points wins." }

def omertaSpec : GameSpec :=
  { id := "omerta"
    name := "Omertà"
    blurb := "A crime family runs rackets and swears to keep quiet. The first to talk takes the reward."
    G := Games.Omerta.game
    valid := Games.Omerta.game_valid
    layout :=
      { tiles := Games.Omerta.tiles, spots := Games.Omerta.spots, edges := Games.Omerta.edges
        links := Games.Omerta.links, theme := Games.Omerta.theme, word := "the city" }
    minSeats := 3
    maxSeats := 4
    guide := "You are in a crime family that shares one city. Wine, cement and fish come from the map. Cash is worth 1 point each, and it pays for a club. A front stands on a corner. A racket goes in the back room of one of your fronts, one per front. A club replaces a front, and costs cement, cash and 1 dirt. At each round's end each racket pays its owner 2 cash. The reward is the cash in the treasury. On every roll it grows by 1 for every 3 rackets running in the city. Building a racket gives you 1 dirt, and that is the only way to get dirt: the bank never sells it. To talk, declare dirt on your turn, any number from 1, while you hold some dirt. At the next roll, or at the round's end if you are the last seat of the round, you take the whole reward, you give up all your dirt, and all your rackets close. Every other seat that runs a racket loses its newest one, and nobody is paid for rackets at a round's end where someone talks. A declaration cannot be taken back after your turn, so later seats in the round see it. Talking is legal at any time, and promises not to talk bind nobody: swear, bargain, pay for silence with a deal, or threaten. A law cannot name a seat, but the table can pass laws about the situation, such as who holds no dirt." }

instance : Inhabited GameSpec := ⟨islandSpec⟩

/-- Every game this server can run. The first is the default. -/
def gameSpecs : List GameSpec := [islandSpec, notCatanSpec, slimeSpec, bubbleSpec, strikeSpec, pirateSpec, omertaSpec]

/-- The game with this id. A log entry with no id is from before there was a choice: it is the Island. -/
def specOf? (id : Option String) : Option GameSpec :=
  match id with
  | none => some islandSpec
  | some i => gameSpecs.find? (·.id == i)

/-- The hash of each mesh file this pack's look names. -/
def GameSpec.meshHashes (d : GameSpec) : List String :=
  d.layout.theme.meshDefs.filterMap fun
    | .defineMeshFile _ sha _ _ _ => some sha
    | _ => none

/-- The folder that holds the mesh file with this hash, if a pack names it. -/
def meshFolderOf (hash : String) : Option String :=
  (gameSpecs.find? (·.meshHashes.contains hash)).map (·.meshFolder)

/-- Every mesh file, under the server's root. -/
def meshFiles : List String :=
  gameSpecs.flatMap fun d => d.meshHashes.map fun h => s!"{d.meshFolder}/{h}.mesh"

/-! ## Does every pack have a look?

A new pack's problems print here, and the build stops. Add what they name. The line below is an old
gap, kept so the older pack looks as it did: Not Catan's relic is gold whoever owns it. -/

/--
info: [("not-catan", ["piece relic does not show the owner's colour for seats [0, 1, 2, 3, 4, 5]"])]
-/
#guard_msgs in
#eval (gameSpecs.map fun d => (d.id, Scene.lookProblems d.G d.layout)).filter (!·.2.isEmpty)

/-! `Scene.lookProblems` checks that a pack names a track on the list. This checks that each one on the list
has its file. -/

/-- info: [] -/
#guard_msgs in
#eval Scene.musicTracks.filterM fun t => do
  return !(← (System.FilePath.mk s!"web/audio/music/{t}.mp3").pathExists)

end CharterServer
