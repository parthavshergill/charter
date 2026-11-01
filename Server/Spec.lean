import Charter.Games.Island
import Charter.Games.Belt
import Charter.Games.NotCatan
import Charter.Games.NotCatanWords
import Charter.Games.SlimeParliamentWords
import Charter.Games.PirateRepublicWords
import Charter.Scene.OfState
import Charter.Scene.Belt
import Charter.Scene.LookCheck

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
    name := "The Island"
    blurb := "The base game: settle an island, then change its rules."
    G := Games.Island.island
    valid := Games.Island.island_valid
    layout :=
      { tiles := Games.Island.tiles, spots := Games.Island.spots, edges := Games.Island.edges
        links := Games.Island.links, theme := Scene.islandTheme, word := "the island" }
    samples := true }

def beltSpec : GameSpec :=
  { id := "belt"
    name := "The Belt"
    blurb := "A shorter game among the asteroids, with four resources and small dice."
    G := Games.Belt.belt
    valid := Games.Belt.belt_valid
    layout :=
      { tiles := Games.Belt.tiles, spots := Games.Belt.spots, edges := Games.Belt.edges
        links := Games.Belt.links, theme := Scene.BeltLook.theme, word := "the belt" } }

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
    guide := "You are a pirate of Nassau. Rum, powder and timber are goods, and each plunder is worth 1 point. From round 2 each seat starts each round with 1 ballot, and ballots can be traded. To stand for captain, declare a number of ballot on your turn. The seat that alone declared the most ballots it really holds at the round's end takes the hat, and a tie leaves the hat where it is. The hat gets a copy of all plunder the dice pay anyone. Whoever holds the hat can declare rum, up to 3, and each other seat pays that much to the captain at the round's end. In round 5 declare pardon, or declare and hold 3 powder, or lose your newest wharf at the round's end. A fort is not a wharf." }

instance : Inhabited GameSpec := ⟨islandSpec⟩

/-- Every game this server can run. The first is the default. -/
def gameSpecs : List GameSpec := [islandSpec, beltSpec, notCatanSpec, slimeSpec, pirateSpec]

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

/-! ## Counters

A game can have a resource that no piece costs. Nobody wants it for itself, so it is a
counter that laws read, such as a flag a law keeps in the treasury. The screen and the Claude seats leave it out of hands,
trades and what a corner pays. It is still in the books and the laws' text, and the rules treat it like
any other resource. -/

/-- This resource is a counter and not a good. -/
abbrev markRes := Scene.markRes

/-- The resources a person trades and holds. -/
def goodsOf (G : GameDef) : List Res := (G.resources.map (·.name)).filter (!markRes G ·)

/-- The regions that pay goods. -/
def paidRegions (G : GameDef) : List Region := G.map.regions.filter (!markRes G ·.res)

/-! ## Does every pack have a look?

A new pack's problems print here, and the build stops. Add what they name. The two lines below are old
gaps, kept so the older packs look as they did: the Belt's dock wears a law-made model with its name
over it, and Not Catan's relic is gold whoever owns it. -/

/--
info: [("belt", ["piece dock has no model"]),
 ("not-catan", ["piece relic does not show the owner's colour for seats [0, 1, 2, 3, 4, 5]"])]
-/
#guard_msgs in
#eval (gameSpecs.map fun d => (d.id, Scene.lookProblems d.G d.layout)).filter (!·.2.isEmpty)

/-! ## What a game's pieces are for

The policies and the chronicle ask these, so they need no piece names. -/

/-- The game's own piece that goes on a spot, such as a settlement. -/
def spotPiece (G : GameDef) : Option PieceDef :=
  G.pieces.find? fun d => match d.placement with
    | .spot => true
    | _ => false

/-- The game's own piece that goes on a link, such as a road. -/
def linkPiece (G : GameDef) : Option PieceDef :=
  G.pieces.find? fun d => match d.placement with
    | .link => true
    | _ => false

/-- The game's own piece that replaces another, such as a city, and the piece it replaces. -/
def upgradePiece (G : GameDef) : Option (PieceDef × PieceKind) :=
  G.pieces.findSome? fun d => match d.placement with
    | .upgrade k => some (d, k)
    | _ => none

end CharterServer
