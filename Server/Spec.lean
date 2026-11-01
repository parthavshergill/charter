import Charter.Games.Island
import Charter.Games.Belt
import Charter.Games.NotCatan
import Charter.Scene.OfState
import Charter.Scene.Belt

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

A pack's name and sentence are what a player reads when choosing it, so keep the sentence short and
plain. `Server/PreviewCheck.lean` plays every pack with bots, and `ServerTests.lean` checks its layout.
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
    guide := "Laurel is not harvested. It pays for a wreath, and there are laurels for only two wreaths in the game." }

instance : Inhabited GameSpec := ⟨islandSpec⟩

/-- Every game this server can run. The first is the default. -/
def gameSpecs : List GameSpec := [islandSpec, beltSpec, notCatanSpec]

/-- The game with this id. A log entry with no id is from before there was a choice: it is the Island. -/
def specOf? (id : Option String) : Option GameSpec :=
  match id with
  | none => some islandSpec
  | some i => gameSpecs.find? (·.id == i)

/-! ## Counters

A game can have a resource that no piece and no law fee costs. Nobody wants it for itself, so it is a
counter that laws read, such as a flag a law keeps in the treasury. The screen and the Claude seats leave it out of hands,
trades and what a corner pays. It is still in the books and the laws' text, and the rules treat it like
any other resource. -/

/-- This resource is a counter and not a good. -/
abbrev markRes := Scene.markRes

/-- The resources a person trades and holds. -/
def goodsOf (G : GameDef) : List Res := (G.resources.map (·.name)).filter (!markRes G ·)

/-- The regions that pay goods. -/
def paidRegions (G : GameDef) : List Region := G.map.regions.filter (!markRes G ·.res)

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
