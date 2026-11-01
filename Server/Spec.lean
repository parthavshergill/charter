import Charter.Games.Island
import Charter.Games.Belt
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
-/

namespace CharterServer
open Charter

/-- A game a table can play: its definition, the proof that it is valid, and how to draw it. -/
structure GameSpec where
  id : String
  G : GameDef
  valid : G.Valid
  layout : Scene.Layout

def islandSpec : GameSpec :=
  { id := "island"
    G := Games.Island.island
    valid := Games.Island.island_valid
    layout :=
      { tiles := Games.Island.tiles, spots := Games.Island.spots, edges := Games.Island.edges
        links := Games.Island.links, theme := Scene.islandTheme, word := "the island" } }

def beltSpec : GameSpec :=
  { id := "belt"
    G := Games.Belt.belt
    valid := Games.Belt.belt_valid
    layout :=
      { tiles := Games.Belt.tiles, spots := Games.Belt.spots, edges := Games.Belt.edges
        links := Games.Belt.links, theme := Scene.BeltLook.theme, word := "the belt" } }

instance : Inhabited GameSpec := ⟨islandSpec⟩

/-- Every game this server can run. The first is the default. -/
def gameSpecs : List GameSpec := [islandSpec, beltSpec]

/-- The game with this id. A log entry with no id is from before there was a choice: it is the Island. -/
def specOf? (id : Option String) : Option GameSpec :=
  match id with
  | none => some islandSpec
  | some i => gameSpecs.find? (·.id == i)

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
