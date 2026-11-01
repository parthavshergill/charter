import Server.Spec

/-!
# A pack's contact sheet

`make contact-sheet PACK=<id>` runs this. It writes a scene with all of a pack's looks in one view: each
model in each seat's colour, every tile top, every monument, and models together on real tiles. It calls
the same functions a game does, at the same scale, under the same camera and light. Only the place
each thing stands is different. `scripts/contact_sheet.py` draws the scene with the real player.
-/

namespace CharterServer.ContactSheet
open GpuCmd HexGrid Charter Charter.Scene
open Charter.Games (TileDef)

/-- The sheet's own radius. At the window size the tool asks for, this gives the scale of a game in a
1440 by 900 window: about 90 pixels to a hex's side. -/
def sheetRadius : Float := 12.0

/-- The floor directions as the viewer sees them: `u` to the right, `v` away from the viewer. -/
def world (u v : Float) : Float × Float := (0.7071 * (u - v), -0.7071 * (u + v))

/-- Move a command across the table. -/
def shift (dx dz : Float) : Cmd → Cmd
  | .draw m t c p =>
    .draw m { t with pos := vec3 (t.pos.x.toFloat + dx) t.pos.y.toFloat (t.pos.z.toFloat + dz) } c p
  | .label s pos k c p => .label s (vec3 (pos.x.toFloat + dx) pos.y.toFloat (pos.z.toFloat + dz)) k c p
  | c => c

def heading (text : String) (u v : Float) : Cmd :=
  let (x, z) := world u v
  .label text (vec3 x 0.2 z) (F32.ofFloat 0.3) 0xFFF6E0 0

/-- A plate behind one part of the sheet, in the colour of the pack's own tiles. -/
def plate (rgb : UInt32) (u v w d : Float) : Cmd :=
  let (x, z) := world u v
  (box x 0 z w 0.01 d rgb (pi / 4.0)).at 0 0 0

def at_ (parts : List Part) (u v : Float) (r : Float := 0) : List Cmd :=
  let (x, z) := world u v
  parts.map (·.at x top z r)

/-- Rows of each piece in each seat's colour. -/
def models (d : GameSpec) (u0 v0 : Float) : List Cmd :=
  let t := d.layout.theme
  let seats := List.range (min t.seats.length d.maxSeats)
  let rows := d.G.pieces.zipIdx.flatMap fun (p, row) =>
    let v := v0 - 1.75 * row.toFloat
    let isLink := match p.placement with
      | .link => true
      | _ => false
    let name := heading p.name (u0 - 1.1) v
    name :: seats.flatMap fun s =>
      let parts := (pieceModel t p s).getD (t.madeModel p.name s)
      at_ (if isLink then parts else parts.map (Part.scaled pieceScale)) (u0 + 1.25 * s.toFloat) v (if isLink then pi / 12.0 else 0)
  rows

/-- A tile at this place, by the same function a game uses. -/
def oneTile (inp : Input) (i : Nat) (t : TileDef) (u v : Float) : List Cmd :=
  let (x, z) := world u v
  (tileCmds inp i t).map (shift x z)

/-- Every tile top, with a number token where the game has one, one of them lit. -/
def tileRow (d : GameSpec) (u0 v0 : Float) : List Cmd :=
  let L := d.layout
  let kinds := (none :: (L.tiles.filterMap (·.res)).eraseDups.map some : List (Option String))
  let inp : Input := { theme := L.theme, tiles := L.tiles, chance := chanceOf d.G, roll := some 8 }
  (kinds.zipIdx.flatMap fun (r, i) =>
    let t : TileDef := { hex := Hex.origin, res := r, number := if r.isSome then some (if i == 1 then 8 else 6 + i) else none }
    oneTile inp (i + 3) t (u0 + 2.2 * i.toFloat) v0)

/-- Every monument. -/
def monumentRow (d : GameSpec) (u0 v0 : Float) : List Cmd :=
  let t := d.layout.theme
  let kinds : List (String × MonumentKind) :=
    [ ("cost", .cost), ("points", .points), ("bank", .bank), ("harvest", .harvest), ("build", .build)
    , ("round", .roundEnd), ("piece", .newPiece "x"), ("repeal", .repeal) ]
  kinds.zipIdx.flatMap fun ((name, k), i) =>
    let u := u0 + 1.15 * i.toFloat
    at_ ((t.monumentModel k).map (Part.scaled 1.5)) u v0 ++ [heading name u (v0 - 0.55)]

/-- Real tiles with real pieces on them, as a game draws them, with the numbers showing. -/
def cluster (d : GameSpec) (u0 v0 : Float) : List Cmd :=
  let L := d.layout
  let t := L.theme
  let hexes := [Hex.origin, ⟨1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩]
  let goods := (L.tiles.filterMap (·.res)).eraseDups
  let tiles : List TileDef := hexes.zipIdx.map fun (h, i) =>
    { hex := h, res := goods[i % max 1 goods.length]?, number := some (4 + (3 * i) % 7) }
  let verts := (hexes.flatMap (·.vertices)).eraseDups
  let edges := (hexes.flatMap (·.edges)).eraseDups
  let small := d.G.pieces.find? fun p => match p.placement with | .spot => true | _ => false
  let large := d.G.pieces.find? fun p => match p.placement with | .upgrade _ => true | _ => false
  let link := d.G.pieces.find? fun p => match p.placement with | .link => true | _ => false
  let attach := d.G.pieces.find? fun p => match p.placement with | .attach _ => true | _ => false
  let spot (i owner : Nat) (shape : Shape) : List SpotPiece :=
    match verts[i]? with
    | some v => [{ v, owner, shape, id := i }]
    | none => []
  let pieces := spot 0 0 .settlement ++ spot 2 1 .settlement ++ spot 4 2 .city ++ spot 7 3 .settlement ++
    (match attach with
     | some p => spot 0 0 (.custom p.name true) ++ spot 7 3 (.custom p.name true)
     | none => [])
  let _ := (small, large)
  let links : List LinkPiece := (edges.take 8).zipIdx.map fun (e, i) =>
    { e, owner := i % 4, kind := (link.map (·.name)).getD "road" }
  let inp : Input :=
    { theme := t, tiles, chance := chanceOf d.G, spotPieces := pieces, linkPieces := links, roll := some 7, round := 12 }
  let (x, z) := world u0 v0
  ((tiles.zipIdx.flatMap fun (tl, i) => tileCmds inp i tl) ++
   (links.zipIdx.flatMap fun (r, j) => linkCmds inp j r) ++
   (pieces.zipIdx.flatMap fun (b, j) => spotCmds inp j b)).map (shift x z)

/-- The whole sheet. -/
def sheet (d : GameSpec) : List Cmd :=
  let t := d.layout.theme
  [ .clear t.tableColor
  , .camera (vec3 11.2 11.0 11.2) (vec3 0 0.05 0) (F32.ofFloat (-sheetRadius))
  , .light (vec3 (-0.62) (-1) (-0.2)) (F32.ofFloat 1.2) ] ++
  meshes ++ t.meshDefs ++
  [plate 0x2A2C26 0 0 60 60] ++
  [heading "models" (-9.5) 12.5] ++ models d (-9.5) 11 ++
  [heading "tile tops" 1.5 12.5] ++ tileRow d 1.5 10.5 ++
  [heading "monuments" 1.5 7.5] ++ monumentRow d 1.5 6 ++
  [heading "together, at game size" (-9.5) 2.8] ++ cluster d (-5.5) (-3) ++
  [heading "the treasury, full and empty" 4 2.8] ++ ((t.treasury 18).map (fun p =>
    let (x, z) := world 4 1
    p.at x 0 z)) ++ ((t.treasury 0).map (fun p =>
    let (x, z) := world 7 1
    p.at x 0 z))

end CharterServer.ContactSheet

open CharterServer in
def main (args : List String) : IO UInt32 := do
  match args with
  | [id, out] =>
    match specOf? (some id) with
    | some d =>
      IO.FS.writeBinFile out (GpuCmd.encode (ContactSheet.sheet d))
      return 0
    | none =>
      IO.eprintln s!"no pack is called {id}. The packs are {gameSpecs.map (·.id)}"
      return 1
  | _ =>
    IO.eprintln "say which pack and where the scene goes: charter-contact <pack> <file>"
    return 1
