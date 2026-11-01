import HexGrid
import GpuCmd
import Charter.Games.HexMap
import Charter.Scene.Models
import Charter.Scene.Look

/-!
# The diorama (lean-gpu-cmd)

`render : Input → List GpuCmd.Cmd` draws a game's map as a model on a table: terrain by resource,
pieces that grow, and a square in the middle where every law in force stands as a monument. What the
world looks like is in its `Theme`. The Island's theme has a tray of sea, a beach, towns and harbours.
Decoration comes only from the state and fixed seeds, so every viewer sees the same world. The
browser's player draws the commands and reports clicks. It holds no game rules.
-/

namespace Charter.Scene
open GpuCmd HexGrid
open Charter.Games (TileDef)

/-- How a piece looks. `settlement` and `city` are a world's small and large piece on a spot. -/
inductive Shape where
  | settlement | city | custom (kind : PieceKind) (attached : Bool)

structure SpotPiece where
  v : Vertex
  owner : Nat
  shape : Shape
  /-- The corner's id, for a hover. -/
  id : Nat := 0

structure LinkPiece where
  e : Edge
  owner : Nat
  kind : PieceKind := "road"

inductive Marker where
  | spot (v : Vertex) (raised : Bool)
  | link (e : Edge)

/-- A hut beside a road, once the road has seen enough rounds. -/
def hut (seed : Nat) : List Part :=
  let side := if seed % 2 == 0 then 0.15 else -0.15
  let u := 0.2 * (rnd seed 4 - 0.5)
  house u side 0 0x7A5A3A plaster2 0.085 0.1 0.055

/-- The base game's square: paving and a stone with a gold cap. -/
def islandSquare : List Part :=
  let paving := (List.range 6).map fun i =>
    let a := pi / 3.0 * i.toFloat + pi / 6.0
    hexp (0.36 * Float.cos a) 0 (0.36 * Float.sin a) 0.2 0.006 (if i % 2 == 0 then 0xAEA282 else 0xC6BA9C)
  paving ++
    [ hexp 0 0 0 0.84 0.008 0xB6AA8C, hexp 0 0.008 0 0.25 0.012 0xE0D7BF
    , box 0 0.02 0 0.16 0.02 0.08 stoneDark, box 0 0.04 0 0.11 0.25 0.035 0x5F5A52
    , box 0 0.29 0 0.13 0.018 0.05 gold ]

/-- The base game's treasury: a chest, with a pile of coins as long as it holds something. -/
def islandChest (total : Nat) : List Part :=
  let body : List Part :=
    [ box 0 0 0 0.8 0.3 0.5 0x7A4D28, gable 0 0.3 0 0.5 0.14 0.8 0x8C5C31 (pi / 2.0)
    , box 0 0.13 0.255 0.11 0.14 0.014 gold, box (-0.3) 0 0 0.05 0.32 0.525 0x3E2716, box 0.3 0 0 0.05 0.32 0.525 0x3E2716 ]
  let coins := (List.range (min total 40)).map fun i =>
    let col := i % 8
    let lvl := i / 8
    let cx := -0.42 + (col % 4).toFloat * 0.23
    let cz := 0.52 + (col / 4).toFloat * 0.23
    cyl cx (lvl.toFloat * 0.042) cz 0.1 0.04 (if (i + lvl) % 3 == 0 then 0xF0C95C else gold)
  body ++ coins

/-- The base game's tiles in the 2D board. -/
def islandFlat : Option Res → UInt32
  | some "grain" => 0xF5C518
  | some "timber" => 0x2F9E44
  | some "ore" => 0x8FA3C4
  | some "wool" => 0x9BE15D
  | some "brick" => 0xE0612A
  | _ => 0xF0D9A0

/-- What one world looks like. Everything that names a resource or a piece is here, so a game with
other resources and pieces can be drawn by the same code. -/
structure Theme where
  /-- The colour behind everything. -/
  tableColor : UInt32
  /-- The colour of a hex. -/
  ground : Option Res → UInt32
  /-- The small things on a hex: seed, what to keep clear, how many pieces stand on it. -/
  decor : Option Res → Nat → (Float → Float → Bool) → Nat → List Part
  /-- What grows on a hex next to a piece: seed, how many, the direction to the piece. -/
  growth : Option Res → Nat → Nat → Float → Float → List Part
  /-- What stands around the map. -/
  surround : List Cmd
  /-- What lies under the tiles. -/
  under : List TileDef → List Cmd
  /-- How a piece of this game looks, if the game has its own look for it. -/
  shape : PieceKind → Option Shape
  /-- The model of the small piece on a spot, by seed, seat and round. -/
  smallModel : Nat → Nat → Nat → List Part
  /-- The model of the large piece on a spot, by seed, seat and round. -/
  largeModel : Nat → Nat → Nat → List Part
  /-- The model of a piece on a link, by kind and seat. -/
  linkModel : PieceKind → Nat → List Part
  /-- Pieces on the edge of the map get a pier and boats. -/
  harbours : Bool
  /-- The model of a piece this game has its own look for, by kind and seat. Such a piece is known by
  its shape, so it has no name over it. Other pieces, such as those laws make, do. -/
  ownModel : PieceKind → Nat → Option (List Part) := fun _ _ => none
  /-- The model of a piece a law made, by its name and seat. It has its name over it. -/
  madeModel : String → Nat → List Part := lawPieceModel
  /-- The colour of each seat. The model functions above use the same colours. -/
  seats : List UInt32 := seatColors
  /-- This world's mesh files, as `defineMeshFile` commands, with ids above the primitives' ids. -/
  meshDefs : List Cmd := []
  /-- What a tile is, by resource and seed, standing on the tile's base. Empty means the plain hex in
  the colour `ground`. The board stays a hex layout: pieces stand on the corners at height `top`. -/
  tileTop : Option Res → Nat → List Part := fun _ _ => []
  /-- What lights up on a tile whose number just came up. -/
  hotParts : List Part := [{ mesh := mHex, sx := 0.96, sy := 0.004, sz := 0.96, rgb := withAlpha 0xFFE27A 0.42 }]
  /-- A law's monument, by what the law is about. -/
  monumentModel : MonumentKind → List Part := monument
  /-- What the monuments stand around, on the first tile. -/
  square : List Part := islandSquare
  /-- What stands beside a link piece after enough rounds, by seed. -/
  roadside : Nat → List Part := hut
  /-- The treasury, by how much it holds. -/
  treasury : Nat → List Part := islandChest
  /-- The colour of a tile in the 2D board. -/
  flat : Option Res → UInt32 := islandFlat
  /-- Words, colours, fonts and marks off the board. -/
  look : Look := {}

instance : Inhabited Theme :=
  ⟨{ tableColor := 0, ground := fun _ => 0, decor := fun _ _ _ _ => [], growth := fun _ _ _ _ _ => []
     surround := [], under := fun _ => [], shape := fun _ => none
     smallModel := fun _ _ _ => [], largeModel := fun _ _ _ => [], linkModel := fun _ _ => [], harbours := false }⟩

structure Input where
  theme : Theme
  tiles : List TileDef
  /-- How many of the dice's outcomes give this number. It sets the dots on a token. -/
  chance : Nat → Nat
  spotPieces : List SpotPiece := []
  linkPieces : List LinkPiece := []
  /-- Legal spots for the viewer, each with its pick id. -/
  markers : List (Marker × UInt32) := []
  roll : Option Nat := none
  round : Nat := 0
  treasuryTotal : Nat := 0
  /-- Laws in force, oldest first: id and the monument it raises. -/
  laws : List (Nat × MonumentKind) := []

/-! Pick ids are stable between renders. -/
def spotPick (v : Nat) : UInt32 := (1 + v).toUInt32
def linkPick (l : Nat) : UInt32 := (1000 + l).toUInt32
def piecePick (spot : Nat) : UInt32 := (3000 + spot).toUInt32
def tilePick (i : Nat) : UInt32 := (7000 + i).toUInt32
def lawPick (id : Nat) : UInt32 := (9000 + id).toUInt32
def treasuryPick : UInt32 := 8999

def baseY : Float := 0.12
def tileH : Float := 0.16
/-- Height of the land everything stands on. -/
def top : Float := baseY + tileH

/-- The direction toward the camera, on the table. Tall things are kept out of the way of a token. -/
def toCamera : Float × Float := (0.7071, 0.7071)

/-- A tall thing here would hide the number token. -/
def hidesToken (x z : Float) : Bool :=
  let along := x * toCamera.1 + z * toCamera.2
  let across := x * toCamera.1 - z * toCamera.2
  along > 0.0 && Float.abs across < 0.3

/-- Scattered points inside a tile, away from its token and its edges. -/
def scatter (seed n : Nat) (rmin rmax : Float) : List (Float × Float × Nat) :=
  (List.range n).map fun i =>
    let a := 2.399963 * i.toFloat + 6.283 * rnd seed 1
    let r := rmin + (rmax - rmin) * Float.sqrt ((i.toFloat + 0.5) / n.toFloat) + 0.05 * (rnd seed (i + 40) - 0.5)
    (r * Float.cos a, r * Float.sin a, i)

/-! ## Terrain -/

def islandGround : Option Res → UInt32
  | some "grain" => 0xD6B04A
  | some "timber" => 0x4E7240
  | some "ore" => 0x8B8679
  | some "wool" => 0x9EBC5E
  | some "brick" => 0xB96C42
  | _ => 0xCFC4A8

/-- A pine: a trunk and two cones. -/
def pine (x z k : Float) (c : UInt32) : List Part :=
  [ cyl x 0 z (0.018 * k) (0.05 * k) timberDark
  , cone x (0.04 * k) z (0.085 * k) (0.15 * k) c
  , cone x (0.115 * k) z (0.062 * k) (0.12 * k) c ]

def forest (seed : Nat) (keep : Float → Float → Bool) (cut : Nat) : List Part :=
  let trees := (scatter seed 16 0.34 0.74).filter fun (x, z, _) => keep x z
  (trees.take (trees.length - min trees.length (cut * 2))).flatMap fun (x, z, i) =>
    let k := if hidesToken x z then 0.62 else 0.82 + 0.45 * rnd seed (i + 9)
    pine x z k (pickFrom [0x2F5A36, 0x3A6B3C, 0x27503A, 0x46773F] seed (i + 20))

def pasture (seed : Nat) (keep : Float → Float → Bool) : List Part :=
  let bumps := (scatter seed 7 0.36 0.72).filter fun (x, z, _) => keep x z
  let hills := bumps.map fun (x, z, i) =>
    lump x (-0.015) z (0.17 + 0.09 * rnd seed i) 0.05 (0.15 + 0.08 * rnd seed (i + 5))
      (pickFrom [0x8DAE52, 0xACC86B, 0x93B458] seed (i + 11))
  let sheep := (scatter (seed + 3) 5 0.4 0.68).filter (fun (x, z, _) => keep x z && !hidesToken x z) |>.flatMap fun (x, z, i) =>
    let r := 6.28 * rnd seed (i + 30)
    let (hx, hz) := turn r 0.042 0
    [ lump x 0.014 z 0.075 0.05 0.052 0xF4EFE2
    , ball (x + hx) 0.03 (z + hz) 0.032 0x38302C ]
  hills ++ sheep

def fields (seed : Nat) (keep : Float → Float → Bool) : List Part :=
  let r := pickFrom [0.0, pi / 3.0, -pi / 3.0] seed 2
  let rows := (List.range 9).flatMap fun i =>
    let u := -0.6 + i.toFloat * 0.15
    let len := 1.28 - 1.1 * Float.abs u
    let (x, z) := turn r 0 u
    if len < 0.25 then [] else
    let c := if i % 2 == 0 then 0xE8C966 else 0xC6962F
    [box x 0 z len 0.018 0.075 c r]
  let hay := (scatter (seed + 7) 3 0.42 0.66).filter (fun (x, z, _) => keep x z && !hidesToken x z) |>.map fun (x, z, _) =>
    cone x 0.018 z 0.05 0.09 0xEFD98C
  rows ++ hay

def mountains (seed : Nat) (keep : Float → Float → Bool) : List Part :=
  -- The big peaks stand behind the token, away from the camera.
  let peak (a r h w : Float) (i : Nat) : List Part :=
    let x := r * Float.cos a
    let z := r * Float.sin a
    if !keep x z then [] else
    let rock := pickFrom [0x76757B, 0x6A6971, 0x7F7D80] seed (i + 3)
    [ { mesh := mCone, x, y := 0, z, rot := 6.28 * rnd seed i, sx := w, sy := h, sz := w, rgb := rock }
    , { mesh := mCone, x, y := h * 0.68, z, rot := 6.28 * rnd seed i, sx := w * 0.33, sy := h * 0.32, sz := w * 0.33, rgb := 0xF3F1EA } ]
  let peaks :=
    peak (-2.4 + 0.3 * rnd seed 1) 0.46 0.56 0.27 1 ++ peak (-1.1 + 0.3 * rnd seed 2) 0.5 0.46 0.23 2 ++
    peak (-3.6 + 0.3 * rnd seed 3) 0.52 0.4 0.21 3 ++ peak (2.7 + 0.3 * rnd seed 4) 0.56 0.27 0.16 4 ++
    peak (-0.1 + 0.3 * rnd seed 5) 0.6 0.25 0.15 5
  let rocks := (scatter (seed + 2) 5 0.4 0.72).filter (fun (x, z, _) => keep x z) |>.map fun (x, z, i) =>
    lump x (-0.01) z (0.06 + 0.05 * rnd seed (i + 8)) 0.05 0.07 0x6F6E73
  peaks ++ rocks

def clayHills (seed : Nat) (keep : Float → Float → Bool) : List Part :=
  let terraces := (scatter seed 5 0.4 0.68).filter (fun (x, z, _) => keep x z && !hidesToken x z) |>.flatMap fun (x, z, i) =>
    let w := 0.15 + 0.08 * rnd seed (i + 4)
    let a := 6.28 * rnd seed (i + 13)
    [ hexp x 0 z w 0.04 0xA9592F a, hexp x 0.04 z (w * 0.66) 0.035 0xC67A49 a ]
  let pits := (scatter (seed + 5) 2 0.45 0.65).filter (fun (x, z, _) => keep x z) |>.map fun (x, z, _) =>
    cyl x 0.001 z 0.07 0.006 0x6E3B22
  let bricks := (scatter (seed + 9) 3 0.4 0.7).filter (fun (x, z, _) => keep x z) |>.flatMap fun (x, z, i) =>
    let r := 6.28 * rnd seed (i + 21)
    [box x 0 z 0.07 0.022 0.04 0x9B4526 r, box x 0.022 z 0.06 0.02 0.035 0xA9502E r]
  terraces ++ pits ++ bricks

/-- What grows near a town on this terrain. `c` is the unit direction toward the town. -/
def development (res : Option Res) (seed count : Nat) (cx cz : Float) : List Part :=
  let (px, pz) := (0 - cz, cx)
  let spot (i : Nat) : Float × Float :=
    let along := 0.5 - 0.1 * (i / 2).toFloat
    let side := (if i % 2 == 0 then 0.13 else -0.13) * (1.0 + (i / 2).toFloat * 0.5)
    (cx * along + px * side, cz * along + pz * side)
  (List.range count).flatMap fun i =>
    let (x, z) := spot i
    let r := 6.28 * rnd seed (i + 50)
    match res with
    | some "grain" =>  -- a windmill
      [ cyl x 0 z 0.05 0.13 plaster, cone x 0.13 z 0.06 0.05 0x8A5D34
      , box x 0.12 (z + 0.052) 0.2 0.022 0.006 0xF4EFE2 (0.7), box x 0.12 (z + 0.052) 0.2 0.022 0.006 0xF4EFE2 (-0.7) ]
    | some "wool" =>  -- a fenced pen with a sheep
      [ box x 0 (z - 0.06) 0.14 0.02 0.008 timberDark, box x 0 (z + 0.06) 0.14 0.02 0.008 timberDark
      , box (x - 0.07) 0 z 0.008 0.02 0.12 timberDark, box (x + 0.07) 0 z 0.008 0.02 0.12 timberDark
      , lump x 0.008 z 0.07 0.045 0.05 0xF4EFE2 ]
    | some "timber" =>  -- stumps and a stack of logs
      [ cyl x 0 z 0.024 0.02 timberDark
      , { mesh := mCyl, x := x + 0.06, y := 0, z := z + 0.03, rot := r, sx := 0.05, sy := 0.03, sz := 0.022, rgb := 0x8A5D34 }
      , { mesh := mCyl, x := x - 0.05, y := 0, z := z - 0.03, rot := r, sx := 0.05, sy := 0.03, sz := 0.022, rgb := 0x7A5230 } ]
    | some "ore" =>  -- a mine mouth with a timber frame
      [ box x 0 z 0.1 0.075 0.05 0x4A4A4E r, box x 0.075 z 0.125 0.016 0.06 timberDark r
      , lump (x + 0.07) 0 (z + 0.05) 0.06 0.03 0.05 0x57575C ]
    | some "brick" =>  -- a kiln and a brick stack
      [ cyl x 0 z 0.05 0.07 0x8C4A2C, cone x 0.07 z 0.05 0.04 0x6E3B22
      , box (x + 0.08) 0 (z + 0.03) 0.06 0.035 0.035 0xA9502E r ]
    | _ => []

/-- The Island's terrain, by the resource of a hex. -/
def islandDecor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (cut : Nat) : List Part :=
  match res with
  | some "timber" => forest seed keep cut
  | some "wool" => pasture seed keep
  | some "grain" => fields seed keep
  | some "ore" => mountains seed keep
  | some "brick" => clayHills seed keep
  | _ => []

def tileCmds (inp : Input) (i : Nat) (t : TileDef) : List Cmd :=
  let (x, z) := t.hex.toPixel 1.0
  let hot := t.number.isSome && t.number == inp.roll
  let corners := t.hex.vertices.map fun v =>
    let (vx, vz) := v.toPixel 1.0
    (v, vx - x, vz - z)
  let here := inp.spotPieces.filter fun b => corners.any (·.1 == b.v)
  let taken := corners.filter fun c => here.any (·.v == c.1)
  let keep (px pz : Float) : Bool :=
    taken.all fun (_, cx, cz) => (px - cx) * (px - cx) + (pz - cz) * (pz - cz) > 0.2
  let seed := 101 * (i + 3)
  let decor := inp.theme.decor t.res seed keep here.length
  let grown := here.zipIdx.flatMap fun (b, j) =>
    let (vx, vz) := b.v.toPixel 1.0
    let isCity := match b.shape with
      | .city => 1
      | _ => 0
    let count := 1 + isCity + min 1 (inp.round / 10)
    inp.theme.growth t.res (seed + 17 * j) count (vx - x) (vz - z)
  let ground := match inp.theme.tileTop t.res seed with
    | [] => [Cmd.draw mHex { pos := vec3 x baseY z, scale := vec3 0.992 tileH 0.992 } (inp.theme.ground t.res) (tilePick i)]
    | parts => parts.map (·.at x baseY z 0 (tilePick i))
  let token := match t.number with
    | some n =>
      let pips := inp.chance n
      let best := (inp.tiles.filterMap (·.number)).foldl (fun b m => max b (inp.chance m)) 0
      let red := pips == best
      let dots := (List.range pips).map fun k =>
        let u := (k.toFloat - (pips.toFloat - 1.0) / 2.0) * 0.038
        let (dx, dz) := (u * 0.7071 + 0.11 * 0.7071, 0 - u * 0.7071 + 0.11 * 0.7071)
        (cyl (x + dx) (top + 0.043) (z + dz) 0.012 0.002 (if red then 0xB5281F else ink)).at 0 0 0
      [ (cyl x top z 0.235 0.035 (if hot then 0xFFD45E else 0xF6EEDB)).at 0 0 0
      , (cyl x (top + 0.035) z 0.205 0.006 (if hot then 0xFFE08A else 0xFBF6E8)).at 0 0 0
      , .label (toString n) (vec3 (x - 0.015) (top + 0.11) (z - 0.015)) (F32.ofFloat 0.3) (if red then 0xB5281F else ink) 0 ] ++ dots
    | none => []
  let glow := if hot then placeAll inp.theme.hotParts x top z else []
  ground ++ glow ++ placeAll decor x top z ++ placeAll grown x top z ++ token

/-! ## The square in the middle -/

/-- Places for monuments. Towns can stand on the square's six corners, so monuments stand between
them: first along the back edges, then the front edges, then in an inner ring around the stone. -/
def monumentSlot (i : Nat) : Float × Float :=
  let edge (k : Nat) : Float := pi / 3.0 * k.toFloat
  let slots : List (Float × Float) :=
    [ (0.6, edge 4), (0.6, edge 3), (0.6, edge 5), (0.6, edge 2), (0.6, edge 0), (0.6, edge 1)
    , (0.33, edge 4 + 0.5), (0.33, edge 3 + 0.5), (0.33, edge 5 + 0.5), (0.33, edge 2 + 0.5), (0.33, edge 0 + 0.5), (0.33, edge 1 + 0.5)
    , (0.72, edge 4 + 0.32), (0.72, edge 3 + 0.32), (0.72, edge 5 + 0.32), (0.72, edge 2 + 0.32) ]
  let (r, a) := slots[i % slots.length]!
  (r * Float.cos a, r * Float.sin a)

def squareCmds (t : Theme) (x z : Float) (laws : List (Nat × MonumentKind)) : List Cmd :=
  let raised := laws.zipIdx.flatMap fun ((id, k), i) =>
    let (mx, mz) := monumentSlot i
    let parts := (t.monumentModel k).map (Part.scaled 1.5)
    let pick := lawPick id
    parts.map (·.at (x + mx) (top + 0.008) (z + mz) 0 pick) ++
    [.label s!"Law {id}" (vec3 (x + mx) (top + 0.47) (z + mz)) (F32.ofFloat 0.085) 0xFFF6E0 pick]
  placeAll t.square x top z ++ raised

/-! ## Pieces -/

def edgeAngle (e : Edge) : Float :=
  let (a, b) := e.ends
  let (x1, z1) := a.toPixel 1.0
  let (x2, z2) := b.toPixel 1.0
  Float.atan2 (-(z2 - z1)) (x2 - x1)

/-- A road in its owner's colour, with marks that differ by seat. Colour is not the only cue. -/
def roadParts (seat : Nat) : List Part :=
  let c := seatColor seat
  let marks : List Float := match seat % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.1, 0.1]
    | _ => [-0.2, 0, 0.2]
  [box 0 0 0 0.76 0.022 0.125 0x3F2C1C, box 0 0.02 0 0.74 0.024 0.092 c] ++
  marks.map fun u => box u 0.042 0 0.03 0.006 0.095 plaster

/-- A link piece a law made: a wall. -/
def wallParts (seat : Nat) : List Part :=
  [ box 0 0 0 0.78 0.06 0.075 stone, box 0 0.06 0 0.74 0.016 0.055 (seatColor seat)
  , box (-0.26) 0.06 0 0.05 0.04 0.09 stoneDark, box 0.26 0.06 0 0.05 0.04 0.09 stoneDark ]

def linkCmds (inp : Input) (j : Nat) (r : LinkPiece) : List Cmd :=
  let (x, z) := r.e.toPixel 1.0
  let a := edgeAngle r.e
  let seed := 977 * (j + 1) + (hashText (toString r.owner))
  let growth :=
    if seed % 3 == 0 && inp.round ≥ 6 + seed % 7 then inp.theme.roadside seed else []
  let parts := inp.theme.linkModel r.kind r.owner ++ growth
  placeAll parts x top z a

/-- Land spots touch up to three tiles. A spot touching one or two is on the coast. -/
def coastDir (inp : Input) (v : Vertex) : Option (Float × Float) :=
  let touching := inp.tiles.filter fun t => t.hex.vertices.contains v
  if !inp.theme.harbours || touching.length ≥ 3 then none
  else
    let (x, z) := v.toPixel 1.0
    let n := Float.sqrt (x * x + z * z)
    some (x / n, z / n)

/-- A pier and moored boats where a town meets the sea. -/
def harbour (seed seat count : Nat) : List Part :=
  let c := seatColor seat
  let posts := [0.3, 0.46, 0.62].map fun u =>
    cyl u (-0.2) 0.05 0.012 0.2 timberDark
  let pier := [box 0.42 (-0.02) 0 0.46 0.018 0.11 0x8A6A44] ++ posts
  let boat (i : Nat) : List Part :=
    let u := 0.46 + 0.17 * i.toFloat
    let side := if i % 2 == 0 then 0.17 else -0.17
    let h := 0.015 + 0.01 * rnd seed i
    [ box u (-0.135 + h) side 0.15 0.035 0.06 timberDark
    , box u (-0.1 + h) side 0.008 0.13 0.008 ink
    , gable u (-0.075 + h) side 0.09 0.09 0.006 c (pi / 2.0) ]
  pier ++ (List.range count).flatMap boat

/-- Towns are drawn larger than life, so they read at a glance from across the table. -/
def pieceScale : Float := 1.28

def spotCmds (inp : Input) (j : Nat) (b : SpotPiece) : List Cmd :=
  let (x, z) := b.v.toPixel 1.0
  let seed := 613 * (j + 11)
  let turnOf := match b.shape with
    | .custom k _ => pickFrom [0.0, pi / 3.0, -pi / 3.0, pi, 2.0 * pi / 3.0, -2.0 * pi / 3.0] (hashText k) (j % 3)
    | _ => pickFrom [0.0, pi / 3.0, -pi / 3.0, pi] seed 1
  let (body, offset) : List Part × (Float × Float) := match b.shape with
    | .settlement => (inp.theme.smallModel seed b.owner inp.round, (0, 0))
    | .city => (inp.theme.largeModel seed b.owner inp.round, (0, 0))
    | .custom k true =>
      ((inp.theme.ownModel k b.owner).getD (inp.theme.madeModel k b.owner), (0.2 * Float.cos turnOf, 0.2 * Float.sin turnOf))
    | .custom k false => ((inp.theme.ownModel k b.owner).getD (inp.theme.madeModel k b.owner), (0, 0))
  let name : List Cmd := match b.shape with
    | .custom k _ =>
      if (inp.theme.ownModel k b.owner).isSome then []
      else [.label k (vec3 (x + offset.1) (top + 0.5) (z + offset.2)) (F32.ofFloat 0.09) 0xFFF6E0 0]
    | _ => []
  let port : List Cmd := match coastDir inp b.v, b.shape with
    | some (dx, dz), .settlement =>
      if inp.round ≥ 2 then
        placeAll (harbour seed b.owner (1 + min 1 (inp.round / 8))) x top z (Float.atan2 (-dz) dx)
      else []
    | some (dx, dz), .city =>
      placeAll (harbour seed b.owner (2 + min 1 (inp.round / 10))) x top z (Float.atan2 (-dz) dx)
    | _, _ => []
  let turned := if offset.1 == 0 && offset.2 == 0 then 0 else turnOf
  (body.map (Part.scaled pieceScale)).map (·.at (x + offset.1) top (z + offset.2) turned (piecePick b.id)) ++ name ++ port

/-- What you can do here: a gold disc and a pulsing bead. -/
def markerCmds : Marker × UInt32 → List Cmd
  | (.spot v raised, pick) =>
    let (x, z) := v.toPixel 1.0
    let y := if raised then top + 0.46 else top + 0.03
    [ .draw mCyl { pos := vec3 x top z, scale := vec3 0.13 0.012 0.13 } (withAlpha 0xFFE08A 0.8) pick
    , .draw mBall { pos := vec3 x y z, scale := vec3 0.15 0.15 0.15 } 0xFFD45E pick
    , .highlight pick 0xFFF4D0 ]
  | (.link e, pick) =>
    let (x, z) := e.toPixel 1.0
    [ .draw mBox { pos := vec3 x (top + 0.01) z, rotY := F32.ofFloat (edgeAngle e), scale := vec3 0.62 0.05 0.13 }
        0xFFD45E pick
    , .highlight pick 0xFFE9A8 ]

/-! ## The tray, the sea, the treasury -/

def trayCmds : List Cmd :=
  let r30 := pi / 6.0
  let waves := (List.range 40).map fun i =>
    let a := 2.399963 * i.toFloat
    let rr := 4.5 + 0.28 * rnd 77 i
    let x := rr * Float.cos a
    let z := rr * Float.sin a
    (box x 0.1 z (0.1 + 0.16 * rnd 78 i) 0.002 0.014 0x5AA0AE (a + pi / 2.0)).at 0 0 0
  [ (hexp 0 0 0 5.9 0.085 0x4A2F1B r30).at 0 0 0
  , (hexp 0 0.085 0 5.62 0.015 0x2C6F86 r30).at 0 0 0 ] ++ waves

/-- A beach and low land under every tile, so the island reads as one mass. -/
def landCmds (tiles : List TileDef) : List Cmd :=
  tiles.flatMap fun t =>
    let (x, z) := t.hex.toPixel 1.0
    [ .draw mLand { pos := vec3 x 0.02 z, scale := vec3 1.2 0.085 1.2 } 0x4F9AA3 0
    , .draw mLand { pos := vec3 x 0.02 z, scale := vec3 1.1 0.12 1.1 } 0xDCC793 0 ]

/-- The treasury stands on the table, on the near side of the map. Its pile shows what it holds. -/
def treasuryCmds (t : Theme) (total : Nat) : List Cmd :=
  let x := 5.95
  let z := -2.0
  let r := -0.8
  (t.treasury total).map (·.at x 0 z r treasuryPick)

/-! ## The whole table -/

/-- The look of the Island. -/
def islandTheme : Theme :=
  { tableColor := 0x2A1C12
    ground := islandGround
    decor := islandDecor
    growth := development
    surround := trayCmds
    under := landCmds
    shape := fun k =>
      if k == "settlement" then some .settlement else if k == "city" then some .city else none
    smallModel := settlement
    largeModel := city
    linkModel := fun k seat => if k == "road" then roadParts seat else wallParts seat
    harbours := true }

/-- The camera looks down from a fixed corner at about 38 degrees. The negative field of view asks
for an orthographic view that keeps this radius in sight at any window shape. -/
def viewRadius : Float := 5.95

def render (inp : Input) : List Cmd :=
  [ .clear inp.theme.tableColor
  , .camera (vec3 11.2 11.0 11.2) (vec3 0 0.05 0) (F32.ofFloat (-viewRadius))
  , .light (vec3 (-0.62) (-1) (-0.2)) (F32.ofFloat 1.2) ] ++
  meshes ++
  inp.theme.meshDefs ++
  inp.theme.surround ++
  inp.theme.under inp.tiles ++
  (inp.tiles.zipIdx.flatMap fun (t, i) => tileCmds inp i t) ++
  (match inp.tiles.head? with
   | some t => let (x, z) := t.hex.toPixel 1.0; squareCmds inp.theme x z inp.laws
   | none => []) ++
  (inp.linkPieces.zipIdx.flatMap fun (r, j) => linkCmds inp j r) ++
  (inp.spotPieces.zipIdx.flatMap fun (b, j) => spotCmds inp j b) ++
  inp.markers.flatMap markerCmds ++
  treasuryCmds inp.theme inp.treasuryTotal

def renderBytes (inp : Input) : ByteArray := GpuCmd.encode (render inp)

end Charter.Scene
