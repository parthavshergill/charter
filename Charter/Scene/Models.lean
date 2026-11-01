import HexGrid
import GpuCmd

/-!
# Small models of the world

Every shape on the table is built here from a few unit meshes. A `Part` is one mesh with its offset,
turn, size and colour. A model is a list of parts around its own origin. Nothing here reads the game:
callers pass in a seed, so the same state always draws the same world.
-/

namespace Charter.Scene
open GpuCmd

def pi : Float := 3.141592653589793

def mBox : UInt32 := 1
def mCyl : UInt32 := 2
def mCone : UInt32 := 3
def mBall : UInt32 := 4
def mGable : UInt32 := 5
def mPyramid : UInt32 := 6
def mHex : UInt32 := 7
def mLand : UInt32 := 8

/-- Unit meshes. Sizes come from each draw's scale, so the stream defines only these. -/
def meshes : List Cmd :=
  [ .defineMesh mBox (.box 1 1 1), .defineMesh mCyl (.cylinder 1 1), .defineMesh mCone (.cone 1 1)
  , .defineMesh mBall (.sphere 0.5), .defineMesh mGable (.gable 1 1 1), .defineMesh mPyramid (.pyramid 1 1)
  , .defineMesh mHex (.hexPrism 1 1), .defineMesh mLand (.hexPrism 1 1) ]

structure Part where
  mesh : UInt32
  x : Float := 0
  y : Float := 0
  z : Float := 0
  rot : Float := 0
  sx : Float := 1
  sy : Float := 1
  sz : Float := 1
  rgb : UInt32

def box (x y z w h d : Float) (rgb : UInt32) (rot : Float := 0) : Part :=
  { mesh := mBox, x, y, z, rot, sx := w, sy := h, sz := d, rgb }
def cyl (x y z r h : Float) (rgb : UInt32) : Part :=
  { mesh := mCyl, x, y, z, sx := r, sy := h, sz := r, rgb }
def cone (x y z r h : Float) (rgb : UInt32) : Part :=
  { mesh := mCone, x, y, z, sx := r, sy := h, sz := r, rgb }
def ball (x y z d : Float) (rgb : UInt32) : Part :=
  { mesh := mBall, x, y, z, sx := d, sy := d, sz := d, rgb }
def lump (x y z w h d : Float) (rgb : UInt32) : Part :=
  { mesh := mBall, x, y, z, sx := w, sy := h, sz := d, rgb }
def gable (x y z w h d : Float) (rgb : UInt32) (rot : Float := 0) : Part :=
  { mesh := mGable, x, y, z, rot, sx := w, sy := h, sz := d, rgb }
def pyr (x y z r h : Float) (rgb : UInt32) (rot : Float := 0) : Part :=
  { mesh := mPyramid, x, y, z, rot, sx := r, sy := h, sz := r, rgb }
def hexp (x y z r h : Float) (rgb : UInt32) (rot : Float := 0) : Part :=
  { mesh := mHex, x, y, z, rot, sx := r, sy := h, sz := r, rgb }

/-- A part at a larger size, about its model's origin. -/
def Part.scaled (k : Float) (p : Part) : Part :=
  { p with x := p.x * k, y := p.y * k, z := p.z * k, sx := p.sx * k, sy := p.sy * k, sz := p.sz * k }

/-- Turn a point about +Y the way the player does. -/
def turn (r x z : Float) : Float × Float :=
  (x * Float.cos r + z * Float.sin r, z * Float.cos r - x * Float.sin r)

/-- Place a part in the world: turn it about the model's origin, then move it. -/
def Part.at (p : Part) (ox oy oz : Float) (r : Float := 0) (pick : UInt32 := 0) : Cmd :=
  let (x, z) := turn r p.x p.z
  .draw p.mesh
    { pos := vec3 (ox + x) (oy + p.y) (oz + z), rotY := F32.ofFloat (p.rot + r)
      scale := vec3 p.sx p.sy p.sz } p.rgb pick

def placeAll (ps : List Part) (ox oy oz : Float) (r : Float := 0) : List Cmd :=
  ps.map (·.at ox oy oz r)

/-- A number in [0, 1), fixed by the seed and the index. -/
def rnd (seed i : Nat) : Float :=
  let a := (seed * 2654435761 + i * 40503 + 12345) % 4294967296
  let b := ((a ^^^ (a >>> 13)) * 1274126177) % 4294967296
  (((b ^^^ (b >>> 16)) % 65536).toFloat) / 65536.0

def pickFrom {α : Type} [Inhabited α] (xs : List α) (seed i : Nat) : α :=
  xs[(rnd seed i * xs.length.toFloat).toUInt64.toNat % xs.length]!

/-- A simple text hash, so a law-made piece keeps one look for its name. -/
def hashText (s : String) : Nat :=
  s.foldl (fun h c => (h * 31 + c.toNat) % 1000003) 7

/-! ## Colours -/

/-- Heraldic colours by seat: gules, azure, or, vert, purpure, rose. The web client reads these too. -/
def seatColors : List UInt32 := [0xB5281F, 0x2257AE, 0xE39A1B, 0x1C8560, 0x6F42A8, 0xC4507F]
def seatColor (i : Nat) : UInt32 := seatColors[i % 6]!

def plaster : UInt32 := 0xEDE3CC
def plaster2 : UInt32 := 0xE2D4B6
def stone : UInt32 := 0xB9B2A2
def stoneDark : UInt32 := 0x8F8A7F
def timberDark : UInt32 := 0x5B3E26
def gold : UInt32 := 0xE5B84B
def marble : UInt32 := 0xF4EFE3
def ink : UInt32 := 0x2A2017

/-! ## Buildings -/

/-- One small house: pale walls and a roof in the owner's colour. -/
def house (x z r : Float) (roof walls : UInt32) (w : Float := 0.125) (d : Float := 0.165) (h : Float := 0.085) : List Part :=
  let rt := 0.078
  [ box x 0 z w h d walls r
  , gable x h z (w * 1.34) rt (d * 1.16) roof r ]

/-- A flagpole. The flag's shape differs by seat, so colour is not the only cue. -/
def flag (x y z : Float) (seat : Nat) : List Part :=
  let c := seatColor seat
  let pole := box x y z 0.012 0.2 0.012 ink
  let top := y + 0.2
  let cloth := match seat % 4 with
    | 0 => [box (x + 0.05) (top - 0.075) z 0.09 0.07 0.006 c]
    | 1 => [box (x + 0.032) (top - 0.105) z 0.055 0.105 0.006 c]
    | 2 => [{ mesh := mCone, x := x + 0.012, y := top - 0.04, z := z, sx := 0.04, sy := -0.09, sz := 0.008, rgb := c }]
    | _ => [box (x + 0.04) (top - 0.05) z 0.07 0.035 0.006 c, box (x + 0.04) (top - 0.1) z 0.07 0.035 0.006 c]
  pole :: cloth

/-- Rooms around the spot: a few houses, more as the rounds pass. -/
def settlement (seed seat round : Nat) : List Part :=
  let roof := seatColor seat
  let extra := min 2 (round / 9)
  let spots : List (Float × Float) :=
    [(0.0, -0.075), (-0.135, 0.075), (0.125, 0.07), (-0.02, 0.17), (0.16, -0.1)]
  let n := 3 + extra
  let houses := ((spots.take n).zipIdx).flatMap fun ((x, z), i) =>
    let r := pickFrom [0.0, pi / 2.0, 0.5, -0.6] seed i
    let walls := if i % 2 == 0 then plaster else plaster2
    let k := 0.92 + 0.22 * rnd seed (i + 7)
    house x z r roof walls (0.125 * k) (0.165 * k) (0.085 * k)
  houses ++ flag 0.02 0.08 (-0.14) seat

/-- A walled town: a ring of wall, towers, a keep and close rows of houses. -/
def city (seed seat round : Nat) : List Part :=
  let roof := seatColor seat
  let ring := 0.335
  let corner (i : Nat) : Float × Float :=
    let a := pi / 3.0 * i.toFloat + pi / 6.0
    (ring * Float.cos a, ring * Float.sin a)
  let walls := (List.range 6).map fun i =>
    let (x1, z1) := corner i
    let (x2, z2) := corner (i + 1)
    box ((x1 + x2) / 2.0) 0 ((z1 + z2) / 2.0) ring 0.085 0.036 stone
      (Float.atan2 (-(z2 - z1)) (x2 - x1))
  let towers := (List.range 6).flatMap fun i =>
    let (x, z) := corner i
    if i % 2 == 0 then
      [cyl x 0 z 0.052 0.17 stone, cone x 0.17 z 0.067 0.095 roof]
    else [cyl x 0 z 0.04 0.11 stoneDark]
  let keep :=
    [box 0.0 0 (-0.06) 0.15 0.23 0.15 stone, pyr 0.0 0.23 (-0.06) 0.125 0.115 roof (pi / 4.0)]
  let spots : List (Float × Float) :=
    [(-0.17, -0.08), (0.17, -0.09), (-0.19, 0.07), (0.18, 0.07), (-0.05, 0.14), (0.06, 0.18), (-0.1, -0.2), (0.1, -0.21)]
  let n := 6 + min 2 (round / 12)
  let houses := ((spots.take n).zipIdx).flatMap fun ((x, z), i) =>
    let r := pickFrom [0.0, pi / 2.0, 0.3, -0.3] seed i
    let walls := if i % 2 == 0 then plaster else plaster2
    house x z r roof walls 0.105 0.135 (0.075 + 0.03 * rnd seed (i + 3))
  [hexp 0 0 0 0.32 0.012 stoneDark (pi / 6.0)] ++ walls ++ towers ++ keep ++ houses ++ flag 0.0 0.34 (-0.06) seat

/-! ## Pieces a law can create -/

/-- A striped tower with a lamp. -/
def lighthouse (seat : Nat) : List Part :=
  let c := seatColor seat
  [ cyl 0 0 0 0.075 0.015 stoneDark, cyl 0 0.015 0 0.058 0.09 plaster, cyl 0 0.105 0 0.052 0.08 c
  , cyl 0 0.185 0 0.046 0.08 plaster, cyl 0 0.265 0 0.052 0.015 ink, ball 0 0.28 0 0.07 0xFFD76A
  , cone 0 0.345 0 0.05 0.05 c ]

/-- A windmill with crossed sails. -/
def windmill (seat : Nat) : List Part :=
  let c := seatColor seat
  [ cyl 0 0 0 0.07 0.2 plaster2, cone 0 0.2 0 0.08 0.07 c
  , box 0 0.2 0.075 0.26 0.018 0.008 timberDark, box 0 0.075 0.075 0.018 0.26 0.008 timberDark ]

/-- A small temple with columns. -/
def temple (seat : Nat) : List Part :=
  let cols := [(-0.07, -0.08), (0.07, -0.08), (-0.07, 0.0), (0.07, 0.0), (-0.07, 0.08), (0.07, 0.08)]
  [box 0 0 0 0.22 0.025 0.25 stone] ++
  cols.map (fun (x, z) => cyl x 0.025 z 0.016 0.11 plaster) ++
  [box 0 0.135 0 0.2 0.018 0.23 plaster2, gable 0 0.153 0 0.215 0.06 0.24 (seatColor seat)]

/-- A tall stone tower with battlements. -/
def watchtower (seat : Nat) : List Part :=
  [ box 0 0 0 0.13 0.27 0.13 stone, box 0 0.27 0 0.16 0.03 0.16 stoneDark
  , box (-0.06) 0.3 (-0.06) 0.035 0.035 0.035 stoneDark, box 0.06 0.3 (-0.06) 0.035 0.035 0.035 stoneDark
  , box (-0.06) 0.3 0.06 0.035 0.035 0.035 stoneDark, box 0.06 0.3 0.06 0.035 0.035 0.035 stoneDark
  , box 0 0.14 0.068 0.13 0.05 0.006 (seatColor seat) ]

/-- A round hall with a gold dome. -/
def domeHall (seat : Nat) : List Part :=
  [ cyl 0 0 0 0.12 0.11 plaster, cyl 0 0.11 0 0.125 0.012 (seatColor seat), ball 0 0.08 0 0.2 gold ]

/-- A market: an open timber frame and stalls. -/
def market (seat : Nat) : List Part :=
  let c := seatColor seat
  [ box (-0.09) 0 (-0.06) 0.1 0.04 0.07 timberDark, box 0.09 0 (-0.06) 0.1 0.04 0.07 timberDark
  , box 0 0 0.07 0.12 0.04 0.07 timberDark
  , gable (-0.09) 0.075 (-0.06) 0.13 0.05 0.1 c, gable 0.09 0.075 (-0.06) 0.13 0.05 0.1 plaster
  , gable 0 0.075 0.07 0.15 0.05 0.1 c
  , box (-0.09) 0.04 (-0.06) 0.01 0.04 0.01 ink, box 0.09 0.04 (-0.06) 0.01 0.04 0.01 ink
  , box 0 0.04 0.07 0.01 0.04 0.01 ink ]

/-- A keep: one strong tower on a mound. -/
def keepModel (seat : Nat) : List Part :=
  [ cyl 0 0 0 0.17 0.04 stoneDark, box 0 0.04 0 0.2 0.2 0.2 stone
  , pyr 0 0.24 0 0.17 0.14 (seatColor seat) (pi / 4.0) ]

/-- A granary: a wide drum under a low cone. -/
def granary (seat : Nat) : List Part :=
  [ cyl (-0.05) 0 0 0.07 0.13 plaster2, cone (-0.05) 0.13 0 0.085 0.06 (seatColor seat)
  , cyl 0.08 0 0.03 0.055 0.1 plaster, cone 0.08 0.1 0.03 0.07 0.05 (seatColor seat) ]

/-- An obelisk. -/
def obeliskModel (seat : Nat) : List Part :=
  [ box 0 0 0 0.13 0.03 0.13 stone, box 0 0.03 0 0.06 0.24 0.06 stoneDark
  , pyr 0 0.27 0 0.05 0.05 (seatColor seat) (pi / 4.0) ]

/-- A law-made piece gets its own model. The name picks a model when it means something, and
otherwise the name's hash picks one, so every viewer sees the same one. -/
def lawPieceModel (name : String) (seat : Nat) : List Part :=
  let has (ws : List String) := ws.any fun w => (name.splitOn w).length > 1
  if has ["light", "beacon", "lamp"] then lighthouse seat
  else if has ["mill"] then windmill seat
  else if has ["temple", "church", "chapel", "shrine", "abbey", "school", "library", "court"] then temple seat
  else if has ["tower", "watch", "guard", "fort"] then watchtower seat
  else if has ["market", "bazaar", "fair", "stall", "port", "dock", "harbo"] then market seat
  else if has ["castle", "keep", "palace", "citadel"] then keepModel seat
  else if has ["granary", "barn", "silo", "store", "farm"] then granary seat
  else if has ["bank", "mint", "hall", "dome", "theatre", "bath", "guild"] then domeHall seat
  else
    match hashText name % 6 with
    | 0 => windmill seat
    | 1 => temple seat
    | 2 => watchtower seat
    | 3 => market seat
    | 4 => granary seat
    | _ => obeliskModel seat

/-! ## Monuments in the square -/

/-- What a law is about, for choosing its monument. -/
inductive MonumentKind where
  | cost | points | bank | harvest | build | roundEnd | roll | newPiece (name : String) | repeal

/-- A monument raised for a law. The kind sets its shape, and each stands on a plinth. -/
def monument : MonumentKind → List Part
  | .cost =>  -- a balance on a column
    [ box 0 0 0 0.12 0.035 0.12 marble, cyl 0 0.03 0 0.022 0.2 plaster
    , box 0 0.225 0 0.15 0.012 0.018 gold, cone (-0.07) 0.195 0 0.03 0.03 gold, cone 0.07 0.195 0 0.03 0.03 gold ]
  | .points =>  -- a column crowned in gold
    [ box 0 0 0 0.12 0.035 0.12 marble, cyl 0 0.03 0 0.027 0.22 plaster, ball 0 0.245 0 0.07 gold ]
  | .bank =>  -- a stack of coins
    [ box 0 0 0 0.12 0.035 0.12 marble, cyl 0 0.03 0 0.04 0.03 gold, cyl 0.004 0.062 0.003 0.04 0.03 gold
    , cyl (-0.004) 0.094 (-0.002) 0.04 0.03 gold, cyl 0 0.126 0.003 0.04 0.03 gold ]
  | .harvest =>  -- a sheaf: an amber cone on a drum
    [ box 0 0 0 0.12 0.035 0.12 marble, cyl 0 0.03 0 0.035 0.08 stone, cone 0 0.11 0 0.045 0.15 0xD9A63C ]
  | .build =>  -- a mason's arch
    [ box 0 0 0 0.14 0.035 0.09 marble, box (-0.045) 0.03 0 0.03 0.16 0.04 plaster
    , box 0.045 0.03 0 0.03 0.16 0.04 plaster, box 0 0.19 0 0.14 0.035 0.05 stoneDark ]
  | .roundEnd =>  -- a bell in a frame
    [ box 0 0 0 0.12 0.035 0.12 marble, box (-0.05) 0.03 0 0.014 0.19 0.03 timberDark
    , box 0.05 0.03 0 0.014 0.19 0.03 timberDark, box 0 0.215 0 0.12 0.016 0.03 timberDark
    , cone 0 0.13 0 0.038 0.085 gold ]
  | .roll =>  -- two dice, one on the other, each with a gilded pip
    [ box 0 0 0 0.12 0.035 0.12 marble, box 0 0.03 0 0.09 0.09 0.09 plaster
    , box 0 0.12 0 0.065 0.065 0.065 plaster, box 0 0.185 0 0.018 0.008 0.018 gold
    , box 0 0.075 0.045 0.018 0.018 0.004 gold ]
  | .newPiece name =>  -- a small gilded model of the piece
    (box 0 0 0 0.14 0.035 0.14 marble) ::
      (lawPieceModel name 0).map fun p => { p with
        x := p.x * 0.55, y := 0.03 + p.y * 0.55, z := p.z * 0.55
        sx := p.sx * 0.55, sy := p.sy * 0.55, sz := p.sz * 0.55, rgb := gold }
  | .repeal =>  -- a broken column
    [ box 0 0 0 0.12 0.035 0.12 marble, cyl 0 0.03 0 0.027 0.1 stoneDark
    , { mesh := mCyl, x := 0.05, y := 0.03, z := 0.03, sx := 0.024, sy := 0.03, sz := 0.024, rgb := stoneDark } ]

end Charter.Scene
