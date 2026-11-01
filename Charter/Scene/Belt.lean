import Charter.Scene.Render

/-!
# The look of the Belt

Rocks and ice in the dark, with domes for outposts and rings for stations.
-/

namespace Charter.Scene.BeltLook
open GpuCmd HexGrid
open Charter.Games (TileDef)

def ground : Option Res → UInt32
  | some "helium" => 0x5A4A78
  | some "alloy" => 0x5F6670
  | some "ice" => 0x9CC4D8
  | some "crystal" => 0x7A3E6E
  | _ => 0x3A3A44

/-- Small things on a hex. Each resource has its own shape, so colour is not the only cue. -/
def decor (res : Option Res) (seed : Nat) (keep : Float → Float → Bool) (_cut : Nat) : List Part :=
  let at_ (n : Nat) (f : Float → Float → Nat → List Part) : List Part :=
    ((scatter seed n 0.36 0.72).filter fun (x, z, _) => keep x z && !hidesToken x z).flatMap fun (x, z, i) => f x z i
  match res with
  | some "helium" => at_ 6 fun x z i =>
      [lump x 0.02 z (0.14 + 0.08 * rnd seed i) 0.07 (0.12 + 0.06 * rnd seed (i + 3)) 0xB7A6E0]
  | some "alloy" => at_ 6 fun x z i =>
      [box x 0 z 0.05 (0.08 + 0.14 * rnd seed i) 0.05 (pickFrom [0xA8B0BC, 0x8C95A3] seed i) (6.28 * rnd seed (i + 2))]
  | some "ice" => at_ 6 fun x z i =>
      [cone x 0 z (0.05 + 0.03 * rnd seed i) (0.12 + 0.12 * rnd seed (i + 5)) 0xE8F6FF]
  | some "crystal" => at_ 5 fun x z i =>
      [pyr x 0 z (0.06 + 0.03 * rnd seed i) (0.16 + 0.12 * rnd seed (i + 6)) 0xD65FB8 (6.28 * rnd seed i)]
  | _ => []

/-- An outpost: a dome on a pad, with a mast. The pad has the owner's colour. -/
def outpost (seed seat _round : Nat) : List Part :=
  let c := seatColor seat
  [ cyl 0 0 0 0.19 0.03 c, ball 0 0.03 0 0.24 0xDCE6EE
  , box 0.11 0.03 (0.02 * rnd seed 1) 0.012 0.2 0.012 ink, ball 0.11 0.23 0 0.04 c ]

/-- A station: a wide ring around a tall core, in the owner's colour. -/
def station (_seed seat _round : Nat) : List Part :=
  let c := seatColor seat
  [ cyl 0 0 0 0.3 0.03 stoneDark, cyl 0 0.03 0 0.09 0.3 stone, cyl 0 0.33 0 0.11 0.03 c
  , cyl 0 0.16 0 0.27 0.035 c, cyl 0 0.165 0 0.22 0.03 0x20242C, ball 0 0.36 0 0.1 0xDCE6EE ]

/-- A lane: a line of light on a dark rail. Marks differ by seat, so colour is not the only cue. -/
def lane (seat : Nat) : List Part :=
  let marks : List Float := match seat % 4 with
    | 0 => []
    | 1 => [0]
    | 2 => [-0.1, 0.1]
    | _ => [-0.2, 0, 0.2]
  [box 0 0 0 0.76 0.016 0.08 0x20242C, box 0 0.016 0 0.72 0.016 0.05 (seatColor seat)] ++
  marks.map fun u => box u 0.03 0 0.03 0.006 0.06 0xF4F8FF

/-- Stars around the map, in fixed places. -/
def stars : List Cmd :=
  let dots := (List.range 90).map fun i =>
    let a := 2.399963 * i.toFloat
    let r := 4.4 + 1.8 * rnd 91 i
    (ball (r * Float.cos a) (0.02 + 0.5 * rnd 92 i) (r * Float.sin a) (0.018 + 0.03 * rnd 93 i) 0xE8EEFF).at 0 0 0
  [(hexp 0 0 0 5.9 0.02 0x12141C (pi / 6.0)).at 0 0 0] ++ dots

/-- Dark rock under the tiles. -/
def rock (tiles : List TileDef) : List Cmd :=
  tiles.map fun t =>
    let (x, z) := t.hex.toPixel 1.0
    .draw mLand { pos := vec3 x 0.02 z, scale := vec3 1.08 0.12 1.08 } 0x262830 0

def theme : Theme :=
  { tableColor := 0x0A0B12
    ground := ground
    decor := decor
    growth := fun _ _ _ _ _ => []
    surround := stars
    under := rock
    shape := fun k =>
      if k == "outpost" then some .settlement else if k == "station" then some .city else none
    smallModel := outpost
    largeModel := station
    linkModel := fun k seat => if k == "lane" then lane seat else wallParts seat
    harbours := false
    flat := fun
      | some "helium" => 0x8E7CC3
      | some "alloy" => 0x8C95A3
      | some "ice" => 0x9CC4D8
      | some "crystal" => 0xB05A9C
      | _ => 0xF0D9A0
    look :=
      { tagline := "Mine the belt. Rewrite its rules. The constitution holds."
        marks :=
          [ ("helium", "helium"), ("alloy", "alloy"), ("ice", "ice"), ("crystal", "crystal")
          , ("lane", "road"), ("outpost", "settlement"), ("station", "city"), ("dock", "made") ] } }

end Charter.Scene.BeltLook
