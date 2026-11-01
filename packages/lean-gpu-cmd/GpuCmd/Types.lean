/-!
# Scene command types

The wire stores every real number as the 32-bit pattern of an IEEE-754 binary32
value. `F32` keeps exactly those bits, so encoding and decoding are exact.
Conversion to and from `Float` happens only at the edges (`F32.ofFloat`,
`F32.toFloat`); `Float → F32` rounds to the nearest binary32 value.
-/

namespace GpuCmd

/-- An IEEE-754 binary32 value, stored as its bit pattern. -/
structure F32 where
  bits : UInt32
  deriving DecidableEq, BEq, Hashable, Inhabited

namespace F32

/-- Round a `Float` (binary64) to the nearest binary32 value. -/
def ofFloat (x : Float) : F32 := ⟨x.toFloat32.toBits⟩

/-- Widen to `Float` (exact). -/
def toFloat (f : F32) : Float := (Float32.ofBits f.bits).toFloat

instance : OfScientific F32 := ⟨fun m s e => ofFloat (OfScientific.ofScientific m s e)⟩
instance {n : Nat} : OfNat F32 n := ⟨ofFloat n.toFloat⟩
/-- Negation flips the sign bit (exact, also for zero and NaN). -/
instance : Neg F32 := ⟨fun f => ⟨f.bits ^^^ 0x80000000⟩⟩
instance : Coe Float F32 := ⟨ofFloat⟩
instance : Repr F32 := ⟨fun f _ => repr f.toFloat⟩
instance : ToString F32 := ⟨fun f => toString f.toFloat⟩

end F32

structure Vec3 where
  x : F32
  y : F32
  z : F32
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Build a `Vec3` from `Float`s. -/
def vec3 (x y z : Float) : Vec3 := ⟨x, y, z⟩

/-- Placement of a mesh instance: translate to `pos`, rotate `rotY` radians about
the +Y axis, then scale per axis (scale is applied first, in mesh space). -/
structure Transform where
  pos : Vec3
  rotY : F32 := 0
  scale : Vec3 := ⟨1, 1, 1⟩
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Transform at a position, no rotation, unit scale. -/
def Transform.at (x y z : Float) : Transform := { pos := vec3 x y z }

/-- Mesh primitives. Every primitive is centered on the Y axis and sits on the
plane y = 0 (it extends upward), so `pos.y = 0` puts it on the table. -/
inductive Prim
  /-- Hexagonal tile, pointy along ±Z (pointy-top in an (x, z) board layout). -/
  | hexPrism (radius height : F32)
  | box (w h d : F32)
  | cylinder (r h : F32)
  | cone (r h : F32)
  | sphere (r : F32)
  /-- Box body of height `0.6 h` with a pitched roof up to `h`; ridge along Z. -/
  | house (w h d : F32)
  /-- A roof with no walls: a triangular prism, full width at y = 0, ridge along Z at y = h. -/
  | gable (w h d : F32)
  /-- A four-sided pyramid, base corners at distance `r` on the X and Z axes, apex at y = h. -/
  | pyramid (r h : F32)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A small repeating motion of every instance of a mesh file. Zero is still.
`pulse` is the change in height as a fraction, `sway` is the tilt in radians, and `glow` is
the added light from 0 to 1. The player runs it. The stream does not change over time. -/
structure Motion where
  pulse : F32 := 0
  sway : F32 := 0
  glow : F32 := 0
  deriving DecidableEq, BEq, Repr, Inhabited

/-- One scene command. Colors are `0xTTRRGGBB`: `TT` is transparency
(`0x00` opaque, `0xFF` invisible); plain `0xRRGGBB` is opaque. -/
inductive Cmd
  | clear (rgb : UInt32)
  | camera (eye target : Vec3) (fovDeg : F32)
  | light (dir : Vec3) (intensity : F32)
  | defineMesh (id : UInt32) (p : Prim)
  /-- `pick = 0` means not pickable. -/
  | draw (mesh : UInt32) (t : Transform) (rgb : UInt32) (pick : UInt32)
  | label (text : String) (pos : Vec3) (size : F32) (rgb : UInt32) (pick : UInt32)
  /-- Outline / glow every object (mesh or label) with this pick id. -/
  | highlight (pick : UInt32) (rgb : UInt32)
  /-- Bind a mesh id to a triangle mesh file, named by the lower-case hex of its SHA-256. The
  player draws `standIn` in the color `tint` until the file loads, and for good if it cannot. -/
  | defineMeshFile (id : UInt32) (sha256 : String) (tint : UInt32) (motion : Motion) (standIn : Prim)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Color with a transparency byte: `alpha = 1` opaque, `alpha = 0` invisible. -/
def withAlpha (rgb : UInt32) (alpha : Float) : UInt32 :=
  let a := if alpha ≤ 0 then 0 else if alpha ≥ 1 then 255 else (alpha * 255).round.toUInt32
  ((255 - a) <<< 24) ||| (rgb &&& 0xFFFFFF)

end GpuCmd
