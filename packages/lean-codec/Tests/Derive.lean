import Codec

/-! `deriving Codec` tests. -/

namespace Codec.DeriveTests

inductive Resource | grain | timber | ore | wool | brick
  deriving Codec, Repr, DecidableEq

structure Point where
  x : Int
  y : Int
  deriving Codec, Repr, DecidableEq

structure Empty' where
  deriving Codec, Repr, DecidableEq

structure One where
  n : Nat
  deriving Codec, Repr, DecidableEq

inductive Shape
  | dot
  | circle (center : Point) (r : Nat)
  | poly (pts : List Point) (label : Option String)
  | tagged (res : Resource)
  | pair (a : Fin 19) (b : UInt64) (c : Bool)
  deriving Codec, Repr, DecidableEq

example : LawfulCodec Resource := inferInstance
example : CanonicalCodec Resource := inferInstance
example : LawfulCodec Point := inferInstance
example : CanonicalCodec Point := inferInstance
example : CanonicalCodec Empty' := inferInstance
example : CanonicalCodec One := inferInstance
example : LawfulCodec Shape := inferInstance
example : CanonicalCodec Shape := inferInstance
example (s : List Shape) : Codec.decode (Codec.encode s) = some s := Codec.decode_encode s

#guard Codec.encode Resource.brick = [4]
#guard (Codec.decode [5] : Option Resource) = none
#guard Codec.encode (Point.mk 1 (-1)) = [2, 1]
#guard Codec.encode (Empty'.mk) = []
#guard Codec.encode (One.mk 300) = [0xAC, 0x02]
#guard (Codec.decode (Codec.encode (Shape.poly [⟨0, 5⟩, ⟨-2, 3⟩] (some "tri"))) : Option Shape)
  = some (Shape.poly [⟨0, 5⟩, ⟨-2, 3⟩] (some "tri"))
#guard [Shape.dot, .circle ⟨1, 2⟩ 3, .poly [] none, .tagged .ore, .pair 18 7 true].all fun s =>
  (Codec.decode (Codec.encode s) : Option Shape) == some s
-- 5 constructors: tag is at most 3 bytes
#guard (Codec.encode (Shape.pair 18 7 true)).take 4 = [1, 1, 1, 18]

end Codec.DeriveTests

-- Derived instances are ordinary kernel-checked proofs.
#print axioms Codec.DeriveTests.instLawfulCodecShape
#print axioms Codec.DeriveTests.instCanonicalCodecShape
#print axioms Codec.DeriveTests.instLawfulCodecResource
#print axioms Codec.DeriveTests.instCanonicalCodecResource
