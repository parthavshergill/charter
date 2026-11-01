import Codec

/-! The README Quickstart, compiled. -/

example (x : List (String × Option Int)) : Codec.decode (Codec.encode x) = some x :=
  Codec.decode_encode x

inductive Color | red | green | blue deriving Repr, DecidableEq

def Color.toFin : Color → Fin 3 | .red => 0 | .green => 1 | .blue => 2
def Color.ofFin : Fin 3 → Color | 0 => .red | 1 => .green | 2 => .blue

instance : Codec Color := Codec.ofEquiv Color.toFin Color.ofFin
instance : LawfulCodec Color :=
  Codec.ofEquiv_lawful Color.toFin Color.ofFin (by intro c; cases c <;> rfl)
instance : CanonicalCodec Color :=
  Codec.ofEquiv_canonical Color.toFin Color.ofFin (by decide)

#guard Codec.encode (300 : Nat) = [172, 2]
#guard (Codec.decode [2] : Option Color) == some .blue
#guard (Codec.decode [3] : Option Color) == none
