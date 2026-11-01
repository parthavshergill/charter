import Codec.Basic

/-!
# Fixed-width codecs: `Unit`, `Bool`, `UInt8`, `UInt16`, `UInt32`, `UInt64`

Multi-byte integers are little endian. All instances here are lawful and
canonical.
-/

namespace Codec

/-- `k` little-endian bytes of `n` (high bits beyond `256^k` are dropped). -/
def encodeFixed : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: encodeFixed k (n / 256)

/-- Read `k` little-endian bytes. -/
def decodeFixed : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs =>
    match decodeFixed k bs with
    | some (m, r) => some (b.toNat + 256 * m, r)
    | none => none

theorem length_encodeFixed (k n : Nat) : (encodeFixed k n).length = k := by
  induction k generalizing n <;> simp_all [encodeFixed]

theorem decodeFixed_encodeFixed (k n : Nat) (h : n < 256 ^ k) (rest : List UInt8) :
    decodeFixed k (encodeFixed k n ++ rest) = some (n, rest) := by
  induction k generalizing n with
  | zero => simp_all [encodeFixed, decodeFixed]
  | succ k ih =>
    have h' : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    simp only [encodeFixed, List.cons_append, decodeFixed, ih _ h', Option.some.injEq,
      Prod.mk.injEq, and_true]
    simp only [UInt8.toNat_ofNat']
    omega

theorem decodeFixed_lt {k : Nat} {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : decodeFixed k bs = some (n, rest)) : n < 256 ^ k ∧ bs = encodeFixed k n ++ rest := by
  induction k generalizing bs n rest with
  | zero => simp [decodeFixed] at h; obtain ⟨rfl, rfl⟩ := h; simp [encodeFixed]
  | succ k ih =>
    match bs, h with
    | [], h => simp [decodeFixed] at h
    | b :: bs, h =>
      simp only [decodeFixed] at h
      split at h
      · rename_i m r hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlt, rfl⟩ := ih hm
        have hb := b.toNat_lt
        refine ⟨by rw [Nat.pow_succ]; omega, ?_⟩
        simp only [encodeFixed, List.cons_append, List.cons.injEq]
        constructor
        · apply UInt8.toNat_inj.mp
          simp only [UInt8.toNat_ofNat']
          omega
        · congr 2; omega
      · simp at h

/-! ### Unit -/

instance codecUnit : Codec Unit where
  encode _ := []
  decodeFrom bs := some ((), bs)

instance lawfulUnit : LawfulCodec Unit where
  decode_encode _ _ := rfl

instance canonicalUnit : CanonicalCodec Unit where
  encode_decode bs a rest h := by
    simp [Codec.decodeFrom] at h; simp [h, Codec.encode]

/-! ### Bool -/

instance codecBool : Codec Bool where
  encode b := [if b then 1 else 0]
  decodeFrom
    | 0 :: r => some (false, r)
    | 1 :: r => some (true, r)
    | _ => none

instance lawfulBool : LawfulCodec Bool where
  decode_encode b _ := by cases b <;> rfl

instance canonicalBool : CanonicalCodec Bool where
  encode_decode bs a rest h := by
    simp only [Codec.decodeFrom] at h
    split at h <;> simp_all [Codec.encode]

/-! ### UInt8 -/

instance codecUInt8 : Codec UInt8 where
  encode b := [b]
  decodeFrom
    | b :: r => some (b, r)
    | [] => none

instance lawfulUInt8 : LawfulCodec UInt8 where
  decode_encode _ _ := rfl

instance canonicalUInt8 : CanonicalCodec UInt8 where
  encode_decode bs a rest h := by
    simp only [Codec.decodeFrom] at h
    split at h <;> simp_all [Codec.encode]

/-! ### UInt16 / UInt32 / UInt64 (little endian) -/

instance codecUInt16 : Codec UInt16 where
  encode x := encodeFixed 2 x.toNat
  decodeFrom bs := (decodeFixed 2 bs).map fun (n, r) => (UInt16.ofNat n, r)

instance lawfulUInt16 : LawfulCodec UInt16 where
  decode_encode x rest := by
    simp [Codec.encode, Codec.decodeFrom, decodeFixed_encodeFixed 2 x.toNat x.toNat_lt]

instance canonicalUInt16 : CanonicalCodec UInt16 where
  encode_decode bs a rest h := by
    simp only [Codec.decodeFrom, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨n, r⟩, hd, rfl, rfl⟩ := h
    obtain ⟨hlt, rfl⟩ := decodeFixed_lt hd
    simp only [Codec.encode]
    rw [UInt16.toNat_ofNat_of_lt' (by simpa [UInt16.size] using hlt)]

instance codecUInt32 : Codec UInt32 where
  encode x := encodeFixed 4 x.toNat
  decodeFrom bs := (decodeFixed 4 bs).map fun (n, r) => (UInt32.ofNat n, r)

instance lawfulUInt32 : LawfulCodec UInt32 where
  decode_encode x rest := by
    simp [Codec.encode, Codec.decodeFrom, decodeFixed_encodeFixed 4 x.toNat x.toNat_lt]

instance canonicalUInt32 : CanonicalCodec UInt32 where
  encode_decode bs a rest h := by
    simp only [Codec.decodeFrom, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨n, r⟩, hd, rfl, rfl⟩ := h
    obtain ⟨hlt, rfl⟩ := decodeFixed_lt hd
    simp only [Codec.encode]
    rw [UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hlt)]

instance codecUInt64 : Codec UInt64 where
  encode x := encodeFixed 8 x.toNat
  decodeFrom bs := (decodeFixed 8 bs).map fun (n, r) => (UInt64.ofNat n, r)

instance lawfulUInt64 : LawfulCodec UInt64 where
  decode_encode x rest := by
    simp [Codec.encode, Codec.decodeFrom, decodeFixed_encodeFixed 8 x.toNat x.toNat_lt]

instance canonicalUInt64 : CanonicalCodec UInt64 where
  encode_decode bs a rest h := by
    simp only [Codec.decodeFrom, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨n, r⟩, hd, rfl, rfl⟩ := h
    obtain ⟨hlt, rfl⟩ := decodeFixed_lt hd
    simp only [Codec.encode]
    rw [UInt64.toNat_ofNat_of_lt' (by simpa [UInt64.size] using hlt)]

end Codec
