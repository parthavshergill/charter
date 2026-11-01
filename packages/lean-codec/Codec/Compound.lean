import Codec.Fixed
import Codec.Nat
import Codec.OfEquiv

/-!
# Compound codecs

* `α × β`     : `encode a ++ encode b`
* `Sum α β`   : tag byte `0`/`1`, then the payload
* `Option α`  : tag byte `0` (none) / `1` (some), then the payload
* `List α`    : LEB128 element count, then the elements
* `Array α`   : as `List α`
* `Int`       : zigzag (`0,-1,1,-2,… ↦ 0,1,2,3,…`) then LEB128
* `Fin n`     : LEB128 of the value; decoding rejects values `≥ n`
* `String`    : LEB128 byte count, then the UTF-8 bytes; invalid UTF-8 is rejected
-/

namespace Codec

variable {α β : Type}

/-! ### Product -/

instance codecProd [Codec α] [Codec β] : Codec (α × β) where
  encode p := encode p.1 ++ encode p.2
  decodeFrom bs :=
    match decodeFrom (α := α) bs with
    | some (a, r) =>
      match decodeFrom (α := β) r with
      | some (b, r') => some ((a, b), r')
      | none => none
    | none => none

instance lawfulProd [Codec α] [Codec β] [LawfulCodec α] [LawfulCodec β] : LawfulCodec (α × β) where
  decode_encode p rest := by
    simp only [Codec.encode, Codec.decodeFrom, List.append_assoc]
    rw [decodeFrom_encode]
    simp only
    rw [decodeFrom_encode]

instance canonicalProd [Codec α] [Codec β] [CanonicalCodec α] [CanonicalCodec β] :
    CanonicalCodec (α × β) where
  encode_decode bs p rest h := by
    simp only [Codec.decodeFrom] at h
    split at h
    · rename_i a r ha
      split at h
      · rename_i b r' hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [CanonicalCodec.encode_decode _ _ _ ha, CanonicalCodec.encode_decode _ _ _ hb]
        simp [Codec.encode]
      · cases h
    · cases h

/-! ### Sum -/

instance codecSum [Codec α] [Codec β] : Codec (Sum α β) where
  encode
    | .inl a => 0 :: encode a
    | .inr b => 1 :: encode b
  decodeFrom
    | 0 :: r =>
      match decodeFrom (α := α) r with
      | some (a, r') => some (.inl a, r')
      | none => none
    | 1 :: r =>
      match decodeFrom (α := β) r with
      | some (b, r') => some (.inr b, r')
      | none => none
    | _ => none

instance lawfulSum [Codec α] [Codec β] [LawfulCodec α] [LawfulCodec β] : LawfulCodec (Sum α β) where
  decode_encode s rest := by
    cases s <;> simp [Codec.encode, Codec.decodeFrom, decodeFrom_encode]

instance canonicalSum [Codec α] [Codec β] [CanonicalCodec α] [CanonicalCodec β] :
    CanonicalCodec (Sum α β) where
  encode_decode bs s rest h := by
    simp only [Codec.decodeFrom] at h
    split at h
    · split at h
      · rename_i a r' ha; cases h
        rw [CanonicalCodec.encode_decode _ _ _ ha]; simp [Codec.encode]
      · cases h
    · split at h
      · rename_i b r' hb; cases h
        rw [CanonicalCodec.encode_decode _ _ _ hb]; simp [Codec.encode]
      · cases h
    · cases h

/-! ### Option -/

instance codecOption [Codec α] : Codec (Option α) where
  encode
    | none => [0]
    | some a => 1 :: encode a
  decodeFrom
    | 0 :: r => some (none, r)
    | 1 :: r =>
      match decodeFrom (α := α) r with
      | some (a, r') => some (some a, r')
      | none => none
    | _ => none

instance lawfulOption [Codec α] [LawfulCodec α] : LawfulCodec (Option α) where
  decode_encode o rest := by
    cases o <;> simp [Codec.encode, Codec.decodeFrom, decodeFrom_encode]

instance canonicalOption [Codec α] [CanonicalCodec α] : CanonicalCodec (Option α) where
  encode_decode bs o rest h := by
    simp only [Codec.decodeFrom] at h
    split at h
    · cases h; simp [Codec.encode]
    · split at h
      · rename_i a r' ha; cases h
        rw [CanonicalCodec.encode_decode _ _ _ ha]; simp [Codec.encode]
      · cases h
    · cases h

/-! ### List -/

/-- Decode exactly `k` consecutive values. -/
def decodeMany [Codec α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    match decodeFrom (α := α) bs with
    | some (a, r) =>
      match decodeMany k r with
      | some (as, r') => some (a :: as, r')
      | none => none
    | none => none

theorem decodeMany_encode [Codec α] [LawfulCodec α] (xs : List α) (rest : List UInt8) :
    decodeMany xs.length (xs.flatMap encode ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeMany,
      decodeFrom_encode, ih]

theorem decodeMany_canonical [Codec α] [CanonicalCodec α] {k : Nat} {bs : List UInt8}
    {xs : List α} {rest : List UInt8} (h : decodeMany k bs = some (xs, rest)) :
    xs.length = k ∧ bs = xs.flatMap encode ++ rest := by
  induction k generalizing bs xs rest with
  | zero => simp [decodeMany] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | succ k ih =>
    simp only [decodeMany] at h
    split at h
    · rename_i a r ha
      split at h
      · rename_i as r' has
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, rfl⟩ := ih has
        rw [CanonicalCodec.encode_decode _ _ _ ha]
        simp [hl]
      · cases h
    · cases h

instance codecList [Codec α] : Codec (List α) where
  encode xs := encodeNat xs.length ++ xs.flatMap encode
  decodeFrom bs :=
    match decodeNat bs with
    | some (k, r) => decodeMany k r
    | none => none

instance lawfulList [Codec α] [LawfulCodec α] : LawfulCodec (List α) where
  decode_encode xs rest := by
    simp only [Codec.encode, Codec.decodeFrom, List.append_assoc, decodeNat_encodeNat,
      decodeMany_encode]

instance canonicalList [Codec α] [CanonicalCodec α] : CanonicalCodec (List α) where
  encode_decode bs xs rest h := by
    simp only [Codec.decodeFrom] at h
    split at h
    · rename_i k r hk
      obtain ⟨hl, rfl⟩ := decodeMany_canonical h
      rw [encodeNat_decodeNat hk, ← hl]
      simp [Codec.encode]
    · cases h

/-! ### Array (as List) -/

instance codecArray [Codec α] : Codec (Array α) := ofEquiv Array.toList List.toArray

instance lawfulArray [Codec α] [LawfulCodec α] : LawfulCodec (Array α) :=
  ofEquiv_lawful Array.toList List.toArray (fun a => by simp)

instance canonicalArray [Codec α] [CanonicalCodec α] : CanonicalCodec (Array α) :=
  ofEquiv_canonical Array.toList List.toArray (fun l => by simp)

/-! ### Int (zigzag, then LEB128) -/

/-- Zigzag: `ofNat n ↦ 2n`, `negSucc n ↦ 2n+1`. -/
def zigzag : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def unzigzag (m : Nat) : Int :=
  if m % 2 = 0 then .ofNat (m / 2) else .negSucc (m / 2)

theorem unzigzag_zigzag (i : Int) : unzigzag (zigzag i) = i := by
  cases i with
  | ofNat n =>
    have h1 : 2 * n % 2 = 0 := by omega
    have h2 : 2 * n / 2 = n := by omega
    simp only [zigzag, unzigzag, h1, h2, ite_true]
  | negSucc n =>
    have h1 : ¬ (2 * n + 1) % 2 = 0 := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp only [zigzag, unzigzag, h1, h2, ite_false]

theorem zigzag_unzigzag (m : Nat) : zigzag (unzigzag m) = m := by
  unfold unzigzag
  split <;> simp only [zigzag] <;> omega

instance codecInt : Codec Int := ofEquiv zigzag unzigzag
instance lawfulInt : LawfulCodec Int := ofEquiv_lawful zigzag unzigzag unzigzag_zigzag
instance canonicalInt : CanonicalCodec Int := ofEquiv_canonical zigzag unzigzag zigzag_unzigzag

/-! ### Fin n -/

def finOfNat? (n m : Nat) : Option (Fin n) := if h : m < n then some ⟨m, h⟩ else none

instance codecFin {n : Nat} : Codec (Fin n) := ofPartial Fin.val (finOfNat? n)

instance lawfulFin {n : Nat} : LawfulCodec (Fin n) :=
  ofPartial_lawful Fin.val (finOfNat? n) (fun a => by simp [finOfNat?, a.isLt])

instance canonicalFin {n : Nat} : CanonicalCodec (Fin n) :=
  ofPartial_canonical Fin.val (finOfNat? n) (fun a b h => by
    unfold finOfNat? at h
    split at h
    · cases h; rfl
    · cases h)

/-! ### String (UTF-8 bytes, length-prefixed) -/

/-- The UTF-8 bytes of a string. -/
def stringBytes (s : String) : List UInt8 := s.toByteArray.data.toList

/-- Strings from UTF-8 bytes; `none` on invalid UTF-8. -/
def stringOfBytes? (l : List UInt8) : Option String := String.fromUTF8? ⟨l.toArray⟩

theorem stringOfBytes?_stringBytes (s : String) : stringOfBytes? (stringBytes s) = some s := by
  have : (⟨s.toByteArray.data.toList.toArray⟩ : ByteArray) = s.toByteArray := by simp
  simp only [stringOfBytes?, stringBytes, this, String.fromUTF8?, s.isValidUTF8, dite_true]
  rfl

theorem stringBytes_of_stringOfBytes? {l : List UInt8} {s : String}
    (h : stringOfBytes? l = some s) : stringBytes s = l := by
  unfold stringOfBytes? String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

instance codecString : Codec String := ofPartial stringBytes stringOfBytes?

instance lawfulString : LawfulCodec String :=
  ofPartial_lawful stringBytes stringOfBytes? stringOfBytes?_stringBytes

instance canonicalString : CanonicalCodec String :=
  ofPartial_canonical stringBytes stringOfBytes? (fun _ _ h => stringBytes_of_stringOfBytes? h)

end Codec
