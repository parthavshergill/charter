import Codec.Basic

/-!
# `Nat` as unsigned LEB128

Seven value bits per byte, least significant group first; the high bit of a
byte is set iff more bytes follow. The decoder rejects over-long encodings
(a continuation byte followed by a group that encodes zero), so the codec is
canonical: every natural number has exactly one accepted byte string.
-/

namespace Codec

/-- Unsigned LEB128 encoding. -/
def encodeNat (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 128 + 128) :: encodeNat (n / 128)
termination_by n
decreasing_by omega

/-- Unsigned LEB128 decoding (structural recursion on the input). Rejects
non-minimal encodings. -/
def decodeNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: r =>
    if b.toNat < 128 then some (b.toNat, r)
    else
      match decodeNat r with
      | some (m, r') => if m = 0 then none else some (b.toNat - 128 + 128 * m, r')
      | none => none

theorem decodeNat_encodeNat (n : Nat) (rest : List UInt8) :
    decodeNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [encodeNat]
    by_cases h : n < 128
    · have h1 : (UInt8.ofNat n).toNat = n := by simp only [UInt8.toNat_ofNat']; omega
      simp [h, decodeNat, h1]
    · have h1 : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by
        simp only [UInt8.toNat_ofNat']; omega
      have h2 : ¬ (n % 128 + 128 < 128) := by omega
      have h3 : ¬ (n / 128 = 0) := by omega
      have h4 : n % 128 + 128 - 128 + 128 * (n / 128) = n := by omega
      simp only [h, ite_false, List.cons_append, decodeNat, h1, h2, ih (n / 128) (by omega), h3, h4]

theorem encodeNat_decodeNat {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : decodeNat bs = some (n, rest)) : bs = encodeNat n ++ rest := by
  induction bs generalizing n rest with
  | nil => simp [decodeNat] at h
  | cons b r ih =>
    simp only [decodeNat] at h
    have hb := b.toNat_lt
    by_cases hlt : b.toNat < 128
    · simp only [hlt, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [encodeNat]
      simp [hlt, UInt8.ofNat_toNat]
    · simp only [hlt, ite_false] at h
      split at h
      · rename_i m r' hm
        by_cases hm0 : m = 0
        · simp [hm0] at h
        · simp only [hm0, ite_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have e1 : ¬ (b.toNat - 128 + 128 * m < 128) := by omega
          have e2 : (b.toNat - 128 + 128 * m) / 128 = m := by omega
          have e3 : UInt8.ofNat ((b.toNat - 128 + 128 * m) % 128 + 128) = b := by
            apply UInt8.toNat_inj.mp
            simp only [UInt8.toNat_ofNat']
            omega
          rw [ih hm, encodeNat.eq_1 (b.toNat - 128 + 128 * m)]
          simp only [e1, ite_false, e2, e3, List.cons_append]
      · cases h

instance codecNat : Codec Nat where
  encode := encodeNat
  decodeFrom := decodeNat

instance lawfulNat : LawfulCodec Nat where
  decode_encode := decodeNat_encodeNat

instance canonicalNat : CanonicalCodec Nat where
  encode_decode _ _ _ h := encodeNat_decodeNat h

end Codec
