import GpuCmd.Types

/-!
# Byte-level wire primitives

Little-endian fixed-width integers, ULEB128 lengths, and UTF-8 strings over
`List UInt8`. Each writer has a reader and a lemma
`read (write x ++ rest) = some (x, rest)`.
-/

namespace GpuCmd.Wire

/-- The low `k` bytes of `n`, least significant first. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => (n % 256).toUInt8 :: leBytes k (n / 256)

/-- Read `k` little-endian bytes as a `Nat`. -/
def readLE : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | k + 1, b :: bs => (readLE k bs).map fun (m, r) => (b.toNat + 256 * m, r)

theorem readLE_leBytes (k n : Nat) (rest : List UInt8) :
    readLE k (leBytes k n ++ rest) = some (n % 256 ^ k, rest) := by
  induction k generalizing n with
  | zero => simp [readLE, leBytes, Nat.mod_one]
  | succ k ih =>
    simp only [leBytes, List.cons_append, readLE, ih, Option.map_some]
    have h : (n % 256).toUInt8.toNat = n % 256 := by
      simp [Nat.toUInt8]
    rw [h, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

theorem leBytes_length (k n : Nat) : (leBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

/-! ## Fixed-width words -/

def u8 (b : UInt8) : List UInt8 := [b]

def readU8 : List UInt8 → Option (UInt8 × List UInt8)
  | [] => none
  | b :: bs => some (b, bs)

theorem readU8_u8 (b : UInt8) (rest : List UInt8) : readU8 (u8 b ++ rest) = some (b, rest) := rfl

def u32 (x : UInt32) : List UInt8 := leBytes 4 x.toNat

def readU32 (bs : List UInt8) : Option (UInt32 × List UInt8) :=
  (readLE 4 bs).map fun (n, r) => (n.toUInt32, r)

theorem readU32_u32 (x : UInt32) (rest : List UInt8) :
    readU32 (u32 x ++ rest) = some (x, rest) := by
  simp only [readU32, u32, readLE_leBytes, Option.map_some]
  have hlt : x.toNat < 256 ^ 4 := x.toNat_lt
  rw [Nat.mod_eq_of_lt hlt]
  simp

/-- An `F32` on the wire is its binary32 bit pattern, little endian. -/
def f32 (f : F32) : List UInt8 := u32 f.bits

def readF32 (bs : List UInt8) : Option (F32 × List UInt8) :=
  (readU32 bs).map fun (x, r) => (⟨x⟩, r)

theorem readF32_f32 (f : F32) (rest : List UInt8) :
    readF32 (f32 f ++ rest) = some (f, rest) := by
  simp [readF32, f32, readU32_u32]

/-! ## ULEB128 (used for string lengths) -/

def uleb (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (n % 128 + 128).toUInt8 :: uleb (n / 128)
termination_by n
decreasing_by omega

def readUleb : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else (readUleb bs).map fun (m, r) => (b.toNat - 128 + 128 * m, r)

theorem readUleb_uleb (n : Nat) (rest : List UInt8) :
    readUleb (uleb n ++ rest) = some (n, rest) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [uleb]
    split
    · rename_i h
      have : n.toUInt8.toNat = n := by
        simp [Nat.toUInt8]; omega
      simp [readUleb, this, h]
    · rename_i h
      have hb : (n % 128 + 128).toUInt8.toNat = n % 128 + 128 := by
        simp [Nat.toUInt8]; omega
      have ih' := ih (n / 128) (by omega)
      have hn : ¬ (n % 128 + 128 < 128) := by omega
      simp only [List.cons_append, readUleb, hb, ih', Option.map_some, hn, ↓reduceIte]
      congr 2
      omega

/-! ## Strings: ULEB128 byte length, then UTF-8 bytes -/

def str (s : String) : List UInt8 :=
  let b := s.toUTF8.data.toList
  uleb b.length ++ b

def readStr (bs : List UInt8) : Option (String × List UInt8) := do
  let (n, r) ← readUleb bs
  if n ≤ r.length then
    let s ← String.fromUTF8? ⟨(r.take n).toArray⟩
    pure (s, r.drop n)
  else none

theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

theorem readStr_str (s : String) (rest : List UInt8) :
    readStr (str s ++ rest) = some (s, rest) := by
  simp only [readStr, str, List.append_assoc, readUleb_uleb]
  have : (⟨s.toByteArray.data.toList.toArray⟩ : ByteArray) = s.toByteArray := by simp
  simp [this, fromUTF8?_toByteArray]

end GpuCmd.Wire
