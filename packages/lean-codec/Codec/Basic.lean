/-!
# Codec: core classes

A `Codec α` turns values into bytes (`encode`) and reads a value back off the
front of a byte list (`decodeFrom`), returning the unconsumed suffix.

* `LawfulCodec α` : decoding an encoding returns the value and leaves any
  trailing bytes untouched (`decode_encode`).
* `CanonicalCodec α` : every successful decode consumed *exactly* the
  encoding of the value it returned (`encode_decode`). Together with
  `LawfulCodec` this makes `encode` a bijection between values and accepted
  byte strings, so equal values have equal bytes and vice versa — the property
  you want before hashing an encoding.
-/

class Codec (α : Type) where
  encode : α → List UInt8
  decodeFrom : List UInt8 → Option (α × List UInt8)

class LawfulCodec (α : Type) [Codec α] : Prop where
  decode_encode : ∀ (a : α) (rest : List UInt8),
    Codec.decodeFrom (Codec.encode a ++ rest) = some (a, rest)

class CanonicalCodec (α : Type) [Codec α] : Prop where
  encode_decode : ∀ (bs : List UInt8) (a : α) (rest : List UInt8),
    Codec.decodeFrom bs = some (a, rest) → bs = Codec.encode a ++ rest

namespace Codec

variable {α : Type} [Codec α]

/-- Decode the whole input; fails if any bytes are left over. -/
def decode (bs : List UInt8) : Option α :=
  match decodeFrom (α := α) bs with
  | some (a, []) => some a
  | _ => none

/-- Encode into a `ByteArray`. -/
def encodeBytes (a : α) : ByteArray := ⟨(encode a).toArray⟩

/-- Decode a whole `ByteArray`; fails if any bytes are left over. -/
def decodeBytes (b : ByteArray) : Option α := decode b.data.toList

theorem decodeFrom_encode [LawfulCodec α] (a : α) (rest : List UInt8) :
    decodeFrom (encode a ++ rest) = some (a, rest) :=
  LawfulCodec.decode_encode a rest

theorem decodeFrom_encode_nil [LawfulCodec α] (a : α) :
    decodeFrom (encode a) = some (a, []) := by
  simpa using LawfulCodec.decode_encode a []

/-- Whole-input round trip. -/
theorem decode_encode [LawfulCodec α] (a : α) : decode (encode a) = some a := by
  simp [decode, decodeFrom_encode_nil]

/-- `ByteArray` round trip. -/
theorem decodeBytes_encodeBytes [LawfulCodec α] (a : α) :
    decodeBytes (encodeBytes a) = some a := by
  simp [decodeBytes, encodeBytes, decode_encode]

/-- Canonicity for whole-input decoding. -/
theorem encode_decode [CanonicalCodec α] {bs : List UInt8} {a : α}
    (h : decode bs = some a) : bs = encode a := by
  unfold decode at h
  split at h
  · rename_i h'
    cases h
    simpa using CanonicalCodec.encode_decode _ _ _ h'
  · cases h

/-- Encoding is injective for lawful codecs. -/
theorem encode_injective [LawfulCodec α] {a b : α} (h : encode a = encode b) : a = b := by
  have h1 := decode_encode a
  rw [h, decode_encode] at h1
  exact (Option.some.inj h1).symm

/-- `decodeBytes` canonicity: accepted byte arrays are exactly encodings. -/
theorem encodeBytes_decodeBytes [CanonicalCodec α] {b : ByteArray} {a : α}
    (h : decodeBytes b = some a) : b = encodeBytes a := by
  have := encode_decode h
  cases b with
  | mk d => simp [encodeBytes, ← this]

end Codec
