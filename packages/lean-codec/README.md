# lean-codec

Turn Lean values into canonical byte strings and back, with kernel-checked proofs that decoding inverts encoding and that every accepted byte string is the encoding of exactly one value.

## Non-goals

- Not a self-describing format (no schema, field names, or versioning on the wire). Both sides must agree on the type.
- Not optimized for throughput. Proofs are over `List UInt8`; `encodeBytes`/`decodeBytes` convert at the edge. Fine for messages of a few KB.
- No streaming or partial-input resumption.
- No protection against resource exhaustion from hostile length prefixes for types whose encoding is empty (`List Unit` with a count of 2^60 decodes by building that list). Every other element type fails fast when the input runs out.
- `deriving Codec` covers only non-parametric, non-recursive types with non-dependent fields. For anything else, use `Codec.ofEquiv` / `Codec.ofPartial` or write the instance by hand.
- The `deriving Codec` handler (meta code) is not itself verified. It does not need to be: every instance it emits is an ordinary proof term that the kernel checks.
- No dependencies: no Mathlib, no Batteries.

## Guarantees

All proved in Lean 4 (`leanprover/lean4:v4.35.0`) without `sorry`, `native_decide`, or new axioms. `Codec/Audit.lean` runs `#print axioms` on each.

Classes (`Codec/Basic.lean`):

```lean
class Codec (α : Type) where
  encode : α → List UInt8
  decodeFrom : List UInt8 → Option (α × List UInt8)   -- consumes a prefix

class LawfulCodec (α : Type) [Codec α] : Prop where
  decode_encode : ∀ (a : α) (rest : List UInt8),
    Codec.decodeFrom (Codec.encode a ++ rest) = some (a, rest)

class CanonicalCodec (α : Type) [Codec α] : Prop where
  encode_decode : ∀ (bs : List UInt8) (a : α) (rest : List UInt8),
    Codec.decodeFrom bs = some (a, rest) → bs = Codec.encode a ++ rest
```

Instances: every type below has a `Codec`, a `LawfulCodec` (named `Codec.lawfulX`), and a `CanonicalCodec` (named `Codec.canonicalX`) instance. The compound ones require the same instances on their components.

| Type | Wire format | Lawful | Canonical |
|---|---|---|---|
| `Unit` | nothing | `lawfulUnit` | `canonicalUnit` |
| `Bool` | `0` / `1` | `lawfulBool` | `canonicalBool` |
| `UInt8` | 1 byte | `lawfulUInt8` | `canonicalUInt8` |
| `UInt16`, `UInt32`, `UInt64` | 2/4/8 bytes, little endian | `lawfulUInt16/32/64` | `canonicalUInt16/32/64` |
| `Nat` | unsigned LEB128, minimal form only | `lawfulNat` | `canonicalNat` |
| `Int` | zigzag, then LEB128 | `lawfulInt` | `canonicalInt` |
| `Fin n` | LEB128 of the value; `≥ n` rejected | `lawfulFin` | `canonicalFin` |
| `String` | LEB128 byte count, UTF-8 bytes; invalid UTF-8 rejected | `lawfulString` | `canonicalString` |
| `List α` | LEB128 count, elements | `lawfulList` | `canonicalList` |
| `Array α` | as `List α` | `lawfulArray` | `canonicalArray` |
| `Option α` | `0` / `1 ‖ a` | `lawfulOption` | `canonicalOption` |
| `α × β` | `a ‖ b` | `lawfulProd` | `canonicalProd` |
| `Sum α β` | `0 ‖ a` / `1 ‖ b` | `lawfulSum` | `canonicalSum` |

Theorems (`variable {α : Type} [Codec α]`):

```lean
theorem Codec.decode_encode [LawfulCodec α] (a : α) : decode (encode a) = some a
theorem Codec.decodeBytes_encodeBytes [LawfulCodec α] (a : α) :
    decodeBytes (encodeBytes a) = some a
theorem Codec.encode_decode [CanonicalCodec α] {bs : List UInt8} {a : α}
    (h : decode bs = some a) : bs = encode a
theorem Codec.encodeBytes_decodeBytes [CanonicalCodec α] {b : ByteArray} {a : α}
    (h : decodeBytes b = some a) : b = encodeBytes a
theorem Codec.encode_injective [LawfulCodec α] {a b : α} (h : encode a = encode b) : a = b

theorem Codec.decodeNat_encodeNat (n : Nat) (rest : List UInt8) :
    decodeNat (encodeNat n ++ rest) = some (n, rest)
theorem Codec.encodeNat_decodeNat {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : decodeNat bs = some (n, rest)) : bs = encodeNat n ++ rest
theorem Codec.decodeFixed_encodeFixed (k n : Nat) (h : n < 256 ^ k) (rest : List UInt8) :
    decodeFixed k (encodeFixed k n ++ rest) = some (n, rest)
theorem Codec.decodeFixed_lt {k : Nat} {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : decodeFixed k bs = some (n, rest)) : n < 256 ^ k ∧ bs = encodeFixed k n ++ rest
theorem Codec.decodeMany_encode [Codec α] [LawfulCodec α] (xs : List α) (rest : List UInt8) :
    decodeMany xs.length (xs.flatMap encode ++ rest) = some (xs, rest)
theorem Codec.decodeMany_canonical [Codec α] [CanonicalCodec α] {k : Nat} {bs : List UInt8}
    {xs : List α} {rest : List UInt8} (h : decodeMany k bs = some (xs, rest)) :
    xs.length = k ∧ bs = xs.flatMap encode ++ rest

theorem Codec.ofEquiv_lawful [Codec β] [LawfulCodec β] (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) : @LawfulCodec α (ofEquiv f g)
theorem Codec.ofEquiv_canonical [Codec β] [CanonicalCodec β] (f : α → β) (g : β → α)
    (h : ∀ b, f (g b) = b) : @CanonicalCodec α (ofEquiv f g)
theorem Codec.ofPartial_lawful [Codec β] [LawfulCodec β] (f : α → β) (g : β → Option α)
    (h : ∀ a, g (f a) = some a) : @LawfulCodec α (ofPartial f g)
theorem Codec.ofPartial_canonical [Codec β] [CanonicalCodec β] (f : α → β) (g : β → Option α)
    (h : ∀ a b, g b = some a → f a = b) : @CanonicalCodec α (ofPartial f g)
```

`Codec.decode` decodes the whole input and fails on leftover bytes. `encodeBytes`/`decodeBytes` are the `ByteArray` versions.

Why canonicity matters: with `LawfulCodec` and `CanonicalCodec` together, `encode` is a bijection between values and accepted byte strings. Two parties that hash encodings get equal hashes exactly when they hold equal values, and a peer cannot smuggle a second byte string (for example an over-long LEB128 number) that decodes to the same value.

Audit output (`lake env lean Codec/Audit.lean`): every listed theorem and instance depends only on a subset of `[propext, Classical.choice, Quot.sound]`; `lawfulUnit` and `lawfulUInt8` depend on no axioms. Full output:

```
'Codec.decode_encode' depends on axioms: [propext]
'Codec.decodeBytes_encodeBytes' depends on axioms: [propext]
'Codec.encode_decode' depends on axioms: [propext]
'Codec.encodeBytes_decodeBytes' depends on axioms: [propext]
'Codec.encode_injective' depends on axioms: [propext]
'Codec.decodeNat_encodeNat' depends on axioms: [propext, Quot.sound]
'Codec.encodeNat_decodeNat' depends on axioms: [propext, Quot.sound]
'Codec.decodeFixed_encodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.decodeFixed_lt' depends on axioms: [propext, Quot.sound]
'Codec.decodeMany_encode' depends on axioms: [propext]
'Codec.decodeMany_canonical' depends on axioms: [propext]
'Codec.ofEquiv_lawful' depends on axioms: [propext]
'Codec.ofEquiv_canonical' depends on axioms: [propext]
'Codec.ofPartial_lawful' depends on axioms: [propext]
'Codec.ofPartial_canonical' depends on axioms: [propext]
'Codec.lawfulUnit' does not depend on any axioms
'Codec.lawfulBool' depends on axioms: [propext]
'Codec.lawfulUInt8' does not depend on any axioms
'Codec.lawfulUInt16' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.lawfulUInt32' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.lawfulUInt64' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.lawfulNat' depends on axioms: [propext, Quot.sound]
'Codec.lawfulInt' depends on axioms: [propext, Quot.sound]
'Codec.lawfulFin' depends on axioms: [propext, Quot.sound]
'Codec.lawfulString' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.lawfulList' depends on axioms: [propext, Quot.sound]
'Codec.lawfulArray' depends on axioms: [propext, Quot.sound]
'Codec.lawfulOption' depends on axioms: [propext]
'Codec.lawfulProd' depends on axioms: [propext]
'Codec.lawfulSum' depends on axioms: [propext]
'Codec.canonicalUnit' depends on axioms: [propext]
'Codec.canonicalBool' depends on axioms: [propext]
'Codec.canonicalUInt8' depends on axioms: [propext]
'Codec.canonicalUInt16' depends on axioms: [propext, Quot.sound]
'Codec.canonicalUInt32' depends on axioms: [propext, Quot.sound]
'Codec.canonicalUInt64' depends on axioms: [propext, Quot.sound]
'Codec.canonicalNat' depends on axioms: [propext, Quot.sound]
'Codec.canonicalInt' depends on axioms: [propext, Quot.sound]
'Codec.canonicalFin' depends on axioms: [propext, Quot.sound]
'Codec.canonicalString' depends on axioms: [propext, Classical.choice, Quot.sound]
'Codec.canonicalList' depends on axioms: [propext, Quot.sound]
'Codec.canonicalArray' depends on axioms: [propext, Quot.sound]
'Codec.canonicalOption' depends on axioms: [propext]
'Codec.canonicalProd' depends on axioms: [propext]
'Codec.canonicalSum' depends on axioms: [propext]
```

## What is tested but not proved

- Concrete byte layouts (e.g. `300 ↦ [0xAC, 0x02]`, little-endian `UInt16`, zigzag for `Int`, UTF-8 for `"hé"`): `#guard` checks in `Tests/Guards.lean`, run by `lake build`.
- Rejection of specific malformed inputs (over-long LEB128, truncated input, bad tags, out-of-range `Fin`, invalid UTF-8, leftover bytes): `#guard` checks. The general rejection property is the canonicity theorem.
- Compiled-code behavior: `lake test` runs randomized round trips (500 values each for `Nat`, `Int`, `String`, `UInt16`, `UInt64`, plus compound types) and a canonicity spot check on 2000 random 4-byte inputs. The proofs cover the definitions; the tests check that the compiled code (including the C implementations of `String.toByteArray` and UTF-8 validation) agrees.
- Performance: not measured beyond the tests running in well under a second.
- `deriving Codec`: `Tests/Derive.lean` derives codecs for an enum, structures (0, 1, and 2 fields), and a 5-constructor inductive with nested derived types, then checks byte layouts and round trips with `#guard`. It also prints the axioms of the derived instances (standard ones only). The handler's error paths (recursive, parametric, missing field instance) were checked by hand.

## Quickstart

`lakefile.toml`:

```toml
[[require]]
name = "codec"
path = "../lean-codec"
```

```lean
import Codec

-- Built-in types
#eval Codec.encode (300 : Nat)                    -- [172, 2]
#eval (Codec.decode [172, 2] : Option Nat)        -- some 300
example (x : List (String × Option Int)) : Codec.decode (Codec.encode x) = some x :=
  Codec.decode_encode x

-- Your own types: map to a type that already has a codec.
inductive Color | red | green | blue deriving Repr, DecidableEq

def Color.toFin : Color → Fin 3 | .red => 0 | .green => 1 | .blue => 2
def Color.ofFin : Fin 3 → Color | 0 => .red | 1 => .green | 2 => .blue

instance : Codec Color := Codec.ofEquiv Color.toFin Color.ofFin
instance : LawfulCodec Color :=
  Codec.ofEquiv_lawful Color.toFin Color.ofFin (by intro c; cases c <;> rfl)
instance : CanonicalCodec Color :=
  Codec.ofEquiv_canonical Color.toFin Color.ofFin (by decide)
```

Or let the deriving handler do it (it generates `Codec`, `LawfulCodec`, and `CanonicalCodec` instances; the last two only when every field type has them):

```lean
inductive Resource | grain | timber | ore | wool | brick
  deriving Codec            -- constructor index as a Nat: one byte

structure Point where
  x : Int
  y : Int
  deriving Codec            -- fields as a product: encode x ++ encode y

inductive Shape
  | dot
  | circle (center : Point) (r : Nat)
  | tagged (res : Resource)
  deriving Codec            -- balanced Sum of products: ⌈log₂ k⌉ tag bytes
```

`deriving Codec` supports non-parametric inductive types and structures whose fields do not depend on each other and do not mention the type itself. It reports an error for recursive, mutual, nested, parametric, or indexed types.

By hand: for a structure, map to a product: `fun s => (s.a, s.b, s.c)`. For an inductive with payloads, map to nested `Sum`s of products (see the example below). Use `Codec.ofPartial` when the inverse can fail (e.g. a `Nat` that must be in range).

Build and test: `lake build` (library, `#guard` tests, audit) and `lake test` (randomized tests).

## Second use case: a tiny network message format

`examples/NetMsg.lean` defines a chat relay protocol with three message kinds (`hello`, `say`, `bye`). It derives a lawful, canonical codec through `Codec.ofEquiv` into `Sum (String × UInt16) (Sum (Nat × String × Option UInt64) Unit)`, packs four messages into one 46-byte packet, peels them off with `decodeFrom`, and shows that a corrupted tag byte is rejected.

```
$ lake exe netmsg
packet: 46 bytes: [0, 5, 97, 108, 105, 99, 101, 3, 0, 1, 0, 7, 11, ...]
decoded 4 messages, equal to input: true
corrupted packet decodes to: none
```
