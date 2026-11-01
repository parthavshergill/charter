import Codec

/-!
# Second use case: a tiny network message format

A chat relay speaks three message kinds over a byte stream. Several messages
are concatenated in one packet; the receiver peels them off one at a time with
`decodeFrom`, which returns the unconsumed rest.

Run with `lake exe netmsg`.
-/

inductive Msg where
  | hello (client : String) (version : UInt16)
  | say (room : Nat) (text : String) (replyTo : Option UInt64)
  | bye
  deriving Repr, BEq

namespace Msg

/-- Wire shape: tag-less, via a sum of products. -/
abbrev Wire := Sum (String × UInt16) (Sum (Nat × String × Option UInt64) Unit)

def toWire : Msg → Wire
  | hello c v => .inl (c, v)
  | say r t p => .inr (.inl (r, t, p))
  | bye => .inr (.inr ())

def ofWire : Wire → Msg
  | .inl (c, v) => hello c v
  | .inr (.inl (r, t, p)) => say r t p
  | .inr (.inr ()) => bye

theorem ofWire_toWire (m : Msg) : ofWire (toWire m) = m := by cases m <;> rfl
theorem toWire_ofWire (w : Wire) : toWire (ofWire w) = w := by
  rcases w with ⟨c, v⟩ | ⟨r, t, p⟩ | ⟨⟩ <;> rfl

instance : Codec Msg := Codec.ofEquiv toWire ofWire
instance : LawfulCodec Msg := Codec.ofEquiv_lawful toWire ofWire ofWire_toWire
instance : CanonicalCodec Msg := Codec.ofEquiv_canonical toWire ofWire toWire_ofWire

end Msg

/-- Read every message in a packet. Fuel = packet length: each message is
at least one byte. -/
def readAll (bs : List UInt8) : Option (List Msg) :=
  go bs.length bs
where
  go : Nat → List UInt8 → Option (List Msg)
    | _, [] => some []
    | 0, _ => none
    | fuel + 1, bs => do
      let (m, rest) ← Codec.decodeFrom (α := Msg) bs
      let ms ← go fuel rest
      return m :: ms

/-- The proof obligations hold for every message, not just these samples. -/
example (m : Msg) (rest : List UInt8) :
    Codec.decodeFrom (Codec.encode m ++ rest) = some (m, rest) :=
  Codec.decodeFrom_encode m rest

def main : IO Unit := do
  let msgs := [Msg.hello "alice" 3, .say 7 "hi all 👋" none, .say 7 "re: hi" (some 41), .bye]
  let packet := msgs.flatMap Codec.encode
  IO.println s!"packet: {packet.length} bytes: {packet}"
  match readAll packet with
  | some back =>
    IO.println s!"decoded {back.length} messages, equal to input: {back == msgs}"
  | none => IO.println "decode failed"
  -- A corrupted byte is rejected rather than misread.
  let bad := packet.set 0 9
  IO.println s!"corrupted packet decodes to: {repr (readAll bad)}"
