import Codec

/-! Compile-time checks, built by `lake build`. -/

open Codec

-- Known byte layouts.
#guard encode (300 : Nat) = [0xAC, 0x02]
#guard encode (0 : Nat) = [0]
#guard encode (127 : Nat) = [0x7F]
#guard encode (128 : Nat) = [0x80, 0x01]
#guard encode (0x1234 : UInt16) = [0x34, 0x12]
#guard encode (0xDEADBEEF : UInt32) = [0xEF, 0xBE, 0xAD, 0xDE]
#guard encode (-1 : Int) = [1]
#guard encode (1 : Int) = [2]
#guard encode (-3 : Int) = [5]
#guard encode "hé" = [3, 0x68, 0xC3, 0xA9]
#guard encode ([true, false] : List Bool) = [2, 1, 0]
#guard encode (some (7 : UInt8)) = [1, 7]
#guard encode (none : Option UInt8) = [0]
#guard encode ((Sum.inr 5 : Sum Bool Nat)) = [1, 5]
#guard encode ((3 : Fin 10), "a") = [3, 1, 0x61]

-- Rejections (canonicity / validity).
#guard (decode [0x80, 0x00] : Option Nat) = none          -- over-long LEB128
#guard (decode [0x80] : Option Nat) = none                -- truncated
#guard (decode [2] : Option Bool) = none                  -- bad tag
#guard (decode [12] : Option (Fin 10)) = none             -- out of range
#guard (decode [1, 0xFF] : Option String) = none          -- invalid UTF-8
#guard (decode [1, 2] : Option UInt8) = none              -- leftover byte
#guard (decode [3, 1, 2] : Option (List UInt8)) = none    -- too short

-- Round trips on sample values.
#guard (decode (encode (2^70 + 5 : Nat)) : Option Nat) = some (2^70 + 5)
#guard (decode (encode (-(2^70 : Int))) : Option Int) = some (-(2^70))
#guard (decode (encode (0xFFFFFFFFFFFFFFFF : UInt64)) : Option UInt64) = some 0xFFFFFFFFFFFFFFFF
#guard (decodeBytes (encodeBytes #[("x", some (-4 : Int)), ("yz", none)]) :
    Option (Array (String × Option Int))) = some #[("x", some (-4)), ("yz", none)]

-- Instance resolution for lawful/canonical compound types.
example : LawfulCodec (List (Nat × Option String) × Array (Sum Int (Fin 3))) := inferInstance
example : CanonicalCodec (List (Nat × Option String) × Array (Sum Int (Fin 3))) := inferInstance
example (x : List (Int × Bool)) : decode (encode x) = some x := decode_encode x
