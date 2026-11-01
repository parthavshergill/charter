import Lean.Data.Json

/-! Small helpers for the Charter server: random ids, hex, JSON field access. -/

namespace CharterServer
open Lean

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (b : ByteArray) : String := Id.run do
  let mut s := ""
  for x in b.toList do
    s := s.push (hexDigit (x.toNat / 16)) |>.push (hexDigit (x.toNat % 16))
  return s

def randomBytes (n : Nat) : IO ByteArray := IO.getRandomBytes n.toUSize

/-- Random token (hex). -/
def randomToken : IO String := return toHex (← randomBytes 16)

/-- Game codes: 5 letters from an unambiguous alphabet. -/
def codeAlphabet : String := "ABCDEFGHJKMNPQRSTUVWXYZ"

def randomCode : IO String := do
  let bs ← randomBytes 5
  let chars := codeAlphabet.toList
  return String.ofList (bs.toList.map fun b => chars[b.toNat % chars.length]!)

def jStr (j : Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption

def jNat (j : Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption

def jBool (j : Json) (k : String) : Option Bool :=
  (j.getObjValAs? Bool k).toOption

def jField (j : Json) (k : String) : Option Json :=
  (j.getObjVal? k).toOption

/-- Remove all object keys that start with `_` (private fields such as tokens or seeds). -/
partial def stripPrivate : Json → Json
  | .obj kvs =>
      Json.mkObj <| kvs.toList.filterMap fun (k, v) =>
        if k.startsWith "_" then none else some (k, stripPrivate v)
  | .arr xs => .arr (xs.map stripPrivate)
  | j => j

def nowMs : IO Nat := IO.monoMsNow

/-- Wall clock seconds via `date +%s` would need a process; use monotonic for ordering only. -/
def okJson (extra : List (String × Json) := []) : Json :=
  Json.mkObj (("ok", true) :: extra)

def errJson (msg : String) : Json :=
  Json.mkObj [("ok", false), ("error", msg)]

end CharterServer
