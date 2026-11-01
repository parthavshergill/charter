import Codec

/-! Randomized round-trip tests (`lake test`). A tiny LCG drives generation so
the run is deterministic and needs no dependencies. -/

open Codec

structure Lcg where s : UInt64

def Lcg.next (g : Lcg) : UInt64 × Lcg :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  (s >>> 11, ⟨s⟩)

def genNat (g : Lcg) : Nat × Lcg :=
  let (a, g) := g.next
  let (b, g) := g.next
  let bits := (a % 4).toNat
  -- mix of tiny, medium and big naturals
  let n := match bits with
    | 0 => (b % 200).toNat
    | 1 => (b % 70000).toNat
    | 2 => b.toNat
    | _ => b.toNat * 2^64 + a.toNat
  (n, g)

def genString (g : Lcg) : String × Lcg := Id.run do
  let (len, g0) := genNat g
  let mut g := g0
  let mut s := ""
  for _ in [0:len % 12] do
    let (c, g') := g.next
    g := g'
    let cs := #['a', 'Z', '0', ' ', 'é', '€', '𝄞', '\n']
    s := s.push cs[(c % 8).toNat]!
  (s, g)

def check {α : Type} [Codec α] [BEq α] (name : String) (xs : List α) : IO Bool := do
  let mut ok := true
  for x in xs do
    if (decode (encode x) : Option α) != some x then
      IO.println s!"FAIL {name}"
      ok := false
    -- prefix property: decoding with trailing bytes leaves them intact
    match (decodeFrom (encode x ++ [0xAA, 0xBB]) : Option (α × List UInt8)) with
    | some (y, r) => if !(y == x && r == [0xAA, 0xBB]) then IO.println s!"FAIL prefix {name}"; ok := false
    | none => IO.println s!"FAIL prefix none {name}"; ok := false
  return ok

def main : IO UInt32 := do
  let mut g : Lcg := ⟨42⟩
  let mut nats : List Nat := []
  let mut ints : List Int := []
  let mut strs : List String := []
  for _ in [0:500] do
    let (n, g1) := genNat g
    let (m, g2) := genNat g1
    let (s, g3) := genString g2
    g := g3
    nats := n :: nats
    ints := (if m % 2 = 0 then (n : Int) else -(n : Int)) :: ints
    strs := s :: strs
  let mut ok := true
  ok := (← check "Nat" nats) && ok
  ok := (← check "Int" ints) && ok
  ok := (← check "String" strs) && ok
  ok := (← check "UInt64" (nats.map UInt64.ofNat)) && ok
  ok := (← check "UInt16" (nats.map UInt16.ofNat)) && ok
  ok := (← check "List (Nat × String)" [nats.zip strs, [], (nats.zip strs).take 3]) && ok
  ok := (← check "Array (Option Int)" [(ints.map fun i => if i % 3 = 0 then none else some i).toArray]) && ok
  -- Canonicity spot check: random byte strings that decode re-encode to themselves.
  let mut accepted := 0
  for _ in [0:2000] do
    let (a, g1) := g.next
    let (b, g2) := g1.next
    g := g2
    let bytes : List UInt8 := [a.toUInt8, (a >>> 8).toUInt8, b.toUInt8, (b >>> 8).toUInt8]
    match (decodeFrom bytes : Option (Nat × List UInt8)) with
    | some (n, r) =>
      accepted := accepted + 1
      if encode n ++ r != bytes then IO.println s!"FAIL canonical {bytes}"; ok := false
    | none => pure ()
  IO.println s!"canonicity spot check: {accepted} accepted inputs re-encoded exactly"
  if ok then IO.println "all codec tests passed"; return 0 else return 1
