import Server.Policy.Net

/-!
# Differential test: Lean policy forward pass vs the NumPy reference

Usage: `policy-diff WEIGHTS OBS.txt EXPECTED.txt`

`OBS.txt` has one observation per line (space-separated numbers); a blank
line or `reset` sets the recurrent state back to zeros (a new game); `turn` starts a
new turn of the seat, and the weights file's state rule says what that does. `EXPECTED.txt` has
one line of logits per observation, written by
`scripts/policy_diff.py expect`. Prints the largest absolute and relative
error over all logits, and the time per forward pass. Exits with code 1 if
the largest absolute error is above `1e-4`.
-/

namespace CharterServer.Policy.Diff

open CharterServer.Policy

/-- Largest allowed absolute difference between a Lean and a NumPy logit. -/
def tolerance : Float := 1e-4

/-- Parse a decimal number like `-1.25e-3`. `none` if it is not one. -/
def parseFloat (s : String) : Option Float := Id.run do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let mut m : Nat := 0
  let mut fracDigits : Nat := 0
  let mut seenDot := false
  let mut digits := 0
  let mut rest := cs
  -- mantissa
  while true do
    match rest with
    | c :: r =>
      if c.isDigit then
        m := m * 10 + (c.toNat - '0'.toNat); digits := digits + 1
        if seenDot then fracDigits := fracDigits + 1
        rest := r
      else if c == '.' && !seenDot then
        seenDot := true; rest := r
      else break
    | [] => break
  if digits == 0 then return none
  -- exponent
  let mut ex : Int := 0
  match rest with
  | c :: r =>
    if c == 'e' || c == 'E' then
      let (eneg, r) := match r with
        | '-' :: r' => (true, r') | '+' :: r' => (false, r') | r' => (false, r')
      if r.isEmpty || !r.all Char.isDigit then return none
      let v : Nat := r.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
      ex := if eneg then -(v : Int) else v
    else return none
  | [] => pure ()
  let e := ex - fracDigits
  let mag := if e ≥ 0 then Float.ofScientific m false e.toNat
             else Float.ofScientific m true (-e).toNat
  return some (if neg then -mag else mag)

#guard parseFloat "-1.25e-3" == some (-0.00125)
#guard parseFloat "42" == some 42.0
#guard parseFloat "x" == none

/-- Show a non-negative number in scientific form, like `3.2e-9`. -/
def sci (x : Float) : String :=
  if x == 0.0 || x.isNaN || x.isInf then toString x else
  let e := (Float.log10 x).floor
  s!"{x / Float.pow 10.0 e}e{e.toInt64}"

/-- Parse a line of space-separated numbers. -/
def parseLine (line : String) : Except String FloatArray := do
  let mut a := FloatArray.emptyWithCapacity 4434
  for w in line.splitOn " " do
    if w.isEmpty then continue
    match parseFloat w with
    | some v => a := a.push v
    | none => throw s!"not a number: {w}"
  return a

end CharterServer.Policy.Diff

open CharterServer.Policy CharterServer.Policy.Diff in
/-- Run the differential test; see the module docstring. -/
def main (args : List String) : IO UInt32 := do
  let [wPath, obsPath, expPath] := args
    | IO.eprintln "usage: policy-diff WEIGHTS OBS.txt EXPECTED.txt"; return 2
  let net ← match Net.read (← IO.FS.readBinFile wPath) with
    | .ok n => pure n
    | .error e => IO.eprintln e; return 2
  let obsLines := (← IO.FS.lines obsPath)
  let expLines := (← IO.FS.lines expPath).filter (fun l => !l.trimAscii.toString.isEmpty)
  let mut state := net.initState
  let mut row := 0
  let mut maxAbs := 0.0
  let mut maxRel := 0.0
  let mut nanos := 0
  for raw in obsLines do
    let line := raw.trimAscii.toString
    if line.isEmpty || line == "reset" then
      state := net.initState; continue
    if line == "turn" then
      state := net.atTurnStart state; continue
    let obs ← match parseLine line with
      | .ok o => pure o | .error e => IO.eprintln e; return 2
    let some expLine := expLines[row]?
      | IO.eprintln s!"EXPECTED.txt has only {expLines.size} rows"; return 2
    let want ← match parseLine expLine with
      | .ok o => pure o | .error e => IO.eprintln e; return 2
    let t0 ← IO.monoNanosNow
    let (logits, s2) ← match net.forward obs (net.atDecision state) with
      | .ok r => pure r | .error e => IO.eprintln e; return 2
    -- force the result before stopping the clock
    let _ := logits.size
    let t1 ← IO.monoNanosNow
    nanos := nanos + (t1 - t0)
    state := s2
    if want.size != logits.size then
      IO.eprintln s!"row {row}: {logits.size} logits, expected {want.size}"; return 1
    for i in [0:want.size] do
      let d := (logits[i]! - want[i]!).abs
      let r := d / max want[i]!.abs 1e-6
      if d > maxAbs || d.isNaN then maxAbs := d
      if r > maxRel then maxRel := r
    row := row + 1
  IO.println s!"rows: {row}, logits per row: {net.actSize}"
  IO.println s!"max abs error: {sci maxAbs}"
  IO.println s!"max rel error: {sci maxRel}"
  IO.println s!"time per forward: {(nanos.toFloat / (max row 1).toFloat) / 1e6} ms"
  if maxAbs > tolerance || maxAbs.isNaN then
    IO.println s!"FAIL: max abs error above {tolerance}"; return 1
  IO.println s!"OK (tolerance {tolerance})"
  return 0
