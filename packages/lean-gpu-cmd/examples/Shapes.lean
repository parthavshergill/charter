import GpuCmd

/-!
# All primitives on a small hex board

Writes `shapes-a.gpc` and `shapes-b.gpc`. Frame b moves a cone, adds houses and a
sphere, removes a cylinder, and turns the ghost spots into highlights, so every
player transition shows. View with `examples/index.html?scene=shapes`.
-/

open GpuCmd

def hexAt (q r : Int) : Float × Float :=
  let qf := Float.ofInt q
  let rf := Float.ofInt r
  (1.02 * Float.sqrt 3 * (qf + rf / 2), 1.02 * 1.5 * rf)

def board : List (Int × Int) := Id.run do
  let mut hs := []
  for q in [-2, -1, 0, 1, 2] do
    for r in [-2, -1, 0, 1, 2] do
      if (q + r).natAbs ≤ 2 then hs := hs ++ [(q, r)]
  return hs

def tileColors : Array UInt32 := #[0xE3C16F, 0x6E9F4B, 0x9AA3A8, 0xB8DB7A, 0xB5653E, 0xD8C49A]

def frame (b : Bool) : List Cmd := Id.run do
  let mut cs : List Cmd :=
    [.camera (vec3 0 9 9.5) (vec3 0 0 0) 40,
     .light (vec3 (-0.5) (-1) (-0.35)) 1.0,
     .defineMesh 1 (.hexPrism 1 0.22), .defineMesh 2 (.cylinder 0.32 0.08),
     .defineMesh 3 (.cone 0.22 0.55), .defineMesh 4 (.sphere 0.18),
     .defineMesh 5 (.house 0.36 0.42 0.36), .defineMesh 6 (.box 0.85 0.09 0.14),
     .defineMesh 7 (.cylinder 0.16 0.06)]
  let mut i := 0
  for (q, r) in board do
    let (x, z) := hexAt q r
    let pick := (1000 + i).toUInt32
    cs := cs ++ [.draw 1 (Transform.at x 0 z) tileColors[i % tileColors.size]! pick]
    if !(q == 0 && r == 0) then
      cs := cs ++ [.draw 2 (Transform.at x 0.22 z) 0xF2E6CC 0,
        .label s!"{i % 6 + 1}" (vec3 x 0.55 z) 0.36 (if i % 6 == 5 then 0xC0392B else 0x2B1D12) 0]
    i := i + 1
  -- pieces
  let (cx, cz) := hexAt 1 (-1)
  let conePos := if b then hexAt (-1) 1 else hexAt 0 1
  cs := cs ++ [.draw 3 (Transform.at conePos.1 0.3 (conePos.2 + 0.45)) 0x2C3E50 77,
    .draw 6 { pos := vec3 (cx - 0.9) 0.22 (cz + 0.5), rotY := 0.52 } 0xC0392B 0,
    .draw 5 { pos := vec3 (cx - 0.45) 0.22 (cz + 0.78), rotY := 0.3 } 0xC0392B 31]
  if b then
    cs := cs ++ [.draw 5 { pos := vec3 0.9 0.22 1.3 } 0x2E86C1 32,
      .draw 5 { pos := vec3 (-1.7) 0.22 (-0.5), rotY := 1.0 } 0x27AE60 33,
      .draw 4 (Transform.at 1.6 0.22 (-1.9)) 0xF1C40F 0]
  else
    cs := cs ++ [.draw 2 { pos := vec3 2.8 0.22 0.2, scale := vec3 1.6 4 1.6 } 0x8E44AD 0]
  -- ghost build spots (translucent, pickable)
  for (k, (x, z)) in (List.range 3).zip [(0.0, -1.55), (-0.9, 1.05), (1.8, 0.5)] do
    let id := (500 + k).toUInt32
    cs := cs ++ [.draw 7 (Transform.at x 0.22 z) (withAlpha 0xFFFFFF 0.45) id]
    if b then cs := cs ++ [.highlight id 0xFFD27A]
  cs := cs ++ [.label (if b then "Your turn: build" else "Round 3") (vec3 0 2.4 (-3.6)) 0.5 0xFFE7B0 900]
  cs := cs ++ [.highlight 1000 0x7FD3FF]
  return cs

def main (args : List String) : IO Unit := do
  let dir := args.headD "examples"
  for (file, b) in [("shapes-a.gpc", false), ("shapes-b.gpc", true)] do
    let bytes := encode (frame b)
    IO.FS.writeBinFile (System.FilePath.mk dir / file) bytes
    IO.println s!"wrote {dir}/{file}: {(frame b).length} commands, {bytes.size} bytes"
