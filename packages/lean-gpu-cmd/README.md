# lean-gpu-cmd

Lean programs describe a 3D scene as a compact, proved-decodable binary command
stream, and a small three.js player (`web/player.js`) renders it in the browser,
animates changes, and reports which object the user clicked.

## Non-goals

- Not a general 3D engine. There are eight primitives, one kind of mesh file, one sun,
  and text labels. No textures, and no general model formats: a mesh file has only
  vertices, vertex colors and triangles, and is named by its SHA-256.
- No scene graph or hierarchy on the Lean side: a stream is a flat list of draws.
- The player is not proved. Only the Lean encoder/decoder pair is.
- No incremental/delta protocol: each stream is a complete scene. The player
  computes the transitions.
- No float arithmetic guarantees: numbers are carried as binary32 bit patterns.

## Guarantees

All theorems are in `GpuCmd/Wire.lean` and `GpuCmd/Codec.lean`. The proofs are
about the byte-level structure of the encoding over `List UInt8`.

```lean
-- the full stream (ByteArray API)
theorem GpuCmd.decode_encode (cs : List Cmd) : decode (encode cs) = some cs
-- the full stream over bytes: magic "GPC1", then commands back to back
theorem GpuCmd.decodeList_encodeList (cs : List Cmd) : decodeList (encodeList cs) = some cs
-- one command, followed by arbitrary bytes
theorem GpuCmd.readCmd_cmdBytes (c : Cmd) (rest : List UInt8) :
    readCmd (cmdBytes c ++ rest) = some (c, rest)
theorem GpuCmd.readPrim_primBytes (p : Prim) (rest : List UInt8) :
    readPrim (primBytes p ++ rest) = some (p, rest)
theorem GpuCmd.readMotion_motionBytes (m : Motion) (rest : List UInt8) :
    readMotion (motionBytes m ++ rest) = some (m, rest)
-- scalar encodings
theorem GpuCmd.Wire.readU32_u32 (x : UInt32) (rest : List UInt8) :
    readU32 (u32 x ++ rest) = some (x, rest)
theorem GpuCmd.Wire.readF32_f32 (f : F32) (rest : List UInt8) :
    readF32 (f32 f ++ rest) = some (f, rest)
theorem GpuCmd.Wire.readUleb_uleb (n : Nat) (rest : List UInt8) :
    readUleb (uleb n ++ rest) = some (n, rest)
theorem GpuCmd.Wire.readStr_str (s : String) (rest : List UInt8) :
    readStr (str s ++ rest) = some (s, rest)
```

The round trip is exact because the wire value type for reals is `F32`, a
structure holding the binary32 bit pattern (`bits : UInt32`). Rounding happens
only in `F32.ofFloat : Float → F32`, outside the theorem. Strings carry an
unbounded ULEB128 length, so the theorems have no size hypotheses.

`#print axioms` output (`GpuCmd/Audit.lean`, built by `lake build`):

```
'GpuCmd.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.decodeList_encodeList' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.readCmd_cmdBytes' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.readPrim_primBytes' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.readMotion_motionBytes' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.Wire.readU32_u32' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.Wire.readF32_f32' depends on axioms: [propext, Classical.choice, Quot.sound]
'GpuCmd.Wire.readUleb_uleb' depends on axioms: [propext, Quot.sound]
'GpuCmd.Wire.readStr_str' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What is tested but not proved

- Golden bytes for `clear`, `highlight`, ULEB128 and UTF-8 labels; command sizes
  match `WIRE.md`; rejection of bad magic, truncation, unknown opcodes, invalid
  UTF-8; `F32` bit patterns for 1.0, -2.5, 0.1 (`Tests/Basic.lean`, `#guard`).
- A 2,013-command round trip at run time (`lake test`).
- The JavaScript decoder agrees with the Lean encoder on a golden stream that
  uses every opcode and primitive, a non-ASCII label and a 300-byte label
  (`node web/decode.test.mjs`, after `lake test` writes `Tests/golden.gpc`). The same test
  feeds the mesh file reader good and bad files.
- The player in headless Chrome (Playwright, manual run): the bar chart renders
  37 meshes and 18 labels with shadows; hovering a bar sets the hover id; a click
  calls `onPick` with the bar's pick id; switching data tweens the bars; orbit
  drag and wheel zoom work.
- Re-rendering an identical stream reuses every object and starts no animation;
  a malformed stream throws and leaves the current scene intact; a settled
  63-object scene runs at display rate (16.7 ms/frame) in headless Chrome.
- The shapes demo (`examples/Shapes.lean`, `index.html?scene=shapes`) shows all six
  primitives, translucent pickable ghosts, highlights, a moved piece, dropped-in
  pieces and a removed piece.
- Not tested: touch pinch zoom on a real device, very large scenes (> 5,000 draws).

## Quickstart

`lakefile.toml`:

```toml
[[require]]
name = "GpuCmd"
path = "../lean-gpu-cmd"
```

Lean:

```lean
import GpuCmd
open GpuCmd

def scene : List Cmd :=
  [.camera (vec3 6 8 10) (vec3 0 0 0) 40,
   .light (vec3 (-0.5) (-1) (-0.3)) 1.0,
   .defineMesh 1 (.hexPrism 1 0.25),
   .defineMesh 2 (.house 0.4 0.45 0.4),
   .draw 1 (Transform.at 0 0 0) 0xD9B44A 0,
   .draw 2 { pos := vec3 0 0.25 0, rotY := 0.3 } 0xC0392B 17,   -- pickable, id 17
   .label "6" (vec3 0 0.6 0) 0.4 0xFFFFFF 0,
   .highlight 17 0xFFD27A]

def bytes : ByteArray := encode scene    -- serve as application/octet-stream
```

Browser (copy `web/` including `web/vendor/`; no CDN):

```html
<canvas id="c" style="width:100vw;height:100vh"></canvas>
<script type="module">
  import { GpuPlayer } from './web/player.js';
  const p = new GpuPlayer(document.getElementById('c'));
  p.onPick = (id) => console.log('picked', id);
  p.render(await (await fetch('/scene')).arrayBuffer());   // call again on every update
</script>
```

Player API: `new GpuPlayer(canvas, { table?: boolean, background?: number })`,
`render(arrayBuffer)`, `onPick(pickId)`, `onHover(pickId | 0)`, `pickAt(ndcX, ndcY)`,
`screenOf(pickId)`, `resetView()`, `setTable(bool)`, `stats()`, `dispose()`.
The option `assetBase` (default `/assets`) says where mesh files are.
Also `decodeStream(buf)` (plain objects) and `ease`.

What the player does:

- Warm tabletop: procedural wooden table at y = 0, hemisphere sky light, a warm
  directional sun with soft PCF shadows fitted to the scene (including object
  heights), a cool fill light, a small procedural environment map for soft
  reflections, ACES tone mapping, fog that hides the table edge.
- Primitives have small bevels (extruded hexes and boxes, lathed cylinders).
- Orbit camera: drag to orbit, right-drag or shift-drag to pan, wheel or pinch
  to zoom, double-click to reset. Polar angle and distance are clamped. A repeated
  `camera` command keeps the viewer's orbit.
- Picking by raycast. Hovered pickables lift slightly and glow; the cursor
  becomes a pointer. A click without drag calls `onPick`.
- `highlight` adds a pulsing back-face outline in the given color (labels get a
  colored glow).
- Transitions between `render` calls: moves, rescales and color changes tween
  with ease-out cubic over 350 ms; new objects drop in with a small bounce and a
  landing squash; removed objects shrink and fade. Identity rules are in `WIRE.md`.

Wire format: see [`WIRE.md`](WIRE.md).

## Second use case: a 3D bar chart

`examples/BarChart.lean` renders monthly rainfall for three cities as a 3D bar
chart, with month and city labels, the wettest month of each city highlighted
and labeled, and every bar pickable.

```sh
lake exe bar-chart-demo examples      # writes examples/barchart-a.gpc and -b.gpc
lake exe shapes-demo examples         # optional: examples/shapes-*.gpc
python3 -m http.server 8000           # from the package root
# open http://localhost:8000/examples/index.html
```

The page shows the hovered or clicked bar ("Mumbai, Jul") and has a button that
switches between two data sets, so the bars animate to their new heights.

## Layout

```
GpuCmd/Types.lean   F32, Vec3, Transform, Prim, Cmd
GpuCmd/Wire.lean    little-endian words, f32, ULEB128, strings + lemmas
GpuCmd/Codec.lean   encode / decode + round-trip theorems
GpuCmd/Audit.lean   #print axioms
Tests/              #guard tests, lake test driver
web/player.js       three.js player (ES module); web/vendor/three.module.min.js (r170, MIT)
web/meshfile.js     reads and refuses mesh files (no three.js)
examples/           bar chart (Lean exe + index.html)
WIRE.md             byte layout and player semantics
```

No dependencies besides Lean core (no Mathlib, no Batteries).
