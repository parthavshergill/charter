# lean-gpu-cmd wire format, version 1

A stream is a byte string:

```
stream  := magic cmd*            -- commands back to back until the input ends
magic   := 0x47 0x50 0x43 0x31   -- ASCII "GPC1"
```

All multi-byte integers are **little endian**. There is no count field and no
padding. A decoder reads commands until no bytes are left. An unknown opcode or a
truncated command makes the whole stream invalid (Lean `decode` returns `none`,
`player.js` throws).

## Scalar encodings

| name  | bytes | meaning |
|-------|-------|---------|
| `u8`  | 1 | unsigned byte |
| `u32` | 4 | unsigned 32-bit integer, little endian |
| `f32` | 4 | IEEE-754 binary32 bit pattern, little endian (`DataView.getFloat32(o, true)`) |
| `vec3`| 12 | `f32 x, f32 y, f32 z` |
| `str` | n+k | ULEB128 byte length `n` (k bytes), then `n` bytes of UTF-8 |
| `rgb` | 4 | `u32` = `0xTTRRGGBB`. `TT` is transparency: `0x00` opaque, `0xFF` invisible. Plain `0xRRGGBB` is opaque. sRGB. |

ULEB128: 7 bits per byte, least significant group first, high bit set on every
byte except the last. `0 → 00`, `127 → 7F`, `128 → 80 01`, `300 → AC 02`.

In Lean, an `f32` is the structure `GpuCmd.F32 { bits : UInt32 }`. The wire stores
`bits` exactly, so the round-trip theorem is exact. `F32.ofFloat` rounds a
`Float` to binary32 at the edge.

## Transform

```
transform := vec3 pos, f32 rotY, vec3 scale     -- 28 bytes
```

The player applies scale first (mesh space), then rotation by `rotY` radians about
+Y (counter-clockwise seen from above, right-handed), then translation to `pos`.

## Commands

| op | name | payload | size |
|----|------|---------|------|
| 1 | `clear` | `rgb` background | 5 |
| 2 | `camera` | `vec3 eye, vec3 target, f32 fovDeg` | 29 |
| 3 | `light` | `vec3 dir, f32 intensity` | 17 |
| 4 | `defineMesh` | `u32 id, prim` | 5 + prim |
| 5 | `draw` | `u32 mesh, transform, rgb, u32 pick` | 41 |
| 6 | `label` | `str text, vec3 pos, f32 size, rgb, u32 pick` | 25 + str |
| 7 | `highlight` | `u32 pick, rgb` | 9 |
| 8 | `defineMeshFile` | `u32 id, str sha256, rgb tint, f32 pulse, f32 sway, f32 glow, prim standIn` | 21 + str + prim |

### Primitives

```
prim := u8 kind, f32 args...
```

| kind | name | args | shape (base on y = 0, centered on the Y axis) |
|------|------|------|-------|
| 1 | `hexPrism` | `radius, height` | hexagon, corner distance `radius`, pointy along ±Z |
| 2 | `box` | `w, h, d` | width X, height Y, depth Z |
| 3 | `cylinder` | `r, h` | |
| 4 | `cone` | `r, h` | apex at y = h |
| 5 | `sphere` | `r` | center at y = r |
| 6 | `house` | `w, h, d` | walls to `0.6 h`, pitched roof to `h`, ridge along Z |
| 7 | `gable` | `w, h, d` | a roof with no walls: triangular prism, full width at `y = 0`, ridge along Z at `y = h` |
| 8 | `pyramid` | `r, h` | four-sided, base corners at distance `r` on the X and Z axes, apex at `y = h` |

## Semantics (player)

- Y is up. The player draws a wooden table at y = 0 (option `table: false` hides it).
- `clear` sets the background color. Default: a warm dark brown.
- `camera` sets the orbit target and eye. The player keeps the viewer's orbit
  when the next stream repeats the same `camera` command; a different command
  moves the camera smoothly.
- A `camera` with `fovDeg < 0` asks for an orthographic camera. `-fovDeg` is the world
  radius, around the target, that must stay in view at any window shape. The player
  fixes the direction: the viewer can pan and zoom but not orbit. A player that does
  not know this rule treats the value as an unusable field of view and falls back to
  45 degrees, so the stream still draws.
- `light dir intensity`: `dir` is the direction the sun rays travel (from the
  light toward the scene, e.g. `(-0.5, -1, -0.3)`). `intensity 1` is the default sun.
  A hemisphere sky light is always present.
- `defineMesh` binds a mesh id to a primitive. Redefining an id with another
  primitive replaces the geometry for later draws in the same and later streams.
- `defineMeshFile` binds a mesh id to a triangle mesh file, named by `sha256`: 64 lower-case hex
  digits. The player fetches `<assetBase>/<sha256>.mesh` once (`assetBase` is `/assets` unless the
  page says otherwise). It knows no other name for the file. Until the file loads, and for good if
  the file is missing or bad, it draws `standIn` in the color `tint`. A missing file is not an
  error in the stream. Draws are the same as for a primitive, and the draw's color multiplies the
  file's vertex colors, so a file that is white takes the draw's color. Flat shading stays on.
- `pulse`, `sway` and `glow` make every instance of the mesh move by itself: height by the fraction
  `pulse`, with the width going the other way, a tilt of `sway` radians about its base, and up to
  `glow` of added light in the draw's color. All zero means still. Reduced motion turns them off.
- `draw` places one instance. `pick ≠ 0` makes it pickable: hover highlights it
  and a click calls `onPick(pick)`. Several objects may share a pick id.
- `label` draws camera-facing text centered at `pos`, `size` world units tall.
- `highlight pick rgb` outlines and pulses every object with that pick id.
- Commands are processed in order. `defineMesh` must come before draws that use it.

### Identity and transitions

The player matches objects between consecutive streams:

1. Objects with `pick ≠ 0` match by `(pick, mesh, k)`: the k-th draw of that mesh
   with that pick id. Labels with `pick ≠ 0` match by `(pick, k)`.
2. Objects with `pick = 0` match by mesh id and exact position (labels: by text). An
   object with no match is new, so it drops in, and the old one fades out. Decoration
   never glides across the board.

A matched object that changed transform or color tweens to the new state (ease-out
cubic, 350 ms). A new object drops in with a small bounce (≈450 ms). An object
missing from the new stream shrinks and fades out (≈220 ms).

Use **stable** pick ids (derived from what the object is, such as a board
coordinate), not list indexes. Otherwise objects can glide to unrelated places.

## Mesh files

A mesh file holds only numbers: no textures, URIs or scripts. All values are little endian.

```
file := "GPM1", u32 vertices, u32 triangles, f32 minX, minY, minZ, f32 maxX, maxY, maxZ,
        position*, color*, index*
position := u16 x, y, z    -- 0 is the minimum and 65535 is the maximum on that axis
color    := u8 r, g, b     -- sRGB, one per vertex
index    := u16 a, b, c    -- one per triangle, counter-clockwise from outside
```

The file's length must be exactly `36 + 9 vertices + 6 triangles` bytes. The player refuses a file
that is too large, has a wrong length, has a bound that is not a finite number or that crosses,
has an index past the last vertex, or does not hash to its name. The limits are in `web/meshfile.js`.
