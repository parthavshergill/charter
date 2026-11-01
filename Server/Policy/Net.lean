/-!
# Policy network: forward pass in plain Lean

This file runs a trained policy network (the "entity2" PufferLib model) on one
observation. It reads the weights from a file, turns an observation into one
score (logit) per action, and keeps a small memory (the recurrent state)
between calls.

## Weights file (`.chpw`)

All numbers are little-endian.

1. The 4 bytes `CHPW`.
2. Eleven unsigned 32-bit integers, in this order:
   format version (must be 1), layout version, `E` (size of one table row
   after encoding), `hidden`, `layers`, `act_size` (number of actions),
   `pointer` (0, 1 or 2), `act_spot`, `act_link`, `act_bank` (where the
   pointer scores go in the action list), `ntables`.
3. For each table: three unsigned 32-bit integers (offset, rows, width).
   The table's values sit at `obs[offset .. offset + rows*width]`, one row
   after another. Column 0 of a row is 1 for a real row and 0 for padding.
4. Four unsigned 32-bit integers: the table numbers of the `kinds`,
   `spots`, `links` and `resources` tables (used by the pointer scores).
5. The weights: 32-bit floats, exactly as in the PufferLib `.bin` file.
   Each block is padded with zeros up to a multiple of 8 floats. Blocks, in
   order, all row-major:
   - one input block per table, `E x width`;
   - `out`, `hidden x (ntables*E)`;
   - `decoder`, `(act_size+1) x hidden` (the last row is the value head; it
     is not used here);
   - if `pointer > 0`: `ptr`, `(2E if pointer = 1, else 4E) x hidden`;
   - one MinGRU block per layer, `(3*hidden) x hidden`.

So converting a PufferLib checkpoint is: header bytes, then the `.bin` bytes.
The observation layout (the tables) lives in the header, so a new layout
needs only a new weights file, not new code.

The math uses 64-bit floats. The reference is the NumPy code in
`scripts/policy_diff.py`.
-/

namespace CharterServer.Policy

/-- One table of the observation: where it starts, how many rows, how many
values per row. -/
structure NetTable where
  offset : Nat
  rows : Nat
  width : Nat
deriving Repr, Inhabited

/-- A table with 2 rows of 3 values starting at position 5. -/
example : NetTable := { offset := 5, rows := 2, width := 3 }

/-- The parsed weights file: sizes, observation layout and all weights. -/
structure Net where
  /-- Which observation layout these weights were trained on. -/
  layoutVersion : Nat
  /-- Size of one encoded table row. -/
  E : Nat
  /-- Size of the hidden vector. -/
  hidden : Nat
  /-- Number of MinGRU layers. -/
  layers : Nat
  /-- Number of actions (number of logits). -/
  actSize : Nat
  /-- 0: no pointer scores; 1: spot and link scores; 2: also bank scores. -/
  pointer : Nat
  /-- First action index of the spot scores. -/
  actSpot : Nat
  /-- First action index of the link scores. -/
  actLink : Nat
  /-- First action index of the bank scores. -/
  actBank : Nat
  /-- The observation tables, in order. -/
  tables : Array NetTable
  /-- Table number of the `kinds` table. -/
  kindsIdx : Nat
  /-- Table number of the `spots` table. -/
  spotsIdx : Nat
  /-- Table number of the `links` table. -/
  linksIdx : Nat
  /-- Table number of the `resources` table. -/
  resourcesIdx : Nat
  /-- One input block per table, `E x width`. -/
  wIn : Array FloatArray
  /-- Mixes the pooled tables into one hidden vector, `hidden x (ntables*E)`. -/
  wOut : FloatArray
  /-- Turns the hidden vector into logits, `(act_size+1) x hidden`. -/
  decoder : FloatArray
  /-- Pointer block (empty when `pointer = 0`). -/
  ptr : FloatArray
  /-- One MinGRU block per layer, `(3*hidden) x hidden`. -/
  grus : Array FloatArray

/-- Read the unsigned 32-bit little-endian integer at byte `i`. -/
def u32At (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i+1)).toUInt32 <<< 8) |||
    ((b.get! (i+2)).toUInt32 <<< 16) ||| ((b.get! (i+3)).toUInt32 <<< 24)

#guard u32At (ByteArray.mk #[1, 2, 0, 0]) 0 == 513

/-- Round `n` up to a multiple of 8 (weight blocks are padded this way). -/
def pad8 (n : Nat) : Nat := (n + 7) / 8 * 8

example : pad8 13 = 16 := by decide

/-- Read `n` float32 values starting at byte `pos`, as 64-bit floats. -/
def readFloats (b : ByteArray) (pos n : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    a := a.push (Float32.ofBits (u32At b (pos + 4 * i))).toFloat
  return a

/-- Number of values in one observation (sum of rows * width). -/
def Net.obsSize (n : Net) : Nat :=
  n.tables.foldl (fun acc t => acc + t.rows * t.width) 0

/-- Number of rows in the pointer block: 0, `2E` or `4E`. -/
def ptrRows (pointer e : Nat) : Nat :=
  if pointer == 0 then 0 else if pointer == 1 then 2 * e else 4 * e

/-- Parse a weights file. Fails with a message if the magic, version, sizes
or table numbers are wrong. -/
def Net.read (b : ByteArray) : Except String Net := do
  if b.size < 48 then
    throw s!"weights file: too short for a header ({b.size} bytes)"
  if b.extract 0 4 != "CHPW".toUTF8 then
    throw "weights file: missing magic bytes CHPW"
  let h (k : Nat) : Nat := (u32At b (4 + 4 * k)).toNat
  if h 0 != 1 then throw s!"weights file: format version {h 0}, expected 1"
  let e := h 2; let hid := h 3; let layers := h 4; let act := h 5
  let pointer := h 6; let nt := h 10
  if pointer > 2 then throw s!"weights file: pointer must be 0, 1 or 2, got {pointer}"
  if e == 0 || hid == 0 || nt == 0 then throw "weights file: E, hidden and ntables must be positive"
  let headerBytes := 4 + 4 * (11 + 3 * nt + 4)
  if b.size < headerBytes then
    throw s!"weights file: header needs {headerBytes} bytes, got {b.size}"
  let mut tables : Array NetTable := #[]
  for t in [0:nt] do
    tables := tables.push { offset := h (11 + 3*t), rows := h (12 + 3*t), width := h (13 + 3*t) }
  let idx (k : Nat) := h (11 + 3 * nt + k)
  let kinds := idx 0; let spots := idx 1; let links := idx 2; let res := idx 3
  -- Check the layout.
  let obsSize := tables.foldl (fun acc t => acc + t.rows * t.width) 0
  for t in tables do
    if t.width == 0 then throw "weights file: a table has width 0"
    if t.offset + t.rows * t.width > obsSize then
      throw s!"weights file: table at offset {t.offset} runs past the observation end {obsSize}"
  if pointer > 0 then
    if kinds ≥ nt || spots ≥ nt || links ≥ nt || res ≥ nt then
      throw "weights file: pointer table number out of range"
    let tk := tables[kinds]!; let ts := tables[spots]!; let tl := tables[links]!
    let tr := tables[res]!
    if tk.rows == 0 then throw "weights file: kinds table has no rows"
    if h 7 + (tk.rows - 1) * ts.rows > act then throw "weights file: spot scores run past act_size"
    if h 8 + tl.rows > act then throw "weights file: link scores run past act_size"
    if pointer == 2 && h 9 + tr.rows * tr.rows > act then
      throw "weights file: bank scores run past act_size"
  -- Check the payload size, then read the blocks.
  let pr := ptrRows pointer e
  let inSizes := tables.map (fun t => e * t.width)
  let total := inSizes.foldl (fun acc s => acc + pad8 s) 0 + pad8 (hid * nt * e)
    + pad8 ((act + 1) * hid) + pad8 (pr * hid) + layers * pad8 (3 * hid * hid)
  let expected := headerBytes + 4 * total
  if b.size != expected then
    throw s!"weights file: expected {expected} bytes, got {b.size}"
  let mut pos := headerBytes
  let mut wIn : Array FloatArray := #[]
  for s in inSizes do
    wIn := wIn.push (readFloats b pos s); pos := pos + 4 * pad8 s
  let wOut := readFloats b pos (hid * nt * e); pos := pos + 4 * pad8 (hid * nt * e)
  let dec := readFloats b pos ((act + 1) * hid); pos := pos + 4 * pad8 ((act + 1) * hid)
  let ptr := readFloats b pos (pr * hid); pos := pos + 4 * pad8 (pr * hid)
  let mut grus : Array FloatArray := #[]
  for _ in [0:layers] do
    grus := grus.push (readFloats b pos (3 * hid * hid)); pos := pos + 4 * pad8 (3 * hid * hid)
  return { layoutVersion := h 1, E := e, hidden := hid, layers, actSize := act, pointer,
           actSpot := h 7, actLink := h 8, actBank := h 9, tables,
           kindsIdx := kinds, spotsIdx := spots, linksIdx := links, resourcesIdx := res,
           wIn, wOut, decoder := dec, ptr, grus }

/-- The recurrent state at the start of a game: zeros, one vector per layer. -/
def Net.initState (n : Net) : Array FloatArray :=
  Array.replicate n.layers (FloatArray.mk (Array.replicate n.hidden 0.0))

/-- The logistic function `1 / (1 + e^(-x))`. -/
@[inline] def sigmoid (x : Float) : Float := 1.0 / (1.0 + Float.exp (-x))

/-- Dot product of `n` values: `a[i..i+n]` with `b[j..j+n]`, added to `acc`.
Out-of-range positions count as 0. -/
def dot (a : FloatArray) (i : Nat) (b : FloatArray) (j : Nat) : Nat → Float → Float
  | 0, acc => acc
  | n + 1, acc => dot a (i + 1) b (j + 1) n (acc + a[i]! * b[j]!)

#guard dot (FloatArray.mk #[1, 2, 3]) 1 (FloatArray.mk #[10, 100]) 0 2 0.0 == 320.0

/-- Matrix times vector: `w` has `rows x cols` values, row-major; `x` has
`cols` values. -/
def matVec (w : FloatArray) (rows cols : Nat) (x : FloatArray) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity rows
  for r in [0:rows] do
    out := out.push (dot w (r * cols) x 0 cols 0.0)
  return out

/-- One MinGRU layer. Takes the weights, the input and the old state; returns
the output and the new state. -/
def minGruStep (w : FloatArray) (hid : Nat) (x s : FloatArray) : FloatArray × FloatArray := Id.run do
  let c := matVec w (3 * hid) hid x
  let mut out := FloatArray.emptyWithCapacity hid
  let mut st := FloatArray.emptyWithCapacity hid
  for i in [0:hid] do
    let hv := c[i]!
    let tilde := if hv ≥ 0.0 then hv + 0.5 else sigmoid hv
    let old := s[i]!
    let nw := old + sigmoid c[hid + i]! * (tilde - old)
    let p := sigmoid c[2 * hid + i]!
    out := out.push (p * nw + (1.0 - p) * x[i]!)
    st := st.push nw
  return (out, st)

/-- Encode each table: every row goes through its input block and a ReLU.
Returns the encoded rows of every table (`rows x E`, padding rows included)
and the hidden vector made from the average over the real rows. -/
def Net.encode (n : Net) (obs : FloatArray) : Array FloatArray × FloatArray := Id.run do
  let e := n.E
  let mut keep : Array FloatArray := #[]
  let mut pooled := FloatArray.emptyWithCapacity (n.tables.size * e)
  for ti in [0:n.tables.size] do
    let t := n.tables[ti]!
    let w := n.wIn[ti]!
    let mut r := FloatArray.emptyWithCapacity (t.rows * e)
    let mut sum := FloatArray.mk (Array.replicate e 0.0)
    let mut count := 0
    for row in [0:t.rows] do
      let base := t.offset + row * t.width
      let real := obs[base]! > 0.5
      if real then count := count + 1
      for k in [0:e] do
        let wb := k * t.width
        let s := dot obs base w wb t.width 0.0
        let v := if s > 0.0 then s else 0.0
        r := r.push v
        if real then sum := sum.set! k (sum[k]! + v)
    let d := (max count 1).toFloat
    for k in [0:e] do
      pooled := pooled.push (sum[k]! / d)
    keep := keep.push r
  return (keep, matVec n.wOut n.hidden (n.tables.size * e) pooled)

/-- Add the pointer scores: spot actions score a (kind, spot) pair, link
actions score a link, bank actions score a (give, get) resource pair. -/
def Net.addPointer (n : Net) (keep : Array FloatArray) (h : FloatArray)
    (logits : FloatArray) : FloatArray := Id.run do
  let e := n.E
  let q := matVec n.ptr (ptrRows n.pointer e) n.hidden h
  let rk := keep[n.kindsIdx]!; let rs := keep[n.spotsIdx]!; let rl := keep[n.linksIdx]!
  let nk := n.tables[n.kindsIdx]!.rows; let ns := n.tables[n.spotsIdx]!.rows
  let nl := n.tables[n.linksIdx]!.rows
  let mut out := logits
  for k in [0:nk - 1] do
    let kb := (k + 1) * e
    for v in [0:ns] do
      let vb := v * e
      let mut s := 0.0
      for i in [0:e] do
        s := s + q[i]! * rs[vb + i]! * rk[kb + i]!
      let a := n.actSpot + k * ns + v
      out := out.set! a (out[a]! + s)
  for l in [0:nl] do
    let lb := l * e
    let mut s := 0.0
    for i in [0:e] do
      s := s + rl[lb + i]! * (q[e + i]! * rk[i]!)
    let a := n.actLink + l
    out := out.set! a (out[a]! + s)
  if n.pointer == 2 then
    let rr := keep[n.resourcesIdx]!
    let nr := n.tables[n.resourcesIdx]!.rows
    let mut give := FloatArray.emptyWithCapacity nr
    let mut get := FloatArray.emptyWithCapacity nr
    for i in [0:nr] do
      let mut a := 0.0
      let mut b := 0.0
      for j in [0:e] do
        a := a + rr[i * e + j]! * q[2 * e + j]!
        b := b + rr[i * e + j]! * q[3 * e + j]!
      give := give.push a; get := get.push b
    for i in [0:nr] do
      for j in [0:nr] do
        let a := n.actBank + i * nr + j
        out := out.set! a (out[a]! + (give[i]! + get[j]!))
  return out

/-- Run the network on one observation. Returns the logits (one per action)
and the new recurrent state. Fails if the observation or the state has the
wrong size. -/
def Net.forward (n : Net) (obs : FloatArray) (state : Array FloatArray) :
    Except String (FloatArray × Array FloatArray) := do
  if obs.size != n.obsSize then
    throw s!"forward: observation has {obs.size} values, expected {n.obsSize}"
  if state.size != n.layers || state.any (·.size != n.hidden) then
    throw s!"forward: state must be {n.layers} vectors of size {n.hidden}"
  let (keep, x0) := n.encode obs
  let mut x := x0
  let mut newState : Array FloatArray := #[]
  for li in [0:n.layers] do
    let (y, s2) := minGruStep n.grus[li]! n.hidden x state[li]!
    x := y; newState := newState.push s2
  let y := matVec n.decoder (n.actSize + 1) n.hidden x
  let logits := FloatArray.mk (y.data.extract 0 n.actSize)
  let logits := if n.pointer > 0 then n.addPointer keep x logits else logits
  return (logits, newState)

/-- The legal action with the highest logit. Ties go to the lowest action
index. Indices past the end of `logits` are skipped. `none` if no legal
action is left. -/
def Net.best (_n : Net) (logits : FloatArray) (legal : Array Nat) : Option Nat := Id.run do
  let mut best : Option (Nat × Float) := none
  for a in legal do
    if h : a < logits.size then
      let v := logits[a]
      best := match best with
        | none => some (a, v)
        | some (b, bv) => if v > bv || (v == bv && a < b) then some (a, v) else some (b, bv)
  return best.map (·.1)

end CharterServer.Policy
