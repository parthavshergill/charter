import GpuCmd.Wire

/-!
# Command stream encoder and decoder

Stream = magic `"GPC1"` followed by commands back to back until the end of the
input. See `WIRE.md` for the byte layout.
-/

namespace GpuCmd
open Wire

def vec3Bytes (v : Vec3) : List UInt8 := f32 v.x ++ f32 v.y ++ f32 v.z

def readVec3 (bs : List UInt8) : Option (Vec3 × List UInt8) := do
  let (x, bs) ← readF32 bs
  let (y, bs) ← readF32 bs
  let (z, bs) ← readF32 bs
  pure (⟨x, y, z⟩, bs)

theorem readVec3_vec3Bytes (v : Vec3) (rest : List UInt8) :
    readVec3 (vec3Bytes v ++ rest) = some (v, rest) := by
  simp [readVec3, vec3Bytes, List.append_assoc, readF32_f32]

def transformBytes (t : Transform) : List UInt8 :=
  vec3Bytes t.pos ++ f32 t.rotY ++ vec3Bytes t.scale

def readTransform (bs : List UInt8) : Option (Transform × List UInt8) := do
  let (pos, bs) ← readVec3 bs
  let (rotY, bs) ← readF32 bs
  let (scale, bs) ← readVec3 bs
  pure (⟨pos, rotY, scale⟩, bs)

theorem readTransform_transformBytes (t : Transform) (rest : List UInt8) :
    readTransform (transformBytes t ++ rest) = some (t, rest) := by
  simp [readTransform, transformBytes, List.append_assoc, readVec3_vec3Bytes, readF32_f32]

def motionBytes (m : Motion) : List UInt8 := f32 m.pulse ++ f32 m.sway ++ f32 m.glow

def readMotion (bs : List UInt8) : Option (Motion × List UInt8) := do
  let (pulse, bs) ← readF32 bs
  let (sway, bs) ← readF32 bs
  let (glow, bs) ← readF32 bs
  pure (⟨pulse, sway, glow⟩, bs)

theorem readMotion_motionBytes (m : Motion) (rest : List UInt8) :
    readMotion (motionBytes m ++ rest) = some (m, rest) := by
  simp [readMotion, motionBytes, List.append_assoc, readF32_f32]

def primBytes : Prim → List UInt8
  | .hexPrism r h => u8 1 ++ f32 r ++ f32 h
  | .box w h d => u8 2 ++ f32 w ++ f32 h ++ f32 d
  | .cylinder r h => u8 3 ++ f32 r ++ f32 h
  | .cone r h => u8 4 ++ f32 r ++ f32 h
  | .sphere r => u8 5 ++ f32 r
  | .house w h d => u8 6 ++ f32 w ++ f32 h ++ f32 d
  | .gable w h d => u8 7 ++ f32 w ++ f32 h ++ f32 d
  | .pyramid r h => u8 8 ++ f32 r ++ f32 h

def readPrim : List UInt8 → Option (Prim × List UInt8)
  | [] => none
  | t :: bs =>
    match t.toNat with
    | 1 => do
      let (r, bs) ← readF32 bs; let (h, bs) ← readF32 bs
      pure (.hexPrism r h, bs)
    | 2 => do
      let (w, bs) ← readF32 bs; let (h, bs) ← readF32 bs; let (d, bs) ← readF32 bs
      pure (.box w h d, bs)
    | 3 => do
      let (r, bs) ← readF32 bs; let (h, bs) ← readF32 bs
      pure (.cylinder r h, bs)
    | 4 => do
      let (r, bs) ← readF32 bs; let (h, bs) ← readF32 bs
      pure (.cone r h, bs)
    | 5 => do
      let (r, bs) ← readF32 bs
      pure (.sphere r, bs)
    | 6 => do
      let (w, bs) ← readF32 bs; let (h, bs) ← readF32 bs; let (d, bs) ← readF32 bs
      pure (.house w h d, bs)
    | 7 => do
      let (w, bs) ← readF32 bs; let (h, bs) ← readF32 bs; let (d, bs) ← readF32 bs
      pure (.gable w h d, bs)
    | 8 => do
      let (r, bs) ← readF32 bs; let (h, bs) ← readF32 bs
      pure (.pyramid r h, bs)
    | _ => none

theorem readPrim_primBytes (p : Prim) (rest : List UInt8) :
    readPrim (primBytes p ++ rest) = some (p, rest) := by
  cases p <;> simp [readPrim, primBytes, u8, List.append_assoc, readF32_f32]

/-- Bytes of one command (first byte = opcode). -/
def cmdBytes : Cmd → List UInt8
  | .clear rgb => u8 1 ++ u32 rgb
  | .camera eye target fov => u8 2 ++ vec3Bytes eye ++ vec3Bytes target ++ f32 fov
  | .light dir i => u8 3 ++ vec3Bytes dir ++ f32 i
  | .defineMesh id p => u8 4 ++ u32 id ++ primBytes p
  | .draw m t rgb pick => u8 5 ++ u32 m ++ transformBytes t ++ u32 rgb ++ u32 pick
  | .label s pos size rgb pick => u8 6 ++ str s ++ vec3Bytes pos ++ f32 size ++ u32 rgb ++ u32 pick
  | .highlight pick rgb => u8 7 ++ u32 pick ++ u32 rgb
  | .defineMeshFile id sha tint m p => u8 8 ++ u32 id ++ str sha ++ u32 tint ++ motionBytes m ++ primBytes p

def readCmd : List UInt8 → Option (Cmd × List UInt8)
  | [] => none
  | t :: bs =>
    match t.toNat with
    | 1 => do
      let (rgb, bs) ← readU32 bs
      pure (.clear rgb, bs)
    | 2 => do
      let (eye, bs) ← readVec3 bs; let (target, bs) ← readVec3 bs; let (fov, bs) ← readF32 bs
      pure (.camera eye target fov, bs)
    | 3 => do
      let (dir, bs) ← readVec3 bs; let (i, bs) ← readF32 bs
      pure (.light dir i, bs)
    | 4 => do
      let (id, bs) ← readU32 bs; let (p, bs) ← readPrim bs
      pure (.defineMesh id p, bs)
    | 5 => do
      let (m, bs) ← readU32 bs; let (tr, bs) ← readTransform bs
      let (rgb, bs) ← readU32 bs; let (pick, bs) ← readU32 bs
      pure (.draw m tr rgb pick, bs)
    | 6 => do
      let (s, bs) ← readStr bs; let (pos, bs) ← readVec3 bs; let (size, bs) ← readF32 bs
      let (rgb, bs) ← readU32 bs; let (pick, bs) ← readU32 bs
      pure (.label s pos size rgb pick, bs)
    | 7 => do
      let (pick, bs) ← readU32 bs; let (rgb, bs) ← readU32 bs
      pure (.highlight pick rgb, bs)
    | 8 => do
      let (id, bs) ← readU32 bs; let (sha, bs) ← readStr bs; let (tint, bs) ← readU32 bs
      let (m, bs) ← readMotion bs; let (p, bs) ← readPrim bs
      pure (.defineMeshFile id sha tint m p, bs)
    | _ => none

theorem readCmd_cmdBytes (c : Cmd) (rest : List UInt8) :
    readCmd (cmdBytes c ++ rest) = some (c, rest) := by
  cases c <;> simp [readCmd, cmdBytes, u8, List.append_assoc, readU32_u32, readF32_f32,
    readVec3_vec3Bytes, readTransform_transformBytes, readPrim_primBytes, readStr_str,
    readMotion_motionBytes]

theorem cmdBytes_ne_nil (c : Cmd) : cmdBytes c ≠ [] := by
  cases c <;> simp [cmdBytes, u8]

/-- Stream magic: ASCII `GPC1`. -/
def magic : List UInt8 := [0x47, 0x50, 0x43, 0x31]

/-- Concatenated command bytes, without the magic. -/
def cmdsBytes (cs : List Cmd) : List UInt8 := cs.flatMap cmdBytes

/-- Decode commands until the input ends. `fuel` bounds the number of commands. -/
def readCmds : Nat → List UInt8 → Option (List Cmd)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bs@(_ :: _) => do
    let (c, r) ← readCmd bs
    let cs ← readCmds fuel r
    pure (c :: cs)

/-- Full stream over `List UInt8`: magic, then commands. -/
def encodeList (cs : List Cmd) : List UInt8 := magic ++ cmdsBytes cs

def decodeList (bs : List UInt8) : Option (List Cmd) :=
  if bs.take 4 = magic then readCmds (bs.length - 4) (bs.drop 4) else none

theorem readCmds_cmdsBytes (cs : List Cmd) (fuel : Nat) (h : cs.length ≤ fuel) :
    readCmds fuel (cmdsBytes cs) = some cs := by
  induction cs generalizing fuel with
  | nil => simp [cmdsBytes, readCmds]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have hne := cmdBytes_ne_nil c
      obtain ⟨b, bs, hb⟩ : ∃ b bs, cmdBytes c ++ cmdsBytes cs = b :: bs := by
        cases hc : cmdBytes c with
        | nil => exact absurd hc hne
        | cons b bs => exact ⟨b, bs ++ cmdsBytes cs, rfl⟩
      have hcs : cmdsBytes (c :: cs) = cmdBytes c ++ cmdsBytes cs := by simp [cmdsBytes]
      rw [hcs, hb, readCmds, ← hb, readCmd_cmdBytes]
      simp [ih fuel (by simp at h; omega)]

theorem cmdsBytes_length_ge (cs : List Cmd) : cs.length ≤ (cmdsBytes cs).length := by
  induction cs with
  | nil => simp [cmdsBytes]
  | cons c cs ih =>
    have := cmdBytes_ne_nil c
    have : 1 ≤ (cmdBytes c).length := by
      cases h : cmdBytes c with
      | nil => contradiction
      | cons => simp
    simp only [cmdsBytes, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

/-- **Round trip** over bytes: decoding an encoded stream returns the commands. -/
theorem decodeList_encodeList (cs : List Cmd) : decodeList (encodeList cs) = some cs := by
  have hm : magic.length = 4 := rfl
  simp only [decodeList, encodeList, List.take_append_of_le_length (by simp [hm] : 4 ≤ magic.length),
    List.length_append, hm]
  simp only [List.take_of_length_le (by simp [hm] : magic.length ≤ 4), ↓reduceIte,
    Nat.add_sub_cancel_left]
  rw [show (magic ++ cmdsBytes cs).drop 4 = cmdsBytes cs from List.drop_left' hm]
  exact readCmds_cmdsBytes cs _ (cmdsBytes_length_ge cs)

/-- Encode a scene to bytes (send these to `web/player.js`). -/
def encode (cs : List Cmd) : ByteArray := ⟨(encodeList cs).toArray⟩

def decode (b : ByteArray) : Option (List Cmd) := decodeList b.data.toList

/-- **Round trip** on `ByteArray`. -/
theorem decode_encode (cs : List Cmd) : decode (encode cs) = some cs := by
  simp [decode, encode, decodeList_encodeList]

end GpuCmd
