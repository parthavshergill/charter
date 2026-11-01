/-!
# SHA-256 (FIPS 180-4) in pure Lean

The message is a plain list of bytes, and every loop is structural recursion or a fold over a
list. So the code runs in the interpreter and also reduces in the kernel. The tests are in
`Charter/Engine/Sha256.lean`: NIST example vectors and padding-boundary vectors.
-/

namespace Charter.Sha256

/-- Round constants (FIPS 180-4 section 4.2.2). -/
def roundConstants : List UInt32 := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The eight working words of the hash. -/
structure Regs where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- Initial hash value (FIPS 180-4 section 5.3.3). -/
def initialRegs : Regs :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The bytes of `n`, most significant first. `count` is how many bytes to write. -/
def natBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, n => natBytes count (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Pad a message (FIPS 180-4 section 5.1.1): `0x80`, zeros, then the bit length in 64 bits. -/
def pad (msg : List UInt8) : List UInt8 :=
  let len := msg.length
  msg ++ [0x80] ++ List.replicate ((119 - len % 64) % 64) 0 ++ natBytes 8 (len * 8)

/-- Group bytes into big-endian 32-bit words. Bytes left over at the end are dropped. -/
def toWords : List UInt8 → List UInt32
  | a :: b :: c :: d :: rest =>
      ((a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32) ::
        toWords rest
  | _ => []

/-- Extend the message schedule by `count` words. The list is newest first. -/
def extendSchedule : Nat → List UInt32 → List UInt32
  | 0, w => w
  | count + 1, w =>
      let next := smallSigma1 (w.getD 1 0) + w.getD 6 0 + smallSigma0 (w.getD 14 0) + w.getD 15 0
      extendSchedule count (next :: w)

/-- The 64-word schedule of a 16-word block, oldest first. -/
def schedule (block : List UInt32) : List UInt32 :=
  (extendSchedule 48 block.reverse).reverse

/-- One compression round. `kw` is the round constant and the schedule word. -/
def round (r : Regs) (kw : UInt32 × UInt32) : Regs :=
  let t1 := r.h + bigSigma1 r.e + ch r.e r.f r.g + kw.1 + kw.2
  let t2 := bigSigma0 r.a + maj r.a r.b r.c
  ⟨t1 + t2, r.a, r.b, r.c, r.d + t1, r.e, r.f, r.g⟩

/-- Process one 16-word block (FIPS 180-4 section 6.2.2). -/
def compress (r : Regs) (block : List UInt32) : Regs :=
  let m := (roundConstants.zip (schedule block)).foldl round r
  ⟨m.a + r.a, m.b + r.b, m.c + r.c, m.d + r.d, m.e + r.e, m.f + r.f, m.g + r.g, m.h + r.h⟩

/-- Compress `count` blocks taken from a list of words. -/
def compressAll : Nat → Regs → List UInt32 → Regs
  | 0, r, _ => r
  | count + 1, r, ws => compressAll count (compress r (ws.take 16)) (ws.drop 16)

/-- The bytes of a word, most significant first. -/
def wordBytes (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The SHA-256 digest of a list of bytes (32 bytes). -/
def hash (msg : List UInt8) : List UInt8 :=
  let padded := pad msg
  let r := compressAll (padded.length / 64) initialRegs (toWords padded)
  [r.a, r.b, r.c, r.d, r.e, r.f, r.g, r.h].flatMap wordBytes

/-- One lowercase hex digit. Only the low four bits of `n` matter. -/
def hexDigit (n : UInt8) : Char :=
  let v := (n &&& 15).toNat
  Char.ofNat (if v < 10 then 48 + v else 87 + v)

/-- Lowercase hexadecimal text of some bytes. -/
def toHex (bytes : List UInt8) : String :=
  String.ofList (bytes.flatMap fun (b : UInt8) => [hexDigit (b >>> 4), hexDigit b])

/-- The digest of a text, in lowercase hexadecimal. Uses the UTF-8 bytes of the text. -/
def hashText (text : String) : String := toHex (hash text.toUTF8.toList)

end Charter.Sha256
