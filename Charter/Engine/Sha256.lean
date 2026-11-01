import Charter.Sha256

/-!
# Tests of SHA-256

The definition is in `Charter/Sha256.lean`, because the spec uses it. These `#guard`s fail the
build if it is wrong.
-/

namespace Charter.Sha256

/-! ## Tests: NIST FIPS 180-4 example vectors -/

#guard hashText "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hashText "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hashText "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard hashText ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
    "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"

#guard toHex (hash (List.replicate 1000000 97)) ==
  "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

/-! ## Tests: padding boundaries

The message of length `n` has byte `i = (7i + 3) mod 256`. The digests come from Python's
`hashlib.sha256`. -/

def pattern (n : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat ((7 * i + 3) % 256)

#guard toHex (hash (pattern 1)) ==
  "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5"
#guard toHex (hash (pattern 55)) ==
  "e7313d333c272e639f790978283f9eb392e843d0f29b7016828bb1daa4aac70b"
#guard toHex (hash (pattern 56)) ==
  "4324d65f3c103567f5589c710bc08f8523f929a9272e3af36fc968e52abc6c27"
#guard toHex (hash (pattern 57)) ==
  "35df609437dcfea3279283ab79fd554e2bf78f8f7ae2de532d8ee300b09e8f73"
#guard toHex (hash (pattern 63)) ==
  "81c80242132f230c3bd41b3e63bbcff16107339549214a99614ff26664625055"
#guard toHex (hash (pattern 64)) ==
  "39e3d7b6b5d075d37d053ad89b24b41bef4f3c29760c84447cab3f3be1882241"
#guard toHex (hash (pattern 65)) ==
  "aacca6ff74fdbb296d165a45cecfa04e5127bc008770fbbdd48006f2d2fae95e"
#guard toHex (hash (pattern 119)) ==
  "9ce7368e4daf32341631b492e80359dc9f594b48453cd0dd5bf0b19279cc177e"
#guard toHex (hash (pattern 120)) ==
  "7836b787757e95e58b3ca5aec90b1b004e8deba1e50e9675af9cabf1a13a04b5"
#guard toHex (hash (pattern 127)) ==
  "a8d23e75d936f303d248888d9b165ee543f4cbafcad3c9dd2a79bd84faa11d07"
#guard toHex (hash (pattern 128)) ==
  "d2742f1f4ac6bb7ca2b239ee18402ba8b3f9f8e652d2a72973c2b9ba11c08cf6"
#guard toHex (hash (pattern 1000)) ==
  "1e9bc38cbf860b9ec31918b065f9b52476c549a782e0e7990bed8ce3868d2371"
#guard toHex (hash (pattern 4096)) ==
  "7486da8f1e13943fae21a0b043f1e99640d7d8ebafb25266478b5cddae1272b5"

end Charter.Sha256
