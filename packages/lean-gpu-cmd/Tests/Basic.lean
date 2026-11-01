import GpuCmd
open GpuCmd

def sample : List Cmd :=
  [.clear 0x112233,
   .camera (vec3 1 2 3) (vec3 0 0 0) 45,
   .light (vec3 (-0.5) (-1) 0.25) 1.5,
   .defineMesh 7 (.hexPrism 1 0.2), .defineMesh 8 (.box 1 2 3), .defineMesh 9 (.cylinder 0.5 1),
   .defineMesh 10 (.cone 0.5 1), .defineMesh 11 (.sphere 0.3), .defineMesh 12 (.house 1 1 1),
   .draw 7 { pos := vec3 1.5 0 (-2), rotY := 0.5, scale := vec3 1 2 1 } 0x80FF0000 42,
   .label "Grüße · 6 ⚑" (vec3 0 1 0) 0.5 0xFFFFFF 3,
   .label (String.ofList (List.replicate 300 'x')) (vec3 0 0 0) 1 0 0,
   .highlight 42 0xFFD700]

-- round trip (also proved as `decode_encode`)
#guard decode (encode sample) == some sample
#guard decode (encode []) == some []

-- golden bytes: magic, opcode, little-endian u32
#guard (encode [.clear 0x112233]).toList == [0x47, 0x50, 0x43, 0x31, 1, 0x33, 0x22, 0x11, 0x00]
#guard (encode [.highlight 1 0xAABBCCDD]).toList ==
  [0x47, 0x50, 0x43, 0x31, 7, 1, 0, 0, 0, 0xDD, 0xCC, 0xBB, 0xAA]
-- f32 bit patterns
#guard (1.0 : F32).bits == 0x3F800000
#guard (-2.5 : F32).bits == 0xC0200000
#guard (0.1 : F32).bits == 0x3DCCCCCD
#guard (0.1 : F32).toFloat == 0.10000000149011612
-- ULEB128 lengths
#guard Wire.uleb 0 == [0]
#guard Wire.uleb 127 == [0x7F]
#guard Wire.uleb 128 == [0x80, 0x01]
#guard Wire.uleb 300 == [0xAC, 0x02]
#guard (encode [.label "é" (vec3 0 0 0) 1 0 0]).toList.take 8 == [0x47, 0x50, 0x43, 0x31, 6, 2, 0xC3, 0xA9]
-- command sizes match WIRE.md
#guard (cmdBytes (.draw 1 { pos := vec3 0 0 0 } 0 0)).length == 41
#guard (cmdBytes (.camera (vec3 0 0 0) (vec3 0 0 0) 1)).length == 29
#guard (cmdBytes (.light (vec3 0 0 0) 1)).length == 17
#guard (cmdBytes (.label "" (vec3 0 0 0) 1 0 0)).length == 26
-- rejection: bad magic, truncation, unknown opcode, invalid UTF-8
#guard decode ⟨#[0x47, 0x50, 0x43, 0x32]⟩ == none
#guard decode ⟨#[0x47, 0x50, 0x43, 0x31, 1, 0, 0]⟩ == none
#guard decode ⟨#[0x47, 0x50, 0x43, 0x31, 99]⟩ == none
#guard decode ⟨#[0x47, 0x50, 0x43, 0x31, 6, 1, 0xFF] ++ (List.replicate 24 (0 : UInt8)).toArray⟩ == none
-- alpha helper
#guard withAlpha 0x123456 1 == 0x00123456
#guard withAlpha 0x123456 0 == 0xFF123456
