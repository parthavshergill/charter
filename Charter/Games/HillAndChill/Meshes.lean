import GpuCmd

/-! Written by `packs/hill-and-chill/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.HillAndChill.Meshes
open GpuCmd

def boothBody : UInt32 := 100
def boothTint : UInt32 := 101
def potluckBody : UInt32 := 102
def potluckTint : UInt32 := 103
def chatBody : UInt32 := 104
def chatTint : UInt32 := 105
def madeCart : UInt32 := 106
def madePicnic : UInt32 := 107
def madeMic : UInt32 := 108
def tileGas : UInt32 := 109
def tileCash : UInt32 := 110
def tileBoba : UInt32 := 111
def tileTakeout : UInt32 := 112
def tileHill : UInt32 := 113
def hotRing : UInt32 := 114
def tree : UInt32 := 115
def palm : UInt32 := 116
def lamp : UInt32 := 117
def cone : UInt32 := 118
def cup : UInt32 := 119
def picnic : UInt32 := 120
def car : UInt32 := 121
def coin : UInt32 := 122
def flowers : UInt32 := 123
def squareHouse : UInt32 := 124
def squareLights : UInt32 := 125
def monCost : UInt32 := 126
def monPoints : UInt32 := 127
def monBank : UInt32 := 128
def monHarvest : UInt32 := 129
def monBuild : UInt32 := 130
def monRound : UInt32 := 131
def monRoll : UInt32 := 132
def monPiece : UInt32 := 133
def monRepeal : UInt32 := 134
def hillside : UInt32 := 135
def townLights : UInt32 := 136
def hostStand : UInt32 := 137

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "cf2377b772c63adc3cdfab72a74fe62c46eed9a9a494b702c9c00e7a947a1734" 0xE3D1CB { pulse := 0, sway := 0, glow := 0 } (.box 0.3 0.12 0.26)
  , .defineMeshFile 101 "571d085296d7ef446e89948c8afaafe3314a4f33bd484cbbce4af0b3bf7e2c73" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 102 "900d53b67328a612d97b75de62edbaf4bdd17109170d326b2348a70837ebda71" 0xBF9B67 { pulse := 0, sway := 0, glow := 0.25 } (.box 0.44 0.28 0.3)
  , .defineMeshFile 103 "e55163238863be3bcb844c292fb27f48107bf6e3ef8f7f1a466b75be0f3ef92e" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 104 "b1230c9a96ca1738f086f2c05e055fbe1a676067327ef103291e7beb5fc893ce" 0x373640 { pulse := 0, sway := 0.02, glow := 0 } (.box 0.6 0.14 0.05)
  , .defineMeshFile 105 "15639d908edd66d563aa3879a956390b87a236d16813e154edaeb520d83ff6ee" 0xFFFFFF { pulse := 0, sway := 0.02, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 106 "a4289300f33b8e44514e374502581ea97344277bbac4da2742289d4e56c70ee5" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.box 0.2 0.25 0.12)
  , .defineMeshFile 107 "815339768b12a8135abbc73440471864c395d8e0513fe40df3faa319f3884b08" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.box 0.26 0.07 0.22)
  , .defineMeshFile 108 "8a497df432877b37c0c0b369605af337de742c114c6a6ce16561c3271ba33fb7" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.08 0.25)
  , .defineMeshFile 109 "08219b47e262007a9aba817d1dc8a61b02a3805f41f7518d2a6c1cc6e86457d7" 0x5C5D5D { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 110 "1b4cc95c4b54b2744b54cfb25ffadc01603c3dce1bbef4ef2d878b3d617fa854" 0x96B067 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 111 "9ce0614dac07aaff9e4e309caa1c26c65f75281b0b405e9ac94b40f337517b8d" 0xC7B4AB { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 112 "936aa12ba307ecd1b02cb8f3e4f9e349e817268e7014db5d7ef2b0766fc4288e" 0xA78D5A { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 113 "d2310a3bf9caeb4f10b060da102429498d51e22d06c2e9ebf6cfd096f86b5e7e" 0x729D52 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 114 "6f05439f8692eb030660c81f0a4ef3b7ab028ea38fc352916ea69b25fea40b91" 0xFFE45C { pulse := 0, sway := 0, glow := 0.7 } (.sphere 0.001)
  , .defineMeshFile 115 "766d4919519c64e75ba0148d38a8f89d52a5fd0acda04c2d281fee2c2899936b" 0x718442 { pulse := 0, sway := 0.02, glow := 0 } (.cone 0.05 0.16)
  , .defineMeshFile 116 "638af860c195536b04490420bdc39e4efa1e5533cbde9b1a2604b95b1bc00a40" 0x5E8F43 { pulse := 0, sway := 0.03, glow := 0 } (.cone 0.06 0.28)
  , .defineMeshFile 117 "31907c5fbeb0d070f7324ae78c25d27d7675c393086bea16f29d1ac1d772dfa7" 0x88724F { pulse := 0, sway := 0, glow := 0.2 } (.cone 0.02 0.2)
  , .defineMeshFile 118 "34fb6bae1211891e8bcc5a428666d7459741bc3ef84ff83ae773e18f17b6fb78" 0xF39E78 { pulse := 0, sway := 0, glow := 0 } (.cone 0.02 0.05)
  , .defineMeshFile 119 "b8b909cfd98c04ba67504ff185e6e88c4038d11af0be8ce2cb2f2ebeedf4d9d0" 0xE6BFBE { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.025 0.07)
  , .defineMeshFile 120 "e052c2ac046c8fe7cea48355b11f4c0ec439ec23d2d7eb600311bf6a7e76c906" 0x97663A { pulse := 0, sway := 0, glow := 0 } (.box 0.12 0.05 0.12)
  , .defineMeshFile 121 "e724744bf06ede9b062dd7b7e2d211578b2fc6d93a9dc01e4bcaf3dbd653941f" 0x5F646F { pulse := 0, sway := 0, glow := 0 } (.box 0.16 0.08 0.08)
  , .defineMeshFile 122 "6c00d3b0839583ebb6b454b2076f9b85264b60df5588ee6eceafcba8d0081458" 0xF8D55D { pulse := 0, sway := 0, glow := 0.3 } (.cylinder 0.03 0.01)
  , .defineMeshFile 123 "cf3ec6b485b17907e2ff78a41e8dcca36f3ed44175b9aad915be0bf0a72ca378" 0xCB9481 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 124 "a1eebbbfa1d5cfd3f522ea58f4ccb955fdb9f740969d9f4cb3b1943210c1c275" 0xC6A07A { pulse := 0, sway := 0, glow := 0 } (.box 0.4 0.3 0.4)
  , .defineMeshFile 125 "88ff67b3a1990ec79aa20c73dbdb3db573e7e5c8ba18f9452298bffb462f0ed1" 0xCAAEA2 { pulse := 0, sway := 0, glow := 0.5 } (.sphere 0.001)
  , .defineMeshFile 126 "0571ae922bdba8786b7ac016f94f56662e6353c2ba4cf70021475a59c1e752b6" 0x938267 { pulse := 0, sway := 0, glow := 0 } (.cone 0.08 0.26)
  , .defineMeshFile 127 "8b3897c3debfa021558c47d361a9db9514ae32c8b867c932fd6f6b9afa21d518" 0xD0B45C { pulse := 0, sway := 0, glow := 0.2 } (.cylinder 0.06 0.2)
  , .defineMeshFile 128 "07f32110765a1bc70eb0e80408df03fd925cf859cad123856a950c396b69c382" 0x92AA94 { pulse := 0, sway := 0, glow := 0.2 } (.box 0.11 0.22 0.08)
  , .defineMeshFile 129 "64addbaf2694548e2711560c4424d139ec202c3374d06f00575e9751a332f059" 0xC79574 { pulse := 0, sway := 0, glow := 0 } (.box 0.1 0.16 0.07)
  , .defineMeshFile 130 "221026038dcd0ff6136bef2fda62dc317219b4dfb85a01c9c1863f0c0638fc77" 0xDAB084 { pulse := 0, sway := 0, glow := 0 } (.cone 0.07 0.16)
  , .defineMeshFile 131 "a8e2e5c651f8c404bc089720953c2c10341bbea5d9701f189bcea14bb4042521" 0xAFA693 { pulse := 0, sway := 0, glow := 0.3 } (.sphere 0.06)
  , .defineMeshFile 132 "b0032fe50b33593944c65b30c26a4ca7344ae7731956469a06fe43827aa92b52" 0xE4BFAD { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.07 0.16)
  , .defineMeshFile 133 "bcaf8149737859288906253457a5dc29ab956c88bdbfe2a2bfbe5071925e8db2" 0x96737D { pulse := 0, sway := 0, glow := 0.4 } (.box 0.17 0.2 0.04)
  , .defineMeshFile 134 "f2507d4fec4e55131f9c2d7f7d1949f2d9273e83172c2c99fab96ab06981525d" 0xB99E92 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.05 0.25)
  , .defineMeshFile 135 "e432c1086b6373c33b1ac3603d981d27522e25013f9152539bda7dfbaca4241f" 0x262E3A { pulse := 0, sway := 0, glow := 0 } (.box 40 0.01 40)
  , .defineMeshFile 136 "e51c39b9ccc7c77b4402376538e403aac6ba09d3201e040b7fead032374a6605" 0xE7C088 { pulse := 0, sway := 0, glow := 0.35 } (.sphere 0.001)
  , .defineMeshFile 137 "24eaf9a71bcec0598a28a444a70540e0faa956161a2d47982c60bfae7f4c3c0d" 0xAC8E6C { pulse := 0, sway := 0, glow := 0 } (.box 0.9 0.45 0.6) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 152), (101, 40), (102, 530), (103, 30), (104, 226), (105, 144), (106, 64), (107, 44), (108, 74), (109, 1334), (110, 1480), (111, 1500), (112, 1520), (113, 1188), (114, 12), (115, 36), (116, 36), (117, 40), (118, 42), (119, 56), (120, 30), (121, 84), (122, 48), (123, 52), (124, 216), (125, 88), (126, 64), (127, 98), (128, 58), (129, 56), (130, 94), (131, 108), (132, 58), (133, 64), (134, 44), (135, 4352), (136, 3310), (137, 308) ]

end Charter.Games.HillAndChill.Meshes
