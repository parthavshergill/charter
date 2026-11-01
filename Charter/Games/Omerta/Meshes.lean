import GpuCmd

/-! Written by `packs/omerta/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.Omerta.Meshes
open GpuCmd

def streetTint : UInt32 := 100
def streetBody : UInt32 := 101
def sedan : UInt32 := 102
def frontBody : UInt32 := 103
def frontTint : UInt32 := 104
def clubBody : UInt32 := 105
def clubTint : UInt32 := 106
def clubNeon : UInt32 := 107
def racketBody : UInt32 := 108
def racketTint : UInt32 := 109
def madeBooth : UInt32 := 110
def madeKiosk : UInt32 := 111
def madeTruck : UInt32 := 112
def barricade : UInt32 := 113
def tileWine : UInt32 := 114
def tileCement : UInt32 := 115
def tileFish : UInt32 := 116
def tilePiazza : UInt32 := 117
def hotRing : UInt32 := 118
def lampPost : UInt32 := 119
def lampGlow : UInt32 := 120
def decoBags : UInt32 := 121
def decoCrates : UInt32 := 122
def cashBundle : UInt32 := 123
def squareFountain : UInt32 := 124
def squareWater : UInt32 := 125
def monCost : UInt32 := 126
def monPoints : UInt32 := 127
def monBank : UInt32 := 128
def monHarvest : UInt32 := 129
def monBuild : UInt32 := 130
def monRound : UInt32 := 131
def monRoll : UInt32 := 132
def monPiece : UInt32 := 133
def monRepeal : UInt32 := 134
def cityGround : UInt32 := 135
def skyline : UInt32 := 136
def harbour : UInt32 := 137
def policeCar : UInt32 := 138
def policeLight : UInt32 := 139
def daDesk : UInt32 := 140
def daLamp : UInt32 := 141

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "0474bc683812a30dcbe5becc52686ed1cceb5cca1de22fb40239dcb2f55510db" 0xEBEBEB { pulse := 0, sway := 0, glow := 0 } (.box 0.62 0.014 0.13)
  , .defineMeshFile 101 "1001c2b116624f827b7d4032ac1008a30fea589b7b0dcc657316c3fe145cd673" 0x8A847A { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 102 "789c9231eb05a16a4b5b087fa275744712bc2744451c1aaeca414c05c2532817" 0xAEA09E { pulse := 0, sway := 0, glow := 0 } (.box 0.2 0.07 0.085)
  , .defineMeshFile 103 "6ce2a507c9a52cdb277fab518f8912c1db71e70b0103b2e20b86cafef7feed75" 0x7B6241 { pulse := 0, sway := 0, glow := 0 } (.box 0.17 0.2 0.17)
  , .defineMeshFile 104 "993b478ac2acd059aa76bdaf360d98d5172d7eb040fca0264172d224a7e65001" 0xE3E3E3 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 105 "f45504055dca85345494c7bfb0c916bf8cc186e35bd41f3c8c57f784f6d77e95" 0xC19D6E { pulse := 0, sway := 0, glow := 0 } (.box 0.28 0.25 0.22)
  , .defineMeshFile 106 "124d32239d549a4d9ac561a3d60fdda0ce64916d25fe9615922c2868b6117cbd" 0xECECEC { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 107 "dfc76bcda5a66b55c8a93ac19c35b83db5e2a92eded205fe7b5d750a9dada080" 0xE5E5E5 { pulse := 0, sway := 0, glow := 0.55 } (.sphere 0.001)
  , .defineMeshFile 108 "9340afa27f6634ff17fa91c82d0f30ce6fd6377837f7dd8c524ecaf9c31d1524" 0x9B7361 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.12 0.12)
  , .defineMeshFile 109 "adfda13512eb37d72e05fe6c3e8129e5d163593ec907b835734f5b155ed06a04" 0xF7F7F7 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 110 "0f17111eabc3daf8156ccc30f05abba2963dbadf9a386a777310d768d3e4888f" 0x9F9B91 { pulse := 0, sway := 0, glow := 0 } (.box 0.08 0.22 0.08)
  , .defineMeshFile 111 "41a716d540a6fbe1b638ce9bdb3b16a4cf4e813adbd06a9c67ca93eeb10e0d69" 0xDED9CC { pulse := 0, sway := 0, glow := 0 } (.box 0.18 0.15 0.12)
  , .defineMeshFile 112 "b787429eac2719b61f2f1aa1b38d6455b4e82e9217b60a9b85ba87d380c22764" 0x7E7E80 { pulse := 0, sway := 0, glow := 0 } (.box 0.24 0.14 0.1)
  , .defineMeshFile 113 "e4fdd86bf41e633c3220c5673dedff4cc222ea18978e28b4896a24f57c79434a" 0x757575 { pulse := 0, sway := 0, glow := 0 } (.box 0.56 0.11 0.08)
  , .defineMeshFile 114 "a054560c58c82de0c96781b51d2719a3168061098af61fe095cf757cd112b8a3" 0x5D5138 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 115 "191e0996a76b78623aa97aeb16a4f14846f93ccfbb54fad21c277d3208208014" 0x9A8667 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 116 "195d20cc439f4341762ecf252db1e33ac0e8e79f1f773e7e5add83751d8839d6" 0x6A6053 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 117 "f263737030c25c842f4f6efaef8c7daa61545dec3f5245ae351d5a1db5c6da92" 0xA29376 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.16)
  , .defineMeshFile 118 "a85011179d0fe4bbe39636419909f81f830147fbe86ef3858f8bd2536a114d5d" 0xFFD379 { pulse := 0, sway := 0, glow := 0.7 } (.sphere 0.001)
  , .defineMeshFile 119 "47ecb60e9fa67bd7c40ba5536d6cf4d25386ee92d28dd45fcce9345c3689f1bb" 0x24262B { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.01 0.26)
  , .defineMeshFile 120 "c3ee6a3aadd9f7461a46d16629511d50aa984705fba22fbbfea2cc4b78bfc980" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.45 } (.sphere 0.001)
  , .defineMeshFile 121 "cc140ad9096003b813c6142de11d9f98017b28ba72a3bdfc8d2ac9419f1b371d" 0xDBD1B7 { pulse := 0, sway := 0, glow := 0 } (.box 0.07 0.045 0.06)
  , .defineMeshFile 122 "112a2359ddab2d53bc90c7d120485059d0a782df9b59bf1f840f42a256d2cce5" 0x9F988B { pulse := 0, sway := 0, glow := 0 } (.box 0.06 0.06 0.045)
  , .defineMeshFile 123 "e45cd82d48b5585f5b3e7c307da144d0a8fd44781f392f7addb44033de9e9c60" 0x9BC282 { pulse := 0, sway := 0, glow := 0 } (.box 0.062 0.03 0.12)
  , .defineMeshFile 124 "14e04ab28756cfdb84172db6f94a1a63413ad14f9aedcb329d383ab098fad5b8" 0x9FA296 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.2 0.28)
  , .defineMeshFile 125 "d67e0c9d25247ba7e4d38306ab520fac117136dba74c5b4528b59e61b460b5e4" 0xB8E0F0 { pulse := 0.08, sway := 0, glow := 0.3 } (.sphere 0.001)
  , .defineMeshFile 126 "158967f5cc6b6f20a79dac1a76752a949e6cedc3883585d122c1690f77f4541e" 0xC2B69A { pulse := 0, sway := 0, glow := 0 } (.box 0.1 0.15 0.08)
  , .defineMeshFile 127 "c86190d1235868db31f104eebf7d2d1f33cd4073dcd0bf62181a456c84b2c111" 0xC4A760 { pulse := 0, sway := 0, glow := 0 } (.cone 0.06 0.17)
  , .defineMeshFile 128 "f5756e5fd3f1d5b12edcb64cbac92b1d6e4699750f30e029089028463d5118b3" 0xA69261 { pulse := 0, sway := 0, glow := 0 } (.box 0.1 0.15 0.09)
  , .defineMeshFile 129 "1d5bdf10d5dc684b8fd6ddcfd7724552e4ab047386fbbee3797db778bce99e56" 0x6D5B4A { pulse := 0, sway := 0, glow := 0 } (.box 0.12 0.12 0.08)
  , .defineMeshFile 130 "8a1446d25a56400cb3d5b76083a53b247769438acb0666d3e61ee71c2af5dd73" 0xC99147 { pulse := 0, sway := 0, glow := 0 } (.box 0.06 0.2 0.06)
  , .defineMeshFile 131 "6bb684152130f51e08a54372deea0ba07148b5d42567348c8ef3f94a3af2fd73" 0x8D897F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.04 0.25)
  , .defineMeshFile 132 "b7c15c994f2cbf42c2caf5c2b66839853de559111c6775edc670f63276c085bc" 0xA28979 { pulse := 0, sway := 0, glow := 0 } (.box 0.1 0.06 0.1)
  , .defineMeshFile 133 "a20b35c81f66b440a80c0434c935188670f5e585fa4602a10da95b9510953c05" 0xAE8366 { pulse := 0, sway := 0, glow := 0 } (.box 0.08 0.15 0.08)
  , .defineMeshFile 134 "d69929028746b208feb6e2904391a952e7cc826b20cb5c83934b249426edb11a" 0xC8C1B2 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.04 0.14)
  , .defineMeshFile 135 "8a646580f6943dea3139e2b4c87314c0d83a5c3629066139303125778fdfca51" 0x292B28 { pulse := 0, sway := 0, glow := 0 } (.box 26 0.01 26)
  , .defineMeshFile 136 "0ec7766f6a76c0dd4aba8ae4b5c8ba23c15464e785586867c3ffbbefac4f5fa5" 0x6E5639 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 137 "06ec86f19068935d974a30529dbcb01af73b4e9caccc2bcb9bcc201b2dfaa3ac" 0x675346 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 138 "0b3d0bebf34d10d7666cf10f413baa1916c0f3aa80260d05d4b9b10a86f25549" 0x595752 { pulse := 0, sway := 0, glow := 0 } (.box 0.2 0.07 0.09)
  , .defineMeshFile 139 "c85221893f5e9fa27bf8d310117b3a826ebc91579b159ea7106cf7dc9f9d89a6" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.9 } (.sphere 0.001)
  , .defineMeshFile 140 "6696b7cca74b4658cd9ddd044a899011192ef97bc164fb418a37abbdf104a82d" 0x907045 { pulse := 0, sway := 0, glow := 0 } (.box 0.6 0.35 1.3)
  , .defineMeshFile 141 "c58301a6cda99d4ad134ec1e930161a64cdee08c413ec7767ff7bc9d7236ffd9" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.5 } (.sphere 0.001) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 32), (101, 30), (102, 76), (103, 88), (104, 144), (105, 202), (106, 80), (107, 60), (108, 224), (109, 46), (110, 38), (111, 48), (112, 30), (113, 92), (114, 1122), (115, 1152), (116, 1104), (117, 984), (118, 12), (119, 30), (120, 16), (121, 30), (122, 30), (123, 20), (124, 162), (125, 48), (126, 112), (127, 116), (128, 68), (129, 150), (130, 98), (131, 160), (132, 60), (133, 68), (134, 82), (135, 2408), (136, 892), (137, 628), (138, 72), (139, 10), (140, 440), (141, 12) ]

/-- Where each bundle of cash lies on the desk, in order: x, y, z and a turn. -/
def cashSlots : List (Float × Float × Float × Float) :=
  [ ((-0.0330), 0.3270, (-0.1425), (-0.0035))
  , ((-0.0330), 0.3270, (-0.0175), 0.0097)
  , (0.0330, 0.3270, (-0.1425), 0.0256)
  , (0.0330, 0.3270, (-0.0175), (-0.0048))
  , (0.0000, 0.3580, (-0.0800), (-0.0096))
  , ((-0.0990), 0.3270, (-0.1425), 0.0190)
  , ((-0.0990), 0.3270, (-0.0175), 0.0034)
  , (0.0990, 0.3270, (-0.1425), (-0.0039))
  , (0.0990, 0.3270, (-0.0175), (-0.0219))
  , ((-0.0330), 0.3270, (-0.2675), (-0.0103))
  , ((-0.0330), 0.3270, 0.1075, (-0.0048))
  , (0.0330, 0.3270, (-0.2675), 0.0024)
  , (0.0330, 0.3270, 0.1075, 0.0291)
  , ((-0.0660), 0.3580, (-0.0800), 0.0209)
  , (0.0660, 0.3580, (-0.0800), (-0.0047))
  , ((-0.0990), 0.3270, (-0.2675), (-0.0201))
  , ((-0.0990), 0.3270, 0.1075, (-0.0203))
  , (0.0000, 0.3580, (-0.2050), 0.0014)
  , (0.0000, 0.3580, 0.0450, (-0.0274))
  , (0.0990, 0.3270, (-0.2675), 0.0283)
  , (0.0990, 0.3270, 0.1075, 0.0134)
  , ((-0.0660), 0.3580, (-0.2050), 0.0002)
  , ((-0.0660), 0.3580, 0.0450, 0.0211)
  , (0.0660, 0.3580, (-0.2050), 0.0013)
  , (0.0660, 0.3580, 0.0450, 0.0077)
  , ((-0.0330), 0.3270, (-0.3925), 0.0253)
  , (0.0330, 0.3270, (-0.3925), (-0.0266))
  , ((-0.0330), 0.3270, 0.2325, 0.0289)
  , (0.0330, 0.3270, 0.2325, 0.0252)
  , ((-0.0330), 0.3890, (-0.1425), 0.0040)
  , ((-0.0330), 0.3890, (-0.0175), 0.0149)
  , (0.0330, 0.3890, (-0.1425), 0.0045)
  , (0.0330, 0.3890, (-0.0175), 0.0099)
  , ((-0.0990), 0.3270, (-0.3925), (-0.0300))
  , ((-0.0990), 0.3270, 0.2325, 0.0046)
  , (0.0990, 0.3270, (-0.3925), 0.0035)
  , (0.0990, 0.3270, 0.2325, (-0.0018))
  , (0.0000, 0.3580, (-0.3300), 0.0144)
  , (0.0000, 0.3580, 0.1700, (-0.0193))
  , (0.0000, 0.4200, (-0.0800), (-0.0227))
  , ((-0.0660), 0.3580, (-0.3300), (-0.0190))
  , ((-0.0660), 0.3580, 0.1700, 0.0247)
  , (0.0660, 0.3580, (-0.3300), 0.0039)
  , (0.0660, 0.3580, 0.1700, (-0.0094))
  , ((-0.0330), 0.3890, (-0.2675), (-0.0284))
  , ((-0.0330), 0.3890, 0.1075, (-0.0001))
  , (0.0330, 0.3890, (-0.2675), (-0.0256))
  , (0.0330, 0.3890, 0.1075, (-0.0239))
  , (0.0000, 0.4200, (-0.2050), (-0.0138))
  , (0.0000, 0.4200, 0.0450, (-0.0262)) ]

/-- The street lamps round the city, as (u, v): u to the viewer's right, v away. The ground under each is lit. -/
def lamps : List (Float × Float) :=
  [ ((-5.1000), (-3.2000)), ((-5.1000), 0.2000), ((-5.1000), 3.6000), ((-2.7000), (-5.1000)), (0.4000, (-5.3000)), (3.2000, (-5.0000)), (5.3000, 1.2000), (5.3000, 4.2000), ((-3.2000), 5.3000), (0.0000, 5.6000), (3.0000, 5.4000), (6.9000, (-4.6000)), (7.3000, (-0.6000)) ]

/-- The quay's line, as u. The harbour lies to its left. -/
def quay : Float := (-5.4500)

end Charter.Games.Omerta.Meshes
