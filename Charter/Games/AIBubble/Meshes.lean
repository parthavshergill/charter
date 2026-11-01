import GpuCmd

/-! Written by `packs/ai-bubble/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.AIBubble.Meshes
open GpuCmd

def dcBody : UInt32 := 100
def dcLed : UInt32 := 101
def campusBody : UInt32 := 102
def campusLed : UInt32 := 103
def steam : UInt32 := 104
def fibreBed : UInt32 := 105
def fibreCore : UInt32 := 106
def madeA : UInt32 := 107
def madeB : UInt32 := 108
def madeC : UInt32 := 109
def tileSilicon : UInt32 := 110
def tilePower : UInt32 := 111
def tileConcrete : UInt32 := 112
def tileExchange : UInt32 := 113
def seam : UInt32 := 114
def pallet : UInt32 := 115
def rack : UInt32 := 116
def pylon : UInt32 := 117
def transformer : UInt32 := 118
def crane : UInt32 := 119
def slabs : UInt32 := 120
def chillers : UInt32 := 121
def battery : UInt32 := 122
def relay : UInt32 := 123
def exchange : UInt32 := 124
def exchangeLit : UInt32 := 125
def lawCost : UInt32 := 126
def lawPoints : UInt32 := 127
def lawBank : UInt32 := 128
def lawHarvest : UInt32 := 129
def lawBuild : UInt32 := 130
def lawRound : UInt32 := 131
def lawRoll : UInt32 := 132
def lawPiece : UInt32 := 133
def lawRepeal : UInt32 := 134
def desert : UInt32 := 135
def farHalls : UInt32 := 136
def farLights : UInt32 := 137
def farLine : UInt32 := 138
def meterBase : UInt32 := 139
def meterGlass : UInt32 := 140
def meterRing : UInt32 := 141

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "473995895022184fb4d7e1457fa84331c63fc09c560e472d050b74b383348787" 0xA6CEDA { pulse := 0, sway := 0, glow := 0 } (.box 0.46 0.14 0.26)
  , .defineMeshFile 101 "0592ec865b747d51b10141450cc3ca9bb0b202be264b8c7da1c4e1c24c5f9da1" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.35 } (.sphere 0.001)
  , .defineMeshFile 102 "afe06fd4123f2dad95641b6115f1bf91ca1431195f952ab63424c0b1b1537f3c" 0x9FC4CD { pulse := 0, sway := 0, glow := 0 } (.box 0.8 0.3 0.7)
  , .defineMeshFile 103 "0f41143e0aeb455f67bb50b050017e24ce4e0db976f2bfaea547973ec54cd135" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.35 } (.sphere 0.001)
  , .defineMeshFile 104 "2672ff48fbea09d2ff9dba170c3bb54b00cc1d174aa9e95ad003e66946c44c02" 0xFFFFFF { pulse := 0.09, sway := 0.05, glow := 0.05 } (.sphere 0.001)
  , .defineMeshFile 105 "ece321fc6ca8a9d8097dddd78fc40d7dd20a8895b5f4d4fd9ea977bafaa6a850" 0x363E4A { pulse := 0, sway := 0, glow := 0 } (.box 0.8 0.02 0.1)
  , .defineMeshFile 106 "bebf5fec5b3163d0354c73ff0709a619decf7db6b95ed88ffed315160ad4eceb" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.5 } (.sphere 0.001)
  , .defineMeshFile 107 "ea67a1272798641afaf2a2f86b33a537ce45304f9032e7b8e4f19bead3bc66e1" 0xF0F0F0 { pulse := 0, sway := 0, glow := 0.25 } (.cylinder 0.096 0.290)
  , .defineMeshFile 108 "741beba0ef6d0b329dd5bb67c6924c3feef3b74b10128f2f2ad9c816221b0e22" 0xF3F3F3 { pulse := 0, sway := 0, glow := 0.25 } (.cylinder 0.096 0.220)
  , .defineMeshFile 109 "67b22d97085bd054209b9927bc5ccb67488a77b7b6cc9ee9c14f9cd8f5d52807" 0xEAEAEA { pulse := 0, sway := 0, glow := 0.25 } (.cylinder 0.072 0.360)
  , .defineMeshFile 110 "3a2bfede21916a3a60a1c681dbf6d7a39bd355a89666682ec5f9de6be7cba0f7" 0x88CA78 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 111 "02bc5d889cc6c18b321e60b3e79d85b995590bdbcb408d32bf281018655c979c" 0xD1A54A { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 112 "301cec3d594a5a473f96e8ca9767b0d15b201981dc2630811eeadcc6e51e6fb8" 0x6B6852 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 113 "85dabf17c540bbda987fad699d7d07c503c96efe63d6b5974306b6759a620d94" 0x126978 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 114 "567d87d27c5f2e3cc256441daf8e98aeebe492f273fdc5323aeb130fa6b6f9cc" 0x1BD4F2 { pulse := 0, sway := 0, glow := 0.35 } (.hexPrism 1 0.01)
  , .defineMeshFile 115 "8ff3d4de80b61ee712659c02deab26fca8275cb5c7a9e8c59b32ed99b31d4b71" 0x324D3A { pulse := 0, sway := 0, glow := 0 } (.box 0.15 0.11 0.12)
  , .defineMeshFile 116 "6ea9728e7b2a2dbdac644f3b152ccd147d4d779253256c66444fe08a237918b8" 0x24CDBC { pulse := 0, sway := 0, glow := 0.4 } (.box 0.09 0.2 0.06)
  , .defineMeshFile 117 "e2bc426207b77e6c0dcaa315ed68fb7832cdd1c09f9be1600801c0e939d81c6f" 0x9D9276 { pulse := 0, sway := 0, glow := 0 } (.cone 0.08 0.44)
  , .defineMeshFile 118 "752b82286391fa6c64c7bf294809bfbca89764e3f34d0fa1a70db2bd400820b5" 0xA4ABB1 { pulse := 0, sway := 0, glow := 0.4 } (.box 0.1 0.06 0.08)
  , .defineMeshFile 119 "8e1a6c3c0ab33e26b1fcb4b4156605c1a134fc85790dbce625f8de3c2c442d89" 0xBFAD61 { pulse := 0, sway := 0, glow := 0 } (.cone 0.05 0.4)
  , .defineMeshFile 120 "c87d69bddc255ab92b319c65ae85e337430cfef6ee714cac779a43ac24a0c4d8" 0xB4BCC5 { pulse := 0, sway := 0, glow := 0 } (.box 0.14 0.05 0.1)
  , .defineMeshFile 121 "1b7efa01cd2b71464ef7a28577803dc80eee54f703404f189085d2ed69b21fb3" 0x436C7E { pulse := 0, sway := 0, glow := 0.25 } (.box 0.2 0.03 0.09)
  , .defineMeshFile 122 "b28f1828c72e7647312c685e841d3300e1d55ba5d5d4a3e3cadc43d0c97c0f74" 0x4D493A { pulse := 0, sway := 0, glow := 0.25 } (.box 0.2 0.04 0.06)
  , .defineMeshFile 123 "19e56aa30b82e1e364e87f40c9b8ef09a6afe0fe1b7ff4b3903144c1abc63146" 0xB37584 { pulse := 0, sway := 0, glow := 0.6 } (.box 0.06 0.1 0.05)
  , .defineMeshFile 124 "fb2cdc24d8f79aa22fdbd2f36a47af4ce01f06386719b69947e36f987c10bf15" 0x1F2733 { pulse := 0, sway := 0, glow := 0 } (.box 0.3 0.7 0.3)
  , .defineMeshFile 125 "95d3dc028507ef12b482d20f49202f5cd7c3fd2aae0eaf96ce92b12616ea2463" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.5 } (.sphere 0.001)
  , .defineMeshFile 126 "98d518536c0935a1bc3a0050790da957b3e40213b49d278835bb9ea7669c4271" 0x744466 { pulse := 0, sway := 0.03, glow := 0.25 } (.cone 0.07 0.25)
  , .defineMeshFile 127 "654c6a27eed3bfa1b4369c3774f9d99b8fd2567f2444e9ca92ea24a0ccfd8847" 0x27986B { pulse := 0, sway := 0, glow := 0.25 } (.cone 0.08 0.2)
  , .defineMeshFile 128 "d6643a4960b615d66455f09ba367e7ab77d3d465c094f5cdf54daf87269c3d7a" 0xA3BCD3 { pulse := 0, sway := 0, glow := 0.2 } (.cylinder 0.07 0.13)
  , .defineMeshFile 129 "c2891e9f9b7b2222f691def877d1e7381af9344dafdb2d4d614b7e1f8fcf2849" 0x21C3DB { pulse := 0, sway := 0, glow := 0.35 } (.box 0.08 0.2 0.08)
  , .defineMeshFile 130 "d9f69035694ba9811d25ef042b26623215a8aa46e0039ab36d943320c88e61af" 0xAEA969 { pulse := 0, sway := 0, glow := 0 } (.cone 0.07 0.26)
  , .defineMeshFile 131 "54ab04f239c4012b4e191fa30da74985b79376f3becba33b3016ce8b93fadecc" 0x757F8A { pulse := 0.05, sway := 0, glow := 0.15 } (.cone 0.07 0.22)
  , .defineMeshFile 132 "675000c29bab51e613c195da4b20174e35b2b026e343af2daf99c66f9b1ccca1" 0xB3727B { pulse := 0.05, sway := 0, glow := 0.9 } (.cone 0.06 0.25)
  , .defineMeshFile 133 "c6c5f24a114c91077bf9278c5a0c3f90a62456aefbf9f5bcafdbee1f64ec66d0" 0x9091BB { pulse := 0, sway := 0, glow := 0.25 } (.cone 0.07 0.2)
  , .defineMeshFile 134 "fc7da3bbfa97a6495ae0ef999639f40d712fa0b3c3ea8b3fc06e1f8696823f24" 0xCE8C95 { pulse := 0, sway := 0, glow := 0.2 } (.cone 0.07 0.23)
  , .defineMeshFile 135 "4c0c8657a66fb5144a957e1e3e3db44f3fb03503728dacb95bc73d5b99dd3af9" 0x152E3B { pulse := 0, sway := 0, glow := 0 } (.box 44 0.003 44)
  , .defineMeshFile 136 "8fc6d4793c199c4e063c0699a95143e5e90f8b0b670e9bb11fca6f860a39b184" 0x273140 { pulse := 0, sway := 0, glow := 0 } (.box 2 0.3 2)
  , .defineMeshFile 137 "86b032263aa24f6a3c7743e2af51f7c8708f0d3e522fa1ccc7404dece91885cd" 0x3FDDE2 { pulse := 0, sway := 0, glow := 0.5 } (.sphere 0.001)
  , .defineMeshFile 138 "bd8916f0d88acddd8a44f26d9556092b844acfa122e2d9c3a3bad1c19b78b7be" 0xA59267 { pulse := 0, sway := 0, glow := 0 } (.box 2 1 0.2)
  , .defineMeshFile 139 "f35b8b3027c59ea4d8d1cafb3f5b441f3188b993bb78ea9605bf55b46e606e5b" 0xA57F71 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.4 0.2)
  , .defineMeshFile 140 "9fb461b0a5e91816e03eaee0db17866475498de1ad2807ba2540b47341a52d48" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 141 "0158ce371e5ba34dcf1fbd6bcd30a5ebd4c731b206337210de3e7016d0e9ebb1" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.6 } (.cylinder 0.16 0.09) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 228), (101, 40), (102, 980), (103, 138), (104, 168), (105, 20), (106, 20), (107, 100), (108, 50), (109, 44), (110, 442), (111, 484), (112, 216), (113, 28), (114, 4), (115, 40), (116, 60), (117, 152), (118, 36), (119, 94), (120, 20), (121, 30), (122, 10), (123, 30), (124, 30), (125, 50), (126, 30), (127, 60), (128, 64), (129, 120), (130, 44), (131, 116), (132, 80), (133, 52), (134, 62), (135, 282), (136, 1252), (137, 1910), (138, 848), (139, 220), (140, 24), (141, 82) ]

end Charter.Games.AIBubble.Meshes
