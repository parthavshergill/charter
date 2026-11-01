import GpuCmd

/-! Written by `packs/the-pit/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.ThePit.Meshes
open GpuCmd

def farmBody : UInt32 := 100
def farmRoof : UInt32 := 101
def elevatorBody : UInt32 := 102
def elevatorPaint : UInt32 := 103
def railBed : UInt32 := 104
def railTies : UInt32 := 105
def madeA : UInt32 := 106
def madeB : UInt32 := 107
def madeC : UInt32 := 108
def tileWheat : UInt32 := 109
def tileLumber : UInt32 := 110
def tileIron : UInt32 := 111
def tileFloor : UInt32 := 112
def shock : UInt32 := 113
def pine : UInt32 := 114
def logs : UInt32 := 115
def ore : UInt32 := 116
def furnace : UInt32 := 117
def pit : UInt32 := 118
def desk : UInt32 := 119
def certificate : UInt32 := 120
def lawCost : UInt32 := 121
def lawPoints : UInt32 := 122
def lawBank : UInt32 := 123
def lawHarvest : UInt32 := 124
def lawBuild : UInt32 := 125
def lawRound : UInt32 := 126
def lawRoll : UInt32 := 127
def lawPiece : UInt32 := 128
def lawRepeal : UInt32 := 129
def prairie : UInt32 := 130
def city : UInt32 := 131
def smoke : UInt32 := 132
def train : UInt32 := 133

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "5a125745abd477d785fa8cdb267934037da023942a45d06f52a1297954536683" 0x716C67 { pulse := 0, sway := 0, glow := 0 } (.box 0.3 0.2 0.24)
  , .defineMeshFile 101 "d468cd01234e058108a651b5daef3ea3259e1ae1b21a9619316a77695537983b" 0xF6F6F6 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 102 "558657d4de4e35209123e0fe7baa73016fe1d2d8c40d9c1c0ca83aa416747b92" 0x573D26 { pulse := 0, sway := 0, glow := 0 } (.box 0.25 0.62 0.25)
  , .defineMeshFile 103 "bc523fc608711fb5bc2c3f52bec0014d79c789a4d8111c0c6ebdfca8003168df" 0xF4F4F4 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 104 "e71728362ea61a3d1e4b099c6cbc6f5e3417d3917d34a14c301669798c335054" 0x64676B { pulse := 0, sway := 0, glow := 0 } (.box 0.84 0.03 0.13)
  , .defineMeshFile 105 "a7daedfdede402f7f2af66e355f876680c6cee421e28aefabd2614dc01769f48" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 106 "99a81d60bdc6200d701ca6aad8601daee9f6012e3fe2a563dde814ba06a487ee" 0xDCDCDC { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.072 0.340)
  , .defineMeshFile 107 "9b552b8135cb1819cee6066da128f4ea31fa82df32866123656fc01e3032f654" 0xE3E3E3 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.112 0.200)
  , .defineMeshFile 108 "4d18dcdd20fb2f15b24315bfb1d4d25f74123641d9370265bc271ee7f8191ada" 0xF7F7F7 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.072 0.380)
  , .defineMeshFile 109 "aa2e914c262a3f51291856e607ec9f182b35ebd74819d354832a9e48aa17b561" 0xB59239 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 110 "4c9acfcd3e73bedc9e56eeb068c9db3cbe539b9ccf35c1dfc740cde4530b2337" 0x5E6236 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 111 "b76fb1c1acb2ad5edb1307835958591a991b98a03f5a12aa952a5b871a8c2d7c" 0x3E2218 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 112 "23aafc12b1192457ea2c4c89eed1a56ae1f01f7cd49094c8debbc7574d01232b" 0x462D16 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.95 0.16)
  , .defineMeshFile 113 "38fdcef9e4e715f083c6a9ffd1394e1b3490331b8e6a8f79d29a5108e925a480" 0xDCB651 { pulse := 0, sway := 0, glow := 0 } (.cone 0.04 0.14)
  , .defineMeshFile 114 "12fbd6330c012e743da490d3881114115b082abd42274db672ba6f2d2e0f816b" 0x355B33 { pulse := 0, sway := 0, glow := 0 } (.cone 0.08 0.3)
  , .defineMeshFile 115 "5aabe92220a2b5658021c3593f9e8aa42c7c07c97d429d15a4cb4d1239803b9a" 0xB8834A { pulse := 0, sway := 0, glow := 0 } (.box 0.14 0.12 0.16)
  , .defineMeshFile 116 "ec715b98d662a12e4bffda8eab55ffa21c51ec2e1f31d127c9dac48ae344baff" 0x552F23 { pulse := 0, sway := 0, glow := 0 } (.cone 0.09 0.075)
  , .defineMeshFile 117 "4070dcb46e716bb2b9bb140f05846d5b17f77ff897e2dfe9f63c9baec8cdde5c" 0x7C3D22 { pulse := 0, sway := 0, glow := 0.4 } (.cone 0.06 0.34)
  , .defineMeshFile 118 "bf71ddd7d1f861526858a6ac2bb6d8879ef4614536ef171474cca20a11a6a09c" 0x836444 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.42 0.07)
  , .defineMeshFile 119 "ef6ad99ec04fa5959254ebbf36e2aa2afdf8844d408e3848e54057465b65e0d3" 0xC09844 { pulse := 0, sway := 0, glow := 0 } (.box 0.34 0.24 0.2)
  , .defineMeshFile 120 "485e62fb82925dbf2b75b06fa28a1ccc83172e88bfa1277106ef4a6800135735" 0xB08071 { pulse := 0, sway := 0, glow := 0 } (.box 0.12 0.006 0.08)
  , .defineMeshFile 121 "1c143f13cb220fa2130fe0b7b8b492094ad6b047e2109c31fd70e7d384863f6b" 0x978870 { pulse := 0, sway := 0.03, glow := 0 } (.cone 0.07 0.24)
  , .defineMeshFile 122 "126f464773f23f92c66b852734e5ad09b2122e90a6f19901feff7989831735a5" 0xBA943E { pulse := 0, sway := 0, glow := 0.2 } (.cone 0.06 0.2)
  , .defineMeshFile 123 "2dc3d03a8a14394be52fab2e8ab9a16347a4d205dd8f7c2a4ee8964ab50b3489" 0xDBBA63 { pulse := 0, sway := 0, glow := 0 } (.box 0.12 0.08 0.08)
  , .defineMeshFile 124 "1031a5c102e944f211fc3f136b5ddc6f8a01a86148af80f86809c9c6fa088f69" 0xB6883F { pulse := 0, sway := 0.02, glow := 0 } (.cone 0.05 0.24)
  , .defineMeshFile 125 "87aa5caf46a721381c24e2a158b2b0d16b8cde0207665f7573b53b44e02ac575" 0x5F4229 { pulse := 0, sway := 0, glow := 0 } (.box 0.1 0.24 0.1)
  , .defineMeshFile 126 "f6f6d0378315e2660971f36a7077b282f02e00e18028573ec2d89f7f6a443078" 0xB18D44 { pulse := 0.05, sway := 0.02, glow := 0 } (.cone 0.07 0.24)
  , .defineMeshFile 127 "de89e342cdb21e169bd35dbca76b76def82797e1cd4f788862908697e7e95036" 0xCEC5B2 { pulse := 0, sway := 0, glow := 0.25 } (.cone 0.05 0.17)
  , .defineMeshFile 128 "960280d36ba67dc4ee5efe1b7c5338d5adaec9d89eb5348deb40d2973adbd1a2" 0x6A615A { pulse := 0, sway := 0, glow := 0 } (.cone 0.07 0.17)
  , .defineMeshFile 129 "6c16762896c7b16f2bf9483e929510299cf9d76e19d775142b453a68a3404950" 0x835D39 { pulse := 0, sway := 0, glow := 0 } (.cone 0.06 0.1)
  , .defineMeshFile 130 "c847f42d315dc6a8448aabd6901dbe40bea4a20b709a820ce236cb0b0313a979" 0x6B623E { pulse := 0, sway := 0, glow := 0 } (.box 44 0.003 44)
  , .defineMeshFile 131 "64daae309a254fa3adf4f2cdc0f72e783553c4e46f544743c2a415e9a0c15ac3" 0x554027 { pulse := 0, sway := 0, glow := 0 } (.box 4 1 4)
  , .defineMeshFile 132 "65e244d1097442aba04c56a7a989811347a92ec48666cae5b62ba8061d24cfa2" 0xFFFFFF { pulse := 0.05, sway := 0.06, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 133 "bf7ef5910cb824489af4df4776111012957c6cbad10829116fa37606472f0cee" 0x53351E { pulse := 0, sway := 0, glow := 0 } (.box 4 0.4 0.3) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 210), (101, 16), (102, 248), (103, 38), (104, 30), (105, 90), (106, 92), (107, 16), (108, 48), (109, 1616), (110, 126), (111, 126), (112, 198), (113, 52), (114, 38), (115, 48), (116, 42), (117, 64), (118, 130), (119, 68), (120, 20), (121, 66), (122, 118), (123, 130), (124, 82), (125, 68), (126, 94), (127, 110), (128, 22), (129, 68), (130, 197), (131, 5328), (132, 720), (133, 562) ]

end Charter.Games.ThePit.Meshes
