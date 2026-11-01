import GpuCmd

/-! Written by `packs/pirate-republic/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.PirateRepublic.Meshes
open GpuCmd

def sloopHull : UInt32 := 100
def sloopSail : UInt32 := 101
def sloopMarks1 : UInt32 := 102
def sloopMarks2 : UInt32 := 103
def sloopMarks3 : UInt32 := 104
def boom : UInt32 := 105
def boomMark : UInt32 := 106
def wharfBody : UInt32 := 107
def wharfTint : UInt32 := 108
def wharfLight : UInt32 := 109
def fortBody : UInt32 := 110
def fortTint : UInt32 := 111
def flagshipBody : UInt32 := 112
def flagshipTint : UInt32 := 113
def privateerBody : UInt32 := 114
def privateerTint : UInt32 := 115
def madeHull : UInt32 := 116
def madeTower : UInt32 := 117
def madeMagazine : UInt32 := 118
def tileTimber : UInt32 := 119
def tileRum : UInt32 := 120
def tilePowder : UInt32 := 121
def tilePlunder : UInt32 := 122
def tileNassau : UInt32 := 123
def hotRing : UInt32 := 124
def palm : UInt32 := 125
def kegs : UInt32 := 126
def cane : UInt32 := 127
def rock : UInt32 := 128
def chest : UInt32 := 129
def coin : UInt32 := 130
def fin : UInt32 := 131
def glint : UInt32 := 132
def squareMast : UInt32 := 133
def squareFlag : UInt32 := 134
def monCost : UInt32 := 135
def monPoints : UInt32 := 136
def monBank : UInt32 := 137
def monHarvest : UInt32 := 138
def monBuild : UInt32 := 139
def monRound : UInt32 := 140
def monRoll : UInt32 := 141
def monPiece : UInt32 := 142
def monRepeal : UInt32 := 143
def sea : UInt32 := 144
def islet : UInt32 := 145
def navy : UInt32 := 146
def sandbar : UInt32 := 147
def sandbarFlag : UInt32 := 148

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "060f47ae2ff44d0f35ddd953fd7c3e473aa2c406d39f2c49ce7fdb64f530a330" 0x654829 { pulse := 0, sway := 0.022, glow := 0 } (.box 0.55 0.06 0.13)
  , .defineMeshFile 101 "95f7bdb2e4b0830de3dfb0775879ffe870fe606c9c47934da244c13eef6a5e35" 0xFFFFFF { pulse := 0, sway := 0.022, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 102 "18129dd836aafbbb987b9e22fe4e99e03ee2a52d24e35418d6f152080ebca5b0" 0x1B1512 { pulse := 0, sway := 0.022, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 103 "ea751d58e05cd24abab5ddc979cff560b9a2818381bbd90866ad7f6c4f757b66" 0x1B1512 { pulse := 0, sway := 0.022, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 104 "2c6052d84aa3768f33e8e398169f45208667167547ff9e9237f82fcf8586f34a" 0x1B1512 { pulse := 0, sway := 0.022, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 105 "2b6caaf010681f9432e82d5bbc9e3cca23140b3586842f4ebde9fc99c4c76bc0" 0x6F4927 { pulse := 0, sway := 0.012, glow := 0 } (.box 0.8 0.05 0.06)
  , .defineMeshFile 106 "889cf3f816caee4fb7fa175c6e5e4a1dc7bfb920dcbe749cb3dac57a81a84d64" 0xFFFFFF { pulse := 0, sway := 0.012, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 107 "5561d61b33716c9b630d1175994be50e0dad751c061af0d709da245cf1442f60" 0x634227 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.2 0.15)
  , .defineMeshFile 108 "a956aa6274a4d38b5d78fdd194febf4c31e3cfc564f2f003b505d1eb47841c86" 0xE7E7E7 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 109 "91d1ee503e3012e9d12b415fe0ff986713f44766ce6ee642fd7c137e8260bd0c" 0xFFC24A { pulse := 0, sway := 0, glow := 0.75 } (.sphere 0.001)
  , .defineMeshFile 110 "44fa4485a04f1236cca7fa0584d506a07fc2724e067593df3db466e57e55df9e" 0x665F5F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.26 0.3)
  , .defineMeshFile 111 "f2f9b79986d3babc59352a89fa04bf37ed242f67b0c0cbec8d0e1e3e0cd692c0" 0xEEEEEE { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 112 "528ce9a7e01495c6bf8b12e848b1f49cba23ef019a8f97e7273ec9c4ad0c84d5" 0x3E3523 { pulse := 0, sway := 0.016, glow := 0 } (.box 0.75 0.3 0.2)
  , .defineMeshFile 113 "f5686cb0d0887d5cd1674a78925df268727acfc8eda0c25957518c07f349a655" 0xFFFFFF { pulse := 0, sway := 0.016, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 114 "5221fa3825bc073b82102b3055faef09a956d8843d6246b78ccfab8a09869ee2" 0xABA08E { pulse := 0, sway := 0.018, glow := 0 } (.box 0.6 0.25 0.17)
  , .defineMeshFile 115 "14d6e3e741789e32c8d35c5609ae6f91aaa97445182bbb7e572f78245c2f892c" 0xFFFFFF { pulse := 0, sway := 0.018, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 116 "0de3f9265876ccf89ac8764d6c001558315b3d7f4d527a24725f432f74d5728f" 0xDBDBDB { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.15 0.14)
  , .defineMeshFile 117 "4f524f45bcfae30c1c6e278462f91676c3be1c6e0130c5acfa86285c1cc71e36" 0xFFFFFF { pulse := 0, sway := 0, glow := 0 } (.cone 0.08 0.3)
  , .defineMeshFile 118 "cf1183afa9c430799784da3df07e2e0538d772cb017d56d707d705edf3704726" 0xCDCDCD { pulse := 0, sway := 0, glow := 0 } (.box 0.22 0.18 0.18)
  , .defineMeshFile 119 "d2fd6046c71169524c692fca5f04ba4dd594ac685afbc7527346f60a9c1a0eea" 0x42A68E { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 120 "3b6b4b210dec9f77ef4cb46540b324f1986725fd660efdd3366a283abc24117b" 0x75BD91 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 121 "bbfda8dd7b760f5a5a2b003e4e8d316e3c39525802f0daeaafa6a46230e95916" 0x4F918A { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 122 "0a1a258294456f84a3c6f002cd598e5e24e5ec67abe91c497be90f86914c96e2" 0x386599 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 123 "b16feed2b23a68b1833a2f79eea7c1e9ccb994e24d93b3cdc8290250b2ef2dd8" 0xAEA073 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 124 "a328ea23f3572085ef94a4967026c41f1639073bf8f3799f6fb4bb3012203abd" 0xFFD84A { pulse := 0, sway := 0, glow := 0.7 } (.sphere 0.001)
  , .defineMeshFile 125 "ff1cc0abd529aa45a2100763c238c5d2f8d03c011641ae5b2ed13cdad99a9235" 0x5B843F { pulse := 0, sway := 0.03, glow := 0 } (.cone 0.08 0.2)
  , .defineMeshFile 126 "21fe7c4428693f57ada611f32826d42af2d3745ae215456230b0b4cce71dc041" 0x8F5E3C { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.05 0.07)
  , .defineMeshFile 127 "d8fdaf230834482498f1995a887e6394a40d91be570bdfd8c5532d6898ec8671" 0xA2C94F { pulse := 0, sway := 0.025, glow := 0 } (.cone 0.03 0.1)
  , .defineMeshFile 128 "e135b533e97f649526c2b946ad0942a329d83a0f1881bc64aecbd8f484d13f8c" 0x6E632F { pulse := 0, sway := 0, glow := 0 } (.cone 0.04 0.07)
  , .defineMeshFile 129 "c67e0ac278e6189daebfd30d7702d1ee9681e35ea1de03caaf21e4475a14900f" 0xC9A03E { pulse := 0, sway := 0, glow := 0.28 } (.box 0.12 0.08 0.08)
  , .defineMeshFile 130 "3236b833009cab7246a297ba89e71e13b2792b206ae6735e316559a350752bf9" 0xFBD253 { pulse := 0, sway := 0, glow := 0.4 } (.cylinder 0.03 0.01)
  , .defineMeshFile 131 "047abb70b86715d5bd0431868ec10645980a85f28b478ac2a816dfe03b071c5c" 0x4A5560 { pulse := 0, sway := 0.08, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 132 "85e1ab55aa8f0618802591a646e377bcceb9b06254a680d40816470a26bd8f91" 0x9FDCDC { pulse := 0.12, sway := 0, glow := 0.5 } (.sphere 0.001)
  , .defineMeshFile 133 "8db520a57ed495c88f323e671f0cbc29269b40d831e42f259ba3400a72435cbc" 0x6C4C2B { pulse := 0, sway := 0, glow := 0 } (.cone 0.13 1.1)
  , .defineMeshFile 134 "63b76ca5d7410678a773b39348910bf031f49bef64e22d57b07eadb3e78e6139" 0x2F2E2E { pulse := 0, sway := 0.018, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 135 "68d369a65c7ff3e0f925ace1f6602e5baf6be27419e27541b8f57a98327a2ec1" 0xB18930 { pulse := 0, sway := 0, glow := 0 } (.cone 0.08 0.25)
  , .defineMeshFile 136 "de6bfa6a098f7e5eb35392a27e765405e3e5489947a40f1e91a3e3dc726a9147" 0xCCA549 { pulse := 0, sway := 0, glow := 0.18 } (.box 0.15 0.14 0.1)
  , .defineMeshFile 137 "cbb7f3947fe8b964e4d2e9a3f86aa43be34568d82a2a03d349c776698c0bc002" 0xC29D4A { pulse := 0, sway := 0, glow := 0.15 } (.cylinder 0.07 0.2)
  , .defineMeshFile 138 "e24fa35e036f874c637f9ba4c297c57393f4017f22dbf8c0bbd6731fb2565a45" 0x996E3F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.09 0.2)
  , .defineMeshFile 139 "1a3c46ef86567258541b34ac58d3c755046ee5751de01c8d39fdc4518d06e062" 0xAC7B44 { pulse := 0, sway := 0, glow := 0 } (.box 0.2 0.18 0.14)
  , .defineMeshFile 140 "38bba70661f172faaee33da1d9b2911b6c97a3dae1502fd7c6f63ce32c395141" 0x9E7D3A { pulse := 0, sway := 0, glow := 0.12 } (.cone 0.08 0.25)
  , .defineMeshFile 141 "b97c818a57d20dc512a0a3e3f3a0bc46706917f2f42d0de5cfc4057232c5fd76" 0x876249 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.07 0.25)
  , .defineMeshFile 142 "62fc94163a2add3cc0b98283579494fb01d13d7adb6a3f14c64028814cc0d690" 0xC7A458 { pulse := 0, sway := 0, glow := 0 } (.box 0.3 0.15 0.14)
  , .defineMeshFile 143 "7660fb1343898fe4140131d50dbd86ce1d465bf523e3dd3b4aa8f20e1b73adfc" 0x6E4B2E { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.05 0.2)
  , .defineMeshFile 144 "cf14c8d79e3b946207040de8ac99b679b4923a7efa66a4d39452e4f7e6ed3b10" 0x042339 { pulse := 0, sway := 0, glow := 0 } (.box 60 0.01 60)
  , .defineMeshFile 145 "86432fba1ccd46bc5dd5525296b8c45b4b0ef2755deec22d0641a7d4e8344ad5" 0x7EB27F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.45 0.15)
  , .defineMeshFile 146 "e58d460fd8f0c0085873d4c9068b0fbf639ce1b61bb7daa109d5ca2d59b7b5b0" 0x8C7D6A { pulse := 0, sway := 0.008, glow := 0 } (.box 2.5 1.8 0.5)
  , .defineMeshFile 147 "f0f95630c8903c5bf64638d2d3bede2f19dd913535a1d957281a8d8e7df108dd" 0x91835E { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.8 0.1)
  , .defineMeshFile 148 "f29a48f70c2a13e9d83eaf944774facbd2828ccd790afa16cf5a9e85ba7dc0de" 0x201F22 { pulse := 0, sway := 0.012, glow := 0 } (.sphere 0.001) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 98), (101, 160), (102, 20), (103, 40), (104, 60), (105, 104), (106, 50), (107, 286), (108, 22), (109, 20), (110, 357), (111, 56), (112, 360), (113, 60), (114, 232), (115, 60), (116, 48), (117, 48), (118, 16), (119, 1362), (120, 1420), (121, 1362), (122, 1460), (123, 1362), (124, 12), (125, 48), (126, 183), (127, 50), (128, 3), (129, 70), (130, 48), (131, 2), (132, 10), (133, 438), (134, 3264), (135, 136), (136, 100), (137, 191), (138, 193), (139, 102), (140, 102), (141, 121), (142, 96), (143, 52), (144, 3528), (145, 43), (146, 1732), (147, 120), (148, 72) ]

end Charter.Games.PirateRepublic.Meshes
