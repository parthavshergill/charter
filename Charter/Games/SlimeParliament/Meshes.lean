import GpuCmd

/-! Written by `packs/slime-parliament/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.SlimeParliament.Meshes
open GpuCmd

def nodeBody : UInt32 := 100
def nodeEyes : UInt32 := 101
def swellBody : UInt32 := 102
def swellWig : UInt32 := 103
def swellEyes : UInt32 := 104
def puffBody : UInt32 := 105
def puffHead : UInt32 := 106
def tendril : UInt32 := 107
def tileOats : UInt32 := 108
def tileDew : UInt32 := 109
def tileRot : UInt32 := 110
def tileSpores : UInt32 := 111
def tileChamber : UInt32 := 112
def oat : UInt32 := 113
def drop : UInt32 := 114
def toadstool : UInt32 := 115
def sporeling : UInt32 := 116
def leaf : UInt32 := 117
def fbCost : UInt32 := 118
def fbPoints : UInt32 := 119
def fbBank : UInt32 := 120
def fbHarvest : UInt32 := 121
def fbBuild : UInt32 := 122
def fbRound : UInt32 := 123
def fbPiece : UInt32 := 124
def fbRepeal : UInt32 := 125
def speaker : UInt32 := 126
def madeA : UInt32 := 127
def madeB : UInt32 := 128
def madeC : UInt32 := 129
def log : UInt32 := 130
def stump : UInt32 := 131

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "714ab3927e95ea85ba7f94838cea2b4fa5fed537d1f002eb34e4dd9a3f3cea27" 0xD0D0D0 { pulse := 0.045, sway := 0, glow := 0.12 } (.sphere 0.15)
  , .defineMeshFile 101 "72651d7507aace04f0be319c1df432938035eb25bee16f2dde3505e19dc26f36" 0xE2DCCB { pulse := 0.045, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 102 "536640f432b1aef9af3c6f92c3098871b85d35b1788a60f46af750ddea09d967" 0xD6D6D6 { pulse := 0.055, sway := 0, glow := 0.14 } (.sphere 0.26)
  , .defineMeshFile 103 "123135e2659a9886f6c6cc8fa5675ab9a5d6eb520e13fa41cf4262057213ce0c" 0xE9E2D0 { pulse := 0.055, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 104 "8fbfc2d81cb5fc0115d7ac30510ad3a991150ccbec69c7f5c23aea721fb34780" 0xDFD9C8 { pulse := 0.055, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 105 "cdf8709c041a97897089d660cb6a05e0939b43bdf9032a17df4616ef9830fe45" 0xC5C5C5 { pulse := 0, sway := 0.02, glow := 0 } (.cylinder 0.08 0.1)
  , .defineMeshFile 106 "6a1f0e41aa99289fb00019cd54c3118c698897da71f2c5ba473a7f185c084a76" 0xEDE6D3 { pulse := 0, sway := 0.02, glow := 0 } (.sphere 0.08)
  , .defineMeshFile 107 "0a7be58e97fbfb525705a58626f9f63b830a72e0f949c3c5c6684c06c5b8c3c1" 0xD2D2D2 { pulse := 0.05, sway := 0, glow := 0.12 } (.box 0.9 0.05 0.1)
  , .defineMeshFile 108 "db27d4c7f1884cc44ab21136fe6a525e34740b253d0616342a037b90da39e68e" 0x5B7436 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 109 "39498f382ce50506d75bb50f62046397f6b27f61d7005e69a0e2fe62f0f91866" 0x2B6870 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 110 "721b6b92b500c7624175bce32ebb6ac92e19f1bc9fbfafc84b5387f3c11b5cd7" 0x41242A { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 111 "ceb0ad747a78f742c75036dd13b14c8f0acfc991b933f4dbd7bfb1575ad09b96" 0xC27D26 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 112 "dcaad54ad48ec348a32b179864d905c0983a4c74e7340a3a46006ca9d973597b" 0xA68153 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 113 "0cd9771b143f1cfe8e04b24476513b60e6a405a6313ec280a85beef2c69acbf5" 0xE8D9A0 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.07 0.03)
  , .defineMeshFile 114 "628f90f125b8fb82fb0f545fe340b4005deb1342d7e61a04b5c0221504fe4d6e" 0xA9E3EE { pulse := 0.035, sway := 0, glow := 0.12 } (.sphere 0.05)
  , .defineMeshFile 115 "5792934434a3bd120332843688423731198ede6860853ece37b7a68aaf3dbcde" 0x927591 { pulse := 0, sway := 0.025, glow := 0 } (.cone 0.06 0.15)
  , .defineMeshFile 116 "0cc4954e513decc86bbfddcc3bc4d4754051124a9ed41797e0fa0578c9dc92b7" 0xEC9338 { pulse := 0, sway := 0.035, glow := 0.12 } (.cone 0.05 0.18)
  , .defineMeshFile 117 "699cc685bbc75603fa1082a5d827decf015f2b947adbc70a3691dd23e4c4ed59" 0x7E5726 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.15 0.02)
  , .defineMeshFile 118 "9caadf6659b5df32cdb311821e18a54fa276620cf2de1e742b38a4eb4a7918c7" 0xB9757E { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 119 "975868af279d7647b182a8da3a0c45edb7841f14d771d7b1e8b7b8a9876a9854" 0xB99D4D { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 120 "c5f2e06aab6ffbd2ea206fae06d188b78ed0722cbcbed4ac782fd831a337697b" 0x5F9E8D { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 121 "c266af4320eb2e0fee66cc59b43775e06d4c04a2a291f352db54490f6af3ddb7" 0xCB914D { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 122 "9d4a2eec568905a325c48b22014fe4a92925fc8f43a069ab681b9140a038d166" 0xA9A27F { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 123 "ba7b6305108c7a864a917104b07e0020f048e73bf3177516fc1f729cbbc43410" 0x947047 { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 124 "7f2194df88023a3999e59a09fad3a67af7ec1dd1057876c003e204ac07a58fea" 0xC5B99F { pulse := 0.0, sway := 0.03, glow := 0.1 } (.cone 0.08 0.3)
  , .defineMeshFile 125 "60cedcb90fb65c6d9e3b61501a19cdc08a2ebee5f118cd6a694691ef71e2d18d" 0x8A7D68 { pulse := 0, sway := 0.012, glow := 0 } (.cone 0.08 0.3)
  , .defineMeshFile 126 "26c02798b55f0333f35648be1efb7682b1add77c45bb5a6635b0b41285edf0d2" 0xAFA38B { pulse := 0, sway := 0.012, glow := 0.05 } (.cone 0.2 0.5)
  , .defineMeshFile 127 "83736db807f36b74ef3dbfaff662c0717bea1aa2fd5a41f00b9997a9474a20a8" 0xE2E2E2 { pulse := 0.03, sway := 0, glow := 0.2 } (.cylinder 0.061 0.277)
  , .defineMeshFile 128 "4ddcc522f5568643837734b696981f3e35930700167e6a9446b8059a6356a1d2" 0xEEEEEE { pulse := 0.03, sway := 0, glow := 0.2 } (.cylinder 0.104 0.174)
  , .defineMeshFile 129 "849f5eb3330c95301babd3212449e82a578820fd680bdded55416143f92694aa" 0xDADADA { pulse := 0.03, sway := 0, glow := 0.2 } (.cylinder 0.128 0.226)
  , .defineMeshFile 130 "6dc9d65b0f2ef1fd401b9a1ecd5638cf77dc42079a0c713e3ef495e2526db028" 0x483D24 { pulse := 0, sway := 0, glow := 0 } (.box 13 0.16 6.4)
  , .defineMeshFile 131 "063a46f006d1062a5ab0b4e57f58823f2c9df1ad3dd9928becbdc259b2ca3e6d" 0x5F462B { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.3 0.33) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 664), (101, 328), (102, 1082), (103, 1796), (104, 608), (105, 380), (106, 816), (107, 602), (108, 942), (109, 974), (110, 1010), (111, 972), (112, 968), (113, 188), (114, 170), (115, 298), (116, 310), (117, 238), (118, 784), (119, 636), (120, 836), (121, 904), (122, 648), (123, 780), (124, 788), (125, 576), (126, 2804), (127, 512), (128, 732), (129, 756), (130, 8114), (131, 1102) ]

end Charter.Games.SlimeParliament.Meshes
