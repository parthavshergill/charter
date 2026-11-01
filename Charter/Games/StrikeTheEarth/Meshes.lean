import GpuCmd

/-! Written by `packs/strike-the-earth/gen.py`. Do not edit it by hand: run the script again. -/

namespace Charter.Games.StrikeTheEarth.Meshes
open GpuCmd

def hallStone : UInt32 := 100
def hallRoof : UInt32 := 101
def hallFire : UInt32 := 102
def shopStone : UInt32 := 103
def shopRoof : UInt32 := 104
def shopFire : UInt32 := 105
def tunnel : UInt32 := 106
def farmStalks : UInt32 := 107
def farmCaps : UInt32 := 108
def gateStone : UInt32 := 109
def gateDoor : UInt32 := 110
def shaftFrame : UInt32 := 111
def shaftPit : UInt32 := 112
def shaftFlag : UInt32 := 113
def epitaphStone : UInt32 := 114
def epitaphCap : UInt32 := 115
def tileStone : UInt32 := 116
def tileOre : UInt32 := 117
def tileFungus : UInt32 := 118
def tileEmber : UInt32 := 119
def seam : UInt32 := 120
def tileChamber : UInt32 := 121
def runes : UInt32 := 122
def rubble : UInt32 := 123
def stalag : UInt32 := 124
def oreChunk : UInt32 := 125
def capTeal : UInt32 := 126
def capViolet : UInt32 := 127
def hotRock : UInt32 := 128
def brazierBody : UInt32 := 129
def brazierFire : UInt32 := 130
def lawCost : UInt32 := 131
def lawPoints : UInt32 := 132
def lawBank : UInt32 := 133
def lawHarvest : UInt32 := 134
def lawBuild : UInt32 := 135
def lawRound : UInt32 := 136
def lawRoll : UInt32 := 137
def lawPiece : UInt32 := 138
def lawBroken : UInt32 := 139
def founder : UInt32 := 140
def founderEyes : UInt32 := 141
def wall : UInt32 := 142
def ground : UInt32 := 143
def river0 : UInt32 := 144
def fall0 : UInt32 := 145
def river1 : UInt32 := 146
def fall1 : UInt32 := 147
def cutFace : UInt32 := 148
def magma : UInt32 := 149
def niche : UInt32 := 150
def riftRim : UInt32 := 151
def riftCore : UInt32 := 152
def shard : UInt32 := 153

/-- Every mesh file: its id, its hash, its colour, how it moves and what stands in for it. -/
def defs : List Cmd :=
  [ .defineMeshFile 100 "98c3ee49f5673e62a5e0e09c47b4cfe31d72a694479d5b07db36216b68d6fb19" 0x918678 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.128 0.118)
  , .defineMeshFile 101 "b7d6fb308e98d248770648507812c34beed099db1a00b870b86533a41b277ab2" 0xEBEBEB { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.107 0.216)
  , .defineMeshFile 102 "590d6e64145009de24fb85aa7a3e7059ec5d834f3dfa21a5a2b72f813830c58f" 0xFFAC4C { pulse := 0.0, sway := 0, glow := 0.55 } (.sphere 0.001)
  , .defineMeshFile 103 "59609eec8bf91966a8d19bb881dc8750e5b15d50c5065110ef38f6db94be0f63" 0x8A8175 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.214 0.389)
  , .defineMeshFile 104 "cf84a05e4f47144533a514ce4abfccc3a880f5fb41a4854052b867d8018d1b6f" 0xEAEAEA { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.227 0.256)
  , .defineMeshFile 105 "f68217f88576cb4f46bec81ea7c5dd79af3a8b6055fe36f9d867c2797a4d8ac9" 0xFFBD60 { pulse := 0.0, sway := 0, glow := 0.7 } (.sphere 0.001)
  , .defineMeshFile 106 "e826e90227011883957acfa45935efe72dac21bedc9bb1c763e61fb43c3dee19" 0xE4E4E4 { pulse := 0, sway := 0, glow := 0 } (.box 0.95 0.05 0.11)
  , .defineMeshFile 107 "8bbd608d15cc9f2987bffe2a6c2ea2c2254bb54811bd026758cb850e5a4874c8" 0xC4BCAC { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.071 0.143)
  , .defineMeshFile 108 "d3d08ac9d46f857aebd7f9b3c5442b55a617d51101a8ad4dc9434c18926eb0b3" 0xF5F5F5 { pulse := 0, sway := 0.02, glow := 0.22 } (.sphere 0.07)
  , .defineMeshFile 109 "2cd4567a709c2a02dcd0f6d8394654a2bfe49d3ab1b29041c2f9ac8f83043052" 0xA49D90 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.122 0.296)
  , .defineMeshFile 110 "2e70d1a439e49b83158ae3c66202c0dd0042e393a351edc1e21a8bfdc09a29bf" 0xE2E2E2 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.053 0.183)
  , .defineMeshFile 111 "5e8ca16918175b791dad2d73727ef7edfe735c4add064b1d1606b4f9759f0e90" 0x66492F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.111 0.389)
  , .defineMeshFile 112 "9d2d87f218fd70a7cbf762835bf05716cd1e3b54c3c395fd7ec8295f2bfea271" 0xFF6016 { pulse := 0, sway := 0, glow := 0.75 } (.sphere 0.001)
  , .defineMeshFile 113 "de140175c17cac47dd40bd43870ff3bfb95ae6be0b95c18f3b40ceef4a5fc49f" 0xEEEEEE { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 114 "e4f6ec23ce1049f62020d65db449621aaa11beaae3e91e9fbaa87fb02976bab9" 0x968F82 { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.075 0.390)
  , .defineMeshFile 115 "b386a9003a1c3afa79165d46cbe2d2c44f7f1929df717ad6f5893558ab97f6b2" 0xFFFFFF { pulse := 0, sway := 0, glow := 0.25 } (.sphere 0.001)
  , .defineMeshFile 116 "b40db5dfd691e3fc14375aaf4a61fbaf5cacbd9e575fb7fb35240f0581549a32" 0x3D4150 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 117 "f73eac7c189d25713a6b2e984f706341e489a3eea19896727d539eb48ab105d7" 0x47331F { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 118 "5491d526a008ba7be7170df002613fc361537ff136d23054f6e145ab670036e0" 0x273545 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 119 "af5d02a605bf4dba1923d70703b045aae7198449800923fb067f20a7dfd97387" 0x181314 { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 120 "f5f871e28183d03cd554e45e549f0e10e8e19894052568088e70067b74754fc5" 0xFF8223 { pulse := 0, sway := 0, glow := 0.7 } (.sphere 0.001)
  , .defineMeshFile 121 "56ff9e0313559793ff55389ca3222e9d97ef20e80b3889c073ce681bffb6ce41" 0x48443D { pulse := 0, sway := 0, glow := 0 } (.hexPrism 0.96 0.15)
  , .defineMeshFile 122 "357badb836043052e54ce15d145071201c9a5c8dec92481dc73fd1c380776f6b" 0xFFC23A { pulse := 0, sway := 0, glow := 0.5 } (.sphere 0.001)
  , .defineMeshFile 123 "5b3922eb7e23f93faec78b8a9b99d9478e800847645f71930d28ead55ec41e69" 0x7E8293 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 124 "12bae68b21551ededad70e4ecc018d3213d2104bd08292759c270974bede4231" 0x787C8C { pulse := 0, sway := 0, glow := 0 } (.cone 0.05 0.2)
  , .defineMeshFile 125 "288b2dc0c32e96d74409a17f4e517879368b200f24e1e6234363873b2015b2f4" 0xEDB257 { pulse := 0, sway := 0, glow := 0.22 } (.cone 0.05 0.14)
  , .defineMeshFile 126 "9ddaa37632006c07b2d93d17c6f2166cdf8821bcee1f52bcc2df0ddf3fb62984" 0x66D5BF { pulse := 0, sway := 0.02, glow := 0.35 } (.cone 0.05 0.2)
  , .defineMeshFile 127 "503ae4d80e16bc4cca338b347bcc37e37b7ae48220a6d2470c6144cb7f8dee77" 0xAE93E4 { pulse := 0, sway := 0.02, glow := 0.3 } (.cone 0.05 0.2)
  , .defineMeshFile 128 "97f4871653abf4fc541401ae58a9b9ae8c21622888c0ba077cd9d90de66d15c0" 0x793419 { pulse := 0, sway := 0, glow := 0.3 } (.sphere 0.001)
  , .defineMeshFile 129 "71ff543a72ca1a8c002d495a419b8eae59f0a65ff600dd9adaf844ededc79e5f" 0x49443F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.05 0.25)
  , .defineMeshFile 130 "5505daa4970585734fe53af91abe2275a30c643a1a013bac6f54178a915af70e" 0xFF8B25 { pulse := 0.06, sway := 0.03, glow := 0.75 } (.sphere 0.001)
  , .defineMeshFile 131 "b3b03cc3fc8801642e662b6f80848b6321da84c29418369dcf7c923ccd6620b4" 0x8A857E { pulse := 0, sway := 0, glow := 0.05 } (.cone 0.08 0.3)
  , .defineMeshFile 132 "45a5e21d785a2045b717749e0625e6fc5c32cdebfb0640f1802ab389944f5f19" 0xC5B485 { pulse := 0, sway := 0, glow := 0.05 } (.cone 0.08 0.3)
  , .defineMeshFile 133 "229f9c3fa327071616f8e7cafe820ed7faab9786ce4c548fbd327cf8ef75c5eb" 0xD4B465 { pulse := 0, sway := 0, glow := 0.05 } (.cone 0.08 0.3)
  , .defineMeshFile 134 "f03f3262003ca3562e467c20bc8b05f1c05e189e4b68ae1fa2bc5419545db0b2" 0x76BBB5 { pulse := 0, sway := 0.012, glow := 0.22 } (.cone 0.08 0.3)
  , .defineMeshFile 135 "52993524ddcfd721499de4c69bb068da53e3e0d0003dc13dde1c39ad15cc29ed" 0x9D8F81 { pulse := 0, sway := 0, glow := 0.05 } (.cone 0.08 0.3)
  , .defineMeshFile 136 "01a8624703fe0ef9413d00f556aa47b0076ad98a4b557a4868619c27e0a2b446" 0x876C52 { pulse := 0.04, sway := 0, glow := 0.6 } (.cone 0.08 0.3)
  , .defineMeshFile 137 "17e8f181b3d3198669b8c58795eed1f552acd1ee2e22f7114578341fb545d4c7" 0x625B56 { pulse := 0, sway := 0, glow := 0.4 } (.cone 0.08 0.3)
  , .defineMeshFile 138 "a8cb5c52b1f8d695f9c5093f5fb98fb0dcc610ef0b8ee42cc7dbe611640d4154" 0x8DC1C2 { pulse := 0, sway := 0, glow := 0.5 } (.cone 0.08 0.3)
  , .defineMeshFile 139 "99b6cacb73bba6d42e3c762a605d9ec1597bc40b319ba0fdf5a19268ef6cc1f7" 0xA79A8B { pulse := 0, sway := 0, glow := 0.3 } (.cone 0.08 0.3)
  , .defineMeshFile 140 "791b2a2fbd3f5dc49df7feeee0751108eea28518141583e67db2fefcd1fcf85e" 0x8D8472 { pulse := 0, sway := 0, glow := 0 } (.cone 0.22 0.7)
  , .defineMeshFile 141 "80fc8117308b68abe6307c4de5bc300130600bddf922bc9a03e238462ecaeb9e" 0xFFD27A { pulse := 0, sway := 0, glow := 0.9 } (.sphere 0.001)
  , .defineMeshFile 142 "eefe04d74200dfcb582409e4403121dc2643f5e615c3e16814e5dcb547ae6df7" 0x312A2D { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 143 "d3a301cbe341d576cd11b846169349b23dc34270e653ca3d1093205ca915f3b3" 0x282023 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 144 "0166c5e762bf3c1923010074d0be4ff323b08ce3bfd2b285c923b4caa1112533" 0xFF8236 { pulse := 0, sway := 0, glow := 0.55 } (.sphere 0.001)
  , .defineMeshFile 145 "d53e36ff7f18c9a22af757b7568cedb96d69b896f995402a50751453a1a96075" 0xFF8236 { pulse := 0, sway := 0, glow := 0.55 } (.sphere 0.001)
  , .defineMeshFile 146 "13ead30efa3fa5c8e0a2c735e7746c7b961241be9136e0a9a019c2a32f7a2dc0" 0xFF8236 { pulse := 0, sway := 0, glow := 0.55 } (.sphere 0.001)
  , .defineMeshFile 147 "95af095faae83ad334a76421a5b71279010ae67932091820c95de836cd9d7f64" 0xFF8236 { pulse := 0, sway := 0, glow := 0.55 } (.sphere 0.001)
  , .defineMeshFile 148 "c055d3da3faf3475a1243abafa623cf315b453bd35e39de4f23825ffd3e02148" 0x492C23 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 149 "9c083014ba2946632b090018dceb526c304b83b4046d253634a71d7f09fbcba1" 0xFF621B { pulse := 0, sway := 0, glow := 0.4 } (.sphere 0.001)
  , .defineMeshFile 150 "9f9f4cf9902358b6c5702df258b57fc2ee2d2380e064fa993ba38afc42f39ae8" 0xA99578 { pulse := 0, sway := 0, glow := 0 } (.sphere 0.001)
  , .defineMeshFile 151 "aa623cca4faee78e967b29fa82b041b352dbef611771b5b35b232b6d64ce1deb" 0x33201F { pulse := 0, sway := 0, glow := 0 } (.cylinder 0.7 0.2)
  , .defineMeshFile 152 "17ef2b37f0028811af30b14be26f303a92e11fcfff8e14819ccbec11091726b7" 0xFF8135 { pulse := 0, sway := 0, glow := 0.75 } (.cylinder 0.4 0.1)
  , .defineMeshFile 153 "3e8f16a1bbe0094afcb8f8c703dd81ef96b3db4c34b68ab8f6be704c93b2645f" 0xFF8136 { pulse := 0.05, sway := 0, glow := 0.55 } (.cone 0.03 0.25) ]

/-- How many triangles each mesh has, by id. -/
def triangles : List (UInt32 × Nat) :=
  [ (100, 464), (101, 312), (102, 260), (103, 680), (104, 440), (105, 220), (106, 204), (107, 126), (108, 432), (109, 416), (110, 304), (111, 960), (112, 168), (113, 184), (114, 600), (115, 232), (116, 1356), (117, 1338), (118, 1334), (119, 1350), (120, 1048), (121, 1340), (122, 1600), (123, 164), (124, 222), (125, 372), (126, 242), (127, 242), (128, 238), (129, 332), (130, 260), (131, 664), (132, 632), (133, 724), (134, 956), (135, 622), (136, 860), (137, 588), (138, 664), (139, 436), (140, 3552), (141, 392), (142, 11136), (143, 8600), (144, 440), (145, 104), (146, 440), (147, 104), (148, 11880), (149, 1440), (150, 980), (151, 1970), (152, 1424), (153, 132) ]

/-- Where the lit halls stand on the back wall: x, y, z and size. -/
def niches : List (Float × Float × Float × Float) :=
  [(-9.475, 3.380, 6.081, 1.10), (-1.103, 2.274, -4.776, 1.41), (-4.896, 1.529, -2.295, 1.22), (3.985, 2.811, -8.104, 1.53), (-2.952, 0.917, -3.566, 1.34)]

/-- Where the braziers stand: x and z. -/
def braziers : List (Float × Float) :=
  [(-2.828, -2.828), (0.212, -3.465), (-3.818, 0.707), (-3.394, 3.677), (3.818, -2.828), (1.838, 4.384), (4.950, 0.990), (-0.636, 6.293)]

end Charter.Games.StrikeTheEarth.Meshes
