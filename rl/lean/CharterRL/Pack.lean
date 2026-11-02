import CharterRL.Gen
import Charter.Games.HexMap

/-!
# Generated worlds for training, and others for validation

The shipped worlds that count goods as points (AI Bubble, Strike the Earth, Pirate Republic, The Pit, Omertà, Hill
and Chill) are all held out, so a policy trained on Island and Not Catan never meets one. These worlds are made from
a seed, so there are as many as wanted, and none of them is a shipped world. Each is kept only if it passes
`G.checks`, the same test as `G.Valid`.

* `pack-train-<n>`: training worlds, from seeds `n`.
* `pack-val-<n>`: validation worlds, from seeds `1000000 + n`, which training never uses.
* `pack-train` and `pack-val`, without a number: the environment deals a new world from that set for each game, from
  the game's seed (`packSize` worlds in each set).

How they differ, each drawn from the seed:
* **map:** a connected patch of 14 to 30 hexes, grown at random from one hex, with about one tile in eight barren;
  numbers from the dice's range.
* **goods:** 3 to 7. In 4 worlds of 5, 1 or 2 of them count as points (`set-worth`, 1 to 3 points each). A point
  good comes from tiles, from a law that pays it at each round's end for each piece of one kind a seat owns, from a
  law that pays it for a build, or (with a piece that costs it, so points can be spent to build) from a law that pays
  seats below half the target. No world hands the same points to every seat whatever it does.
* **pieces (the build tree):** a piece on a spot and a piece on a link always; then any of an upgrade, a second spot
  piece, and an attachment, with costs of 1 to 3 goods, 0 to 3 points, yields 0 to 2 and limits 2 to 15.
* **length and target:** 8 to 12 rounds in 3 worlds of 5, else 15 to 30; targets from 5 to 40, higher where points
  come from goods.
* **dice and bank:** 1 to 3 dice of 4 to 8 sides; bank rates 2 to 5.
* **laws:** the point-good laws are founding laws; 0 to 2 other founding laws, and a library of 8 for votes.
* **seats:** 2 to 6.
-/

namespace CharterRL.Pack
open Charter Charter.Games HexGrid CharterRL.Gen

/-- How many worlds the environment deals from for `pack-train` and `pack-val`. -/
def packSize : Nat := 512

/-- The seed of world `n` of a set. -/
def seedOf (set : String) (n : Nat) : Nat := if set == "val" then 1000000 + n else n

/-- A connected patch of hexes, grown at random from the origin. -/
def patch (size : Nat) (r : Rng) : List Hex × Rng := Id.run do
  let mut hs : Array Hex := #[Hex.origin]
  let mut r := r
  let mut tries := 0
  while hs.size < size && tries < 20 * size do
    tries := tries + 1
    let (i, r1) := r.range 0 (hs.size - 1); r := r1
    let ns := hs[i]!.neighbors
    let (j, r1) := r.range 0 (ns.length - 1); r := r1
    let h := ns[j]!
    if !hs.contains h then hs := hs.push h
  return (hs.toList, r)

/-- A world of the pack, its library of laws and its spots' places. -/
def make (seed : Nat) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
  let mut r : Rng := ⟨UInt64.ofNat seed * 0x9E3779B97F4A7C15 + 0x51ED⟩
  let (nhex, r1) := r.range 14 30; r := r1
  let (hexes, r1) := patch nhex r; r := r1
  let (nres, r1) := r.range 3 7; r := r1
  let rs := resNames.extract 0 nres
  let (pointKind, r1) := r.range 0 4; r := r1
  let (npoint, r1) := r.range 1 2; r := r1
  let npoint := if pointKind == 0 then 0 else min npoint (nres - 2)
  let pointGoods := (rs.extract (nres - npoint) nres).toList
  let goods := (rs.extract 0 (nres - npoint)).toList
  let (dice, r1) := r.range 1 3; r := r1
  let (sides, r1) := r.range 4 8; r := r1
  -- Tiles: each gets a good (or nothing), and a number the dice can show.
  let mut tiles : List TileDef := []
  for h in hexes do
    let (barren, r1) := r.range 0 7; r := r1
    let (a, r1) := r.range 0 (nres - 1); r := r1
    let (num, r1) := r.range dice (dice * sides); r := r1
    -- Point goods come from tiles only in one kind of world.
    let res := if a ≥ nres - npoint && pointKind != 1 then goods[a % goods.length]! else rs[a]!
    tiles := tiles ++ [if barren == 0 then { hex := h, res := none, number := none }
                       else { hex := h, res := some res, number := some num }]
  let spots := spotsOf tiles
  let links := linksOf tiles
  let regions := regionsOf tiles
  let nspots := spots.length
  -- Pieces.
  let costOf (r : Rng) (pool : List String) : Bundle × Rng := Id.run do
    let mut r := r
    let (n, r1) := r.range 1 (min 3 pool.length); r := r1
    let mut c : Bundle := []
    for _ in [0:n] do
      let (a, r1) := r.range 0 (pool.length - 1); r := r1
      let (k, r1) := r.range 1 3; r := r1
      if !(c.any (·.1 == pool[a]!)) then c := c ++ [(pool[a]!, k)]
    return (c, r)
  let (c0, r1) := costOf r goods; r := r1
  let (c1, r1) := costOf r goods; r := r1
  let (p0, r1) := r.range 0 2; r := r1
  let (l0, r1) := r.range 3 8; r := r1
  let (l1, r1) := r.range 6 15; r := r1
  let mut pieces : List PieceDef :=
    [ { name := "hut", cost := c0, points := max 1 p0, placement := .spot, yield := 1, limit := l0 }
    , { name := "path", cost := c1, points := 0, placement := .link, yield := 0, limit := l1 } ]
  let (hasUp, r1) := r.range 0 2; r := r1
  if hasUp != 0 then
    let (c, r1) := costOf r goods; r := r1
    let (l, r1) := r.range 2 6; r := r1
    pieces := pieces ++ [{ name := "fort", cost := c, points := 2, placement := .upgrade "hut", yield := 2, limit := l }]
  let (hasSpot2, r1) := r.range 0 2; r := r1
  if hasSpot2 == 0 then
    -- A second spot piece; in some worlds it costs a point good.
    let pool := if pointKind == 4 then goods ++ pointGoods else goods
    let (c, r1) := costOf r pool; r := r1
    let (pts, r1) := r.range 1 3; r := r1
    let (l, r1) := r.range 2 6; r := r1
    pieces := pieces ++ [{ name := "mill", cost := c, points := pts, placement := .spot, yield := 1, limit := l }]
  let (hasAttach, r1) := r.range 0 2; r := r1
  if hasAttach == 0 then
    let (c, r1) := costOf r goods; r := r1
    let (pts, r1) := r.range 1 3; r := r1
    pieces := pieces ++ [{ name := "tower", cost := c, points := pts, placement := .attach "hut", yield := 0, limit := 2 }]
  let ks := (pieces.map (·.name)).toArray
  -- Length and target.
  let (short, r1) := r.range 0 4; r := r1
  let (rounds, r1) := if short < 3 then r.range 8 12 else r.range 15 30; r := r1
  let (target, r1) := if npoint > 0 then r.range 8 40 else r.range 5 14; r := r1
  let (bank, r1) := r.range 2 5; r := r1
  let (setup2, r1) := r.range 0 3; r := r1
  let G0 : GameDef :=
    { name := s!"Pack world {seed}"
      resources := (rs.toList.map fun n => { name := n, stock := 400 })
      pieces, map := { spotCount := nspots, links, regions }
      diceCount := dice, diceSides := sides, targetPoints := target, rounds, bankRate := bank
      setupPieces := if setup2 == 0 then ["hut", "hut"] else ["hut", "path", "hut", "path"] }
  if !G0.checks then throw s!"pack world {seed} does not pass G.checks"
  -- The point goods, as founding laws.
  let names := rs.toList
  let mut found : List String := []
  for (p, i) in pointGoods.zipIdx do
    let (w, r1) := r.range 1 3; r := r1
    let (amt, r1) := r.range 1 2; r := r1
    let source := match pointKind with
      | 2 => s!" (on-round-end (for-each-player true (transfer bank each {p} (count each {ks[amt % ks.size]!}))))"
      | 3 => s!" (on-build {ks[(i + 1) % ks.size]!} (transfer bank actor {p} {amt + 1}))"
      | 4 => s!" (on-round-end (for-each-player (< (points each) {target / 2}) (transfer bank each {p} 1)))"
      | _ => ""
    found := found ++ [s!"(law \"{p} is worth {w}\" (set-worth {p} {w}){source})"]
  let (nother, r1) := r.range 0 2; r := r1
  let mut i := 0
  for _ in [0:nother] do
    let (t, r1) := lawTexts rs ks #[] i r; r := r1
    i := i + 1
    found := found ++ [t]
  let mut G := G0
  for (L, _) in parsed names found do
    let G' := { G with foundingLaws := G.foundingLaws ++ [L] }
    if G'.checks then G := G'
  let spotKinds := (pieces.filter fun d => match d.placement with | .spot => true | _ => false).map (·.name) |>.toArray
  let mut texts : List String := []
  for _ in [0:8] do
    let (t, r1) := lawTexts rs ks spotKinds i r; r := r1
    i := i + 1
    texts := texts ++ [t]
  let library := (parsed names texts).toArray
  return (G, library, normalised (spots.map (·.toPixel 1.0)))

/-- The tables of world `n` of a set (`train` or `val`). A seed whose world fails the checks is skipped: the next
seed is tried, so every `n` has a world. -/
def world (set : String) (n : Nat) : Tables := Id.run do
  for k in [0:64] do
    match make (seedOf set n + 7919 * k) with
    | .ok (G, library, xy) => return Tables.make s!"pack-{set}-{n}" G Charter.minSeats Charter.maxSeats library xy
    | .error _ => pure ()
  return default

/-- The tables of a pack id: `pack-train-<n>`, `pack-val-<n>`, or `pack-train` / `pack-val` (world 0 of the set,
until a game is dealt; see `dealt`). -/
def tables? (id : String) : Option Tables :=
  match id.splitOn "-" with
  | ["pack", set] => if set == "train" || set == "val" then some { world set 0 with id } else none
  | ["pack", set, n] =>
    if set == "train" || set == "val" then n.toNat?.map (world set) else none
  | _ => none

/-- The world a game of `pack-train` or `pack-val` is dealt, from the game's seed. Other tables stay as they are. -/
def dealt (T : Tables) (seed : Nat) : Tables :=
  match T.id with
  | "pack-train" => { world "train" (seed % packSize) with id := T.id }
  | "pack-val" => { world "val" (seed % packSize) with id := T.id }
  | _ => T

end CharterRL.Pack
