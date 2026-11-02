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
* **laws:** the point-good laws are founding laws; 0 to 3 other founding laws, and a library of 10 for votes, made
  from the law language (`langLaw`, 12 shapes): treasury dividends to each seat, harvest taxes to the bank, piece moves
  on a roll, bank rate, points and cost changes, goods made worth points (so trades and holdings decide), declarations
  that buy points (so declaring matters), build rewards with conditions, effects at once, and repeals.
* **stocks:** 100 to 999 of each good.
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

/-- A law made from the law language, of one of 12 shapes chosen by the seed, over these goods (`R`), point goods
(`P`, or a good when there is none) and kinds (`K`). `forLibrary` allows the shapes that only make sense as a vote:
an effect at once (`now`) and a repeal. Each shape gives some observation columns their only values in training:
`from_treasury`, `to_each`, `to_bank`, `piece_moves`, `when`, `set_bank_rate`, `set_points`, `set_cost`,
`set_worth`, and laws that read declarations. -/
def langLaw (goods points kinds : Array String) (i : Nat) (forLibrary : Bool) (r : Rng) : String × Rng := Id.run do
  let mut r := r
  let (t, r1) := r.range 0 (if forLibrary then 11 else 9); r := r1
  let (a, r1) := r.range 0 (goods.size - 1); r := r1
  let (b, r1) := r.range 0 (goods.size - 1); r := r1
  let (c, r1) := r.range 0 (kinds.size - 1); r := r1
  let (n, r1) := r.range 1 4; r := r1
  let (d, r1) := r.range 2 12; r := r1
  let R := goods[a]!
  let R2 := goods[b]!
  let P := if points.isEmpty then R2 else points[a % points.size]!
  let K := kinds[c]!
  let body := match t with
    | 0 => s!"(on-round-end (for-each-player (< (points each) {n + 2}) (transfer treasury each {R} 1)))"
    | 1 => s!"(on-harvest (if (res-is {R}) (transfer actor bank {R} 1)))"
    | 2 => s!"(on-roll (for-each-player (and (= rolled {d}) (< (points actor) (points each))) (move-piece each actor {K})))"
    | 3 => s!"(set-bank-rate {n + 1})"
    | 4 => s!"(set-points {K} {n})"
    | 5 => s!"(set-cost {K} (bundle ({R} {n}) ({R2} 1)))"
    | 6 => s!"(set-worth {R} 1)"
    | 7 => s!"(on-round-end (for-each-player (<= 1 (declared each {R})) (transfer each treasury {R} (min (declared each {R}) (holding each {R}))) (transfer bank each {P} 1)))"
    | 8 => s!"(on-build {K} (if (<= {n} (holding actor {R})) (transfer actor treasury {R} {n}) (transfer bank actor {P} 1)))"
    | 9 => s!"(on-round-end (for-each-player (<= {n} (holding each {R})) (transfer each bank {R} 1) (transfer treasury each {P} 1)))"
    | 10 => s!"(now (for-each-player (< (points each) {n + 10}) (transfer bank each {R} 2)))"
    | _ => "(repeal 0)"
  return (s!"(law \"Law {i}\" {body})", r)

/-- A general world of the pack (style 0), its library of laws and its spots' places. -/
def makeGeneral (seed : Nat) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
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
      resources := (rs.toList.zipIdx.map fun (n, j) => { name := n, stock := 100 + (seed * 37 + j * 211) % 900 })
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
  let (nother, r1) := r.range 0 3; r := r1
  let mut i := 0
  for _ in [0:nother] do
    let (t, r1) := langLaw goods.toArray pointGoods.toArray ks i false r; r := r1
    i := i + 1
    found := found ++ [t]
  let mut G := G0
  for (L, _) in parsed names found do
    let G' := { G with foundingLaws := G.foundingLaws ++ [L] }
    if G'.checks then G := G'
  let spotKinds := (pieces.filter fun d => match d.placement with | .spot => true | _ => false).map (·.name) |>.toArray
  let mut texts : List String := []
  for j in [0:10] do
    let (t, r1) := if j % 3 == 0 then lawTexts rs ks spotKinds i r else langLaw goods.toArray pointGoods.toArray ks i true r
    r := r1
    i := i + 1
    texts := texts ++ [t]
  let library := (parsed names texts).toArray
  return (G, library, normalised (spots.map (·.toPixel 1.0)))

/-- Tiles over these hexes: a good from `pool` with a number, or barren with chance `1 / barrenOneIn`. `lowPips`
draws numbers from the dice's ends, where they come up least. -/
def tilesFor (hexes : List Hex) (pool : Array String) (barrenOneIn dice sides : Nat) (lowPips : Bool) (r : Rng) :
    List TileDef × Rng := Id.run do
  let mut r := r
  let mut out : List TileDef := []
  let lo := dice
  let hi := dice * sides
  let mid := (lo + hi) / 2
  for h in hexes do
    let (barren, r1) := r.range 0 (barrenOneIn - 1); r := r1
    let (a, r1) := r.range 0 (pool.size - 1); r := r1
    let (num, r1) := if lowPips then
        let (side, r1) := r.range 0 1
        let (k, r2) := r1.range 0 1
        (if side == 0 then lo + k else hi - k, r2)
      else r.range (mid - 2) (mid + 2)
    r := r1
    out := out ++ [if barren == 0 then { hex := h, res := none, number := none }
                   else { hex := h, res := some pool[a]!, number := some num }]
  return (out, r)

/-- The laws of a shaped world, its library, its spots' places, from its game and law texts. -/
def finish (G0 : GameDef) (rs : Array String) (found : List String) (goods points kinds : Array String) (r : Rng)
    (spots : List Vertex) : GameDef × Array (Law × String) × Array (Float × Float) := Id.run do
  let names := rs.toList
  let mut G := G0
  for (L, _) in parsed names found do
    let G' := { G with foundingLaws := G.foundingLaws ++ [L] }
    if G'.checks then G := G'
  let mut r := r
  let spotKinds := (G0.pieces.filter fun d => match d.placement with | .spot => true | _ => false).map (·.name) |>.toArray
  let mut texts : List String := []
  for j in [0:10] do
    -- One law in three from the older templates, which include a new piece; the rest from the law language.
    let (t, r1) := if j % 3 == 0 then lawTexts rs kinds spotKinds (100 + j) r else langLaw goods points kinds (100 + j) true r
    r := r1
    texts := texts ++ [t]
  return (G, (parsed names texts).toArray, normalised (spots.map (·.toPixel 1.0)))

/-- Style 1, **chains**: a chain of 2 or 3 steps on a spot. A fort replaces a hut and costs goods the board barely
makes, so it is funded by bank trades at a rate of 2 or 3. A keep attaches to a fort, and in half the worlds a spire
attaches to the keep; they cost a good that counts as a point, which a fort earns when it is built, so a seat
turns held points into more points by climbing. The board is poor (a third of tiles barren, numbers from the dice's
ends), but every seat gets a lump of the board's goods at the end of round 1, so a seat that converts it well moves
first. -/
def makeChain (seed : Nat) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
  let mut r : Rng := ⟨UInt64.ofNat seed * 0xD1B54A32D192ED03 + 0xC4A1⟩
  let (nhex, r1) := r.range 16 26; r := r1
  let (hexes, r1) := patch nhex r; r := r1
  let (nres, r1) := r.range 5 7; r := r1
  let rs := resNames.extract 0 nres
  let star := rs[nres - 1]!
  let nboard := (nres - 1) / 2 + 1
  let board := rs.extract 0 nboard
  let scarce := rs.extract nboard (nres - 1)
  -- About one tile in twelve makes a scarce good; the rest make board goods. No tile makes the point good.
  let pool := board ++ board ++ board ++ board ++ board ++ board ++ board ++ board ++ board ++ board ++ board ++ scarce
  let (tiles, r1) := tilesFor hexes pool 3 2 6 true r; r := r1
  let spots := spotsOf tiles
  let (three, r1) := r.range 0 1; r := r1
  let (n1, r1) := r.range 1 3; r := r1
  let (n2, r1) := r.range 1 3; r := r1
  let s0 := scarce[0]!
  let s1 := scarce[scarce.size - 1]!
  let b0 := board[0]!
  let b1 := board[1 % board.size]!
  let mut pieces : List PieceDef :=
    [ { name := "hut", cost := [(b0, 1), (b1, 1)], points := 1, placement := .spot, yield := 1, limit := 5 }
    , { name := "path", cost := [(b0, 1)], points := 0, placement := .link, yield := 0, limit := 12 }
    , { name := "fort", cost := [(b1, 2), (s0, n1)], points := 2, placement := .upgrade "hut", yield := 2, limit := 4 }
    , { name := "keep", cost := [(star, 2), (s1, n2)], points := 4, placement := .attach "fort", yield := 0, limit := 4 } ]
  if three == 1 then
    pieces := pieces ++ [{ name := "spire", cost := [(star, 3), (b0, 2)], points := 6, placement := .attach "keep"
                           yield := 0, limit := 2 }]
  pieces := pieces.map fun d => { d with cost := (d.cost.foldl (fun acc (g, k) =>
      if acc.any (·.1 == g) then acc.map (fun (h, m) => if h == g then (h, m + k) else (h, m)) else acc ++ [(g, k)]) []) }
  let (bank, r1) := r.range 2 3; r := r1
  let (target, r1) := r.range 18 26; r := r1
  let (rounds, r1) := r.range 10 12; r := r1
  let (lump, r1) := r.range 4 8; r := r1
  let G0 : GameDef :=
    { name := s!"Pack chain world {seed}"
      resources := rs.toList.map fun n => { name := n, stock := 999 }
      pieces, map := { spotCount := spots.length, links := linksOf tiles, regions := regionsOf tiles }
      diceCount := 2, diceSides := 6, targetPoints := target, rounds, bankRate := bank
      setupPieces := ["hut", "path", "hut", "path"] }
  if !G0.checks then throw s!"pack chain world {seed} does not pass G.checks"
  let found :=
    [ s!"(law \"A start\" (on-round-end (for-each-player (= round 1) (transfer bank each {b0} {lump}) (transfer bank each {b1} {lump}))))"
    , s!"(law \"Forts pay\" (set-worth {star} 1) (on-build fort (transfer bank actor {star} 2)))" ]
  let ks := (pieces.map (·.name)).toArray
  return finish G0 rs found board #[star] ks r spots

/-- Style 2, **fast**: a rich board (few barren tiles, numbers from the dice's middle), cheap pieces, a good that
counts as points and is paid for building, and a target that a seat reaches by about round 6 to 8 only if it builds
every turn. A seat that waits falls behind fast, and the round limit is near. -/
def makeFast (seed : Nat) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
  let mut r : Rng := ⟨UInt64.ofNat seed * 0xA0761D6478BD642F + 0x5A57⟩
  let (nhex, r1) := r.range 18 30; r := r1
  let (hexes, r1) := patch nhex r; r := r1
  let (nres, r1) := r.range 4 6; r := r1
  let rs := resNames.extract 0 nres
  let goods := rs.extract 0 (nres - 1)
  let star := rs[nres - 1]!
  let (tiles, r1) := tilesFor hexes goods 10 2 6 false r; r := r1
  let spots := spotsOf tiles
  let g (i : Nat) := goods[i % goods.size]!
  let (a, r1) := r.range 0 (goods.size - 1); r := r1
  let pay := 1
  let worth := 1
  let pieces : List PieceDef :=
    [ { name := "hut", cost := [(g a, 1), (g (a + 1), 1)], points := 1, placement := .spot, yield := 1, limit := 6 }
    , { name := "path", cost := [(g (a + 2), 1)], points := 0, placement := .link, yield := 0, limit := 15 }
    , { name := "fort", cost := [(g (a + 1), 2), (g (a + 3), 1)], points := 2, placement := .upgrade "hut", yield := 2
        limit := 5 } ]
  let pieces := pieces.map fun d => { d with cost := (d.cost.foldl (fun acc (gd, k) =>
      if acc.any (·.1 == gd) then acc.map (fun (h, m) => if h == gd then (h, m + k) else (h, m)) else acc ++ [(gd, k)]) []) }
  let (bank, r1) := r.range 2 4; r := r1
  let (target, r1) := r.range 22 30; r := r1
  let (rounds, r1) := r.range 8 10; r := r1
  let G0 : GameDef :=
    { name := s!"Pack fast world {seed}"
      resources := rs.toList.map fun n => { name := n, stock := 999 }
      pieces, map := { spotCount := spots.length, links := linksOf tiles, regions := regionsOf tiles }
      diceCount := 2, diceSides := 6, targetPoints := target, rounds, bankRate := bank
      setupPieces := ["hut", "path", "hut", "path"] }
  if !G0.checks then throw s!"pack fast world {seed} does not pass G.checks"
  let found := [s!"(law \"Building pays\" (set-worth {star} {worth}) (on-build hut (transfer bank actor {star} {pay})) (on-build fort (transfer bank actor {star} {pay + 1})))"]
  let ks := (pieces.map (·.name)).toArray
  return finish G0 rs found goods #[star] ks r spots

/-- A world of the pack in a style: a general world (0), a chain world (1) or a fast world (2). -/
def make (seed : Nat) (style : Nat := 0) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) :=
  match style with
  | 1 => makeChain seed
  | 2 => makeFast seed
  | _ => makeGeneral seed

/-- The tables of world `n` of a set (`train` or `val`). A seed whose world fails the checks is skipped: the next
seed is tried, so every `n` has a world. -/
def world (set : String) (n : Nat) : Tables := Id.run do
  for k in [0:64] do
    match make (seedOf set n + 7919 * k) (n % 3) with
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
