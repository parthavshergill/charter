import CharterRL.Pack
import CharterRL.WildOk

/-!
# Wild worlds, for training a policy that reads the rules

`pack-wild` deals a new world each game out of `wildSize` (65536), and `pack-wild-val` out of `valSize` (8192) from
seeds training never uses. `pack-wild-<n>` and `pack-wild-val-<n>` name one world. World `n` has style `n % 4`:

* **0, economy:** a random build tree. 2 to 12 goods, 0 to 3 of them worth points. Pieces on spots and links,
  upgrade chains (an upgrade of an upgrade, up to 6 pieces long), attachments, odd costs (1 to 4 of up to 4 goods), points
  0 to 6, yields 0 to 3, limits 1 to 20. Rich or starved boards (from 1 tile in 20 to 1 in 3 barren), small or large
  bank stocks, 1 to 4 dice of 2 to 12 sides, bank rates 2 to 8, 5 to 60 rounds, and a target well above the
  points setup gives. 0 to 3 founding laws.
* **1, laws:** a smaller random build tree with 4 to 14 founding laws from the whole law language (`wildLaw`).
* **2, island:** this branch's Island with costs, points, yields, limits, target, rounds and bank rate changed, and
  0 to 6 founding laws added. Its own vote library stays, with more added.
* **3, not-catan:** the same for Not Catan.

No world is built from a held-out shipped world: the only shipped worlds used are Island and Not Catan, which
training already plays.

Every world must pass `G.checks`. A seed whose world does not is skipped, as in the pack. Each world's vote library
has 14 more laws from `wildLaw`, including repeals of its founding laws, so laws can pass and lapse during a game.
With the setting `repeal_every`, the environment also proposes repeals of laws in force.

A world can still be dishonest: won by doing nothing, by luck, or in setup. `rl/worlds/wild_filter.py` plays each
world against `table` and `idle` seats and writes `CharterRL.WildOk`; `dealt` deals only the worlds it accepted.
-/

namespace CharterRL.Wild
open Charter Charter.Games HexGrid CharterRL.Gen CharterServer

/-- How many worlds `pack-wild` deals from. -/
def wildSize : Nat := 65536

/-- How many worlds `pack-wild-val` deals from. -/
def valSize : Nat := 8192

/-- The seed of world `n` of a set (`train` or `val`). The ranges never meet each other or the pack's. -/
def seedOf (set : String) (n : Nat) : Nat := (if set == "val" then 90000000 else 30000000) + n

/-- The styles, by `n % 4`. -/
def styleNames : Array String := #["economy", "laws", "island", "not-catan"]

/-- One of these, at random. -/
def pickOf {α : Type} [Inhabited α] (xs : Array α) (r : Rng) : α × Rng :=
  let (i, r) := r.range 0 (xs.size - 1)
  (xs[i]!, r)

/-- A law from the whole law language, as a title and a body. `goods` are the goods, `points` the goods worth
points (may be empty), `kinds` the kinds of piece, `spotKinds` those that stand on a spot, `founding` how many
founding laws there are (for repeals), and `lo`..`hi` the dice's totals. `forLibrary` allows the shapes that only
make sense as a vote: an effect at once, repeals, and a new piece. -/
def wildLaw (goods points kinds spotKinds : Array String) (founding lo hi : Nat) (i : Nat) (forLibrary : Bool)
    (r : Rng) : String × Rng := Id.run do
  let mut r := r
  let (t, r1) := r.range 0 (if forLibrary then 25 else 19); r := r1
  -- A founding law does not change a piece's points or make a plain good count: that would change what setup is
  -- worth, or end the game in its first rounds. A vote may.
  let t := if !forLibrary && (t == 9 || t == 11) then 13 else t
  let (R, r1) := pickOf goods r; r := r1
  let (R2, r1) := pickOf goods r; r := r1
  let (K, r1) := pickOf kinds r; r := r1
  let (K2, r1) := pickOf kinds r; r := r1
  let (S, r1) := pickOf (if spotKinds.isEmpty then kinds else spotKinds) r; r := r1
  let (n, r1) := r.range 1 4; r := r1
  let (m, r1) := r.range 2 6; r := r1
  let (d, r1) := r.range lo (max lo hi); r := r1
  let (k, r1) := r.range 0 (max 1 founding - 1); r := r1
  let (P, r1) := if points.isEmpty then (R2, r) else pickOf points r; r := r1
  let cost := if R == R2 then s!"(bundle ({R} {n + 1}))" else s!"(bundle ({R} {n}) ({R2} 1))"
  let (title, body) : String × String := match t with
    | 0 => (s!"Harvest tax on {R}", s!"(on-harvest (if (res-is {R}) (transfer actor treasury {R} (/ amount 2))))")
    | 1 => (s!"Wealth tax on {R}",
        s!"(on-round-end (for-each-player (<= {m} (holding each {R})) (transfer each treasury {R} (/ (holding each {R}) 3))))")
    | 2 => (s!"Dividend of {R}",
        s!"(on-round-end (for-each-player true (transfer treasury each {R} (/ (holding treasury {R}) 4))))")
    | 3 => (s!"Help for the last",
        s!"(on-round-end (for-each-player (= (points each) (least-over true (points each))) (transfer bank each {R} {n})))")
    | 4 => (s!"The leader pays",
        s!"(on-round-end (for-each-player (and (<= 3 (points each)) (= (points each) (most-over true (points each)))) (transfer each treasury {R} (min {n} (holding each {R})))))")
    | 5 => (s!"Auction for {P}",
        s!"(on-round-end (for-each-player (and (<= 1 (declared each {R})) (= (declared each {R}) (most-over true (declared each {R})))) (transfer each treasury {R} (min (declared each {R}) (holding each {R}))) (transfer bank each {P} {n})))")
    | 6 => (s!"Honest count of {R}",
        s!"(on-round-end (for-each-player (and (<= 1 (declared each {R})) (<= (declared each {R}) (holding each {R}))) (transfer bank each {R2} (/ (declared each {R}) 2))))")
    | 7 => (s!"Raid on {d}",
        s!"(on-roll (for-each-player (and (= rolled {d}) (< (points actor) (points each))) (move-piece each actor {K})))")
    | 8 => (s!"Bank rate {m}", s!"(set-bank-rate {m})")
    | 9 => (s!"{K} is worth {n - 1}", s!"(set-points {K} {n - 1})")
    | 10 => (s!"New price of {K}", s!"(set-cost {K} {cost})")
    | 11 => (s!"{R} counts", s!"(set-worth {R} {1 + n % 2})")
    | 12 => (s!"Bonus for {K}", s!"(on-build {K} (if (<= {n} (count actor {K2})) (transfer bank actor {P} 1)))")
    | 13 => (s!"Exchange of {R}",
        s!"(on-round-end (for-each-player (<= {m} (holding each {R})) (transfer each bank {R} {m}) (transfer bank each {R2} 1)))")
    | 14 => (s!"{K} brings {R}", s!"(on-build {K} (transfer bank actor {R} {n}))")
    | 15 => (s!"Lucky {d}", s!"(on-roll (if (= rolled {d}) (for-each-player true (transfer bank each {R} 1))))")
    | 16 => (s!"Early help",
        s!"(on-round-end (for-each-player (and (< round {m + 2}) (< (count each {K}) 2)) (transfer bank each {R} 2)))")
    | 17 => (s!"Upkeep of {K}",
        s!"(on-round-end (for-each-player (<= 3 (count each {K})) (transfer each bank {R} (min (count each {K}) (holding each {R})))))")
    | 18 => (s!"Points from {K}", s!"(on-round-end (for-each-player (<= {n + 2} (count each {K})) (transfer bank each {P} 1)))")
    | 19 => (s!"{R} makes {R2}", s!"(on-harvest (if (res-is {R}) (transfer bank actor {R2} 1)))")
    | 20 => (s!"Windfall of {R}", s!"(now (for-each-player (< (points each) {n + 6}) (transfer bank each {R} {m})))")
    | 21 | 22 =>
      if founding == 0 then (s!"Windfall of {R}", s!"(now (for-each-player true (transfer bank each {R} {n})))")
      else (s!"Repeal of law {k}", s!"(repeal {k})")
    | 23 =>
      if founding == 0 then (s!"New price of {K}", s!"(set-cost {K} {cost})")
      else (s!"Repeal of law {k}, and a new price of {K}", s!"(repeal {k}) (set-cost {K} {cost})")
    | 24 => (s!"Annex {i}",
        s!"(new-piece annex{i} (bundle ({R} {m})) (points {n}) (attach {S}) (yield 1) (limit 2))")
    | _ => (s!"Tax and relief on {R}",
        s!"(on-harvest (if (res-is {R}) (transfer actor treasury {R} 1))) (on-round-end (for-each-player (< (points each) {m + 2}) (transfer treasury each {R} 1)))")
  return (s!"(law \"{title}\" {body})", r)

/-- Add founding laws from these texts, each kept only if the game still passes `G.checks`. -/
def addFounding (G : GameDef) (texts : List String) : GameDef := Id.run do
  let names := G.resources.map (·.name)
  let mut G := G
  for (L, _) in parsed names texts do
    if G.foundingLaws.length < 40 then
      let G' := { G with foundingLaws := G.foundingLaws ++ [L] }
      if G'.checks then G := G'
  return G

/-- A vote library of `count` laws from `wildLaw`. -/
def wildLibrary (G : GameDef) (points : Array String) (count : Nat) (r : Rng) : Array (Law × String) × Rng := Id.run do
  let names := G.resources.map (·.name)
  let goods := (names.filter (!points.contains ·)).toArray
  let goods := if goods.isEmpty then names.toArray else goods
  let kinds := (G.pieces.map (·.name)).toArray
  let spotKinds := ((G.pieces.filter fun d => match d.placement with | .spot => true | _ => false).map (·.name)).toArray
  let lo := G.diceCount
  let hi := G.diceCount * G.diceSides
  let mut r := r
  let mut texts : List String := []
  for j in [0:count] do
    let (t, r1) := wildLaw goods points kinds spotKinds G.foundingLaws.length lo hi (200 + j) true r
    r := r1
    texts := texts ++ [t]
  return ((parsed names texts).toArray, r)

/-- Tiles over these hexes: a good from `pool` and a number from `lo` to `hi` (near the middle when `middle`), or
barren with chance 1 in `barrenOneIn`. -/
def wildTiles (hexes : List Hex) (pool : Array String) (barrenOneIn lo hi : Nat) (middle : Bool) (r : Rng) :
    List TileDef × Rng := Id.run do
  let mut r := r
  let mut out : List TileDef := []
  let mid := (lo + hi) / 2
  let a := if middle then max lo (mid - 2) else lo
  let b := if middle then min hi (mid + 2) else hi
  for h in hexes do
    let (barren, r1) := r.range 0 (barrenOneIn - 1); r := r1
    let (g, r1) := pickOf pool r; r := r1
    let (num, r1) := r.range a b; r := r1
    out := out ++ [if barren == 0 then { hex := h, res := none, number := none }
                   else { hex := h, res := some g, number := some num }]
  return (out, r)

/-- A cost of 1 to `most` goods from `pool`, 1 to 4 of each. -/
def wildCost (pool : Array String) (most : Nat) (r : Rng) : Bundle × Rng := Id.run do
  let mut r := r
  let (n, r1) := r.range 1 (max 1 (min most pool.size)); r := r1
  let mut c : Bundle := []
  for _ in [0:n] do
    let (g, r1) := pickOf pool r; r := r1
    let (k, r1) := r.range 1 4; r := r1
    if !(c.any (·.1 == g)) then c := c ++ [(g, k)]
  return (c, r)

/-- Styles 0 and 1: a world with a random build tree. `dense` (style 1) makes the tree smaller and the founding laws
many. -/
def makeTree (seed : Nat) (dense : Bool) :
    Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
  let mut r : Rng := ⟨UInt64.ofNat seed * 0xBF58476D1CE4E5B9 + 0x3C6EF372⟩
  let (nhex, r1) := r.range 4 (if dense then 24 else 34); r := r1
  let (hexes, r1) := Pack.patch nhex r; r := r1
  let (nres, r1) := r.range 2 (if dense then 7 else 12); r := r1
  let rs := resNames.extract 0 nres
  let (np, r1) := r.range 0 3; r := r1
  let npoint := min np (nres - 1)
  let points := rs.extract (nres - npoint) nres
  let goods := rs.extract 0 (nres - npoint)
  -- Dice and board.
  let (dpick, r1) := r.range 0 9; r := r1
  let dice := if dpick < 2 then 1 else if dpick < 8 then 2 else if dpick < 9 then 3 else 4
  let (sides, r1) := r.range 2 12; r := r1
  let sides := if dice == 1 then max 4 sides else sides
  let (barrenOneIn, r1) := pickOf #[3, 4, 6, 8, 12, 20] r; r := r1
  let (fromTiles, r1) := r.range 0 1; r := r1
  let (middle, r1) := r.range 0 1; r := r1
  let pool := if fromTiles == 0 then rs else goods
  let (tiles, r1) := wildTiles hexes pool barrenOneIn dice (dice * sides) (middle == 0) r; r := r1
  let spots := spotsOf tiles
  if spots.length > maxSpots then throw s!"wild world {seed} has {spots.length} spots"
  -- The build tree. `stands` are kinds that stand on a spot, for upgrades and attachments.
  let (c0, r1) := wildCost goods 3 r; r := r1
  let (p0, r1) := r.range 0 2; r := r1
  let (y0, r1) := r.range 1 2; r := r1
  let (l0, r1) := r.range 3 12; r := r1
  let mut pieces : List PieceDef :=
    [{ name := kindNames[0]!, cost := c0, points := max 1 p0, placement := .spot, yield := y0, limit := l0 }]
  let mut stands : Array String := #[kindNames[0]!]
  let mut chain : Array String := #[kindNames[0]!]
  let (hasLink, r1) := r.range 0 4; r := r1
  if hasLink != 0 then
    let (c, r1) := wildCost goods 2 r; r := r1
    let (l, r1) := r.range 4 20; r := r1
    pieces := pieces ++ [{ name := kindNames[1]!, cost := c, points := 0, placement := .link, yield := 0, limit := l }]
  let (extra, r1) := if dense then r.range 1 4 else r.range 1 9; r := r1
  let mut next := 2
  for _ in [0:extra] do
    let (kind, r1) := r.range 0 9; r := r1
    let (spendPoints, r1) := r.range 0 3; r := r1
    let pool := if spendPoints == 0 && !points.isEmpty then goods ++ points else goods
    let (c, r1) := wildCost pool 4 r; r := r1
    let (pts, r1) := r.range 0 6; r := r1
    let (y, r1) := r.range 0 3; r := r1
    let (l, r1) := r.range 1 20; r := r1
    let name := kindNames[next]!
    -- 0-3: an upgrade, of the top of the chain (so chains grow) or of any spot kind; 4-5: an attachment;
    -- 6-7: another spot piece; 8-9: a link piece.
    let (top, r1) := r.range 0 2; r := r1
    let (on, r1) := pickOf stands r; r := r1
    let placement : Placement :=
      if kind < 4 then .upgrade (if top != 0 then chain.back! else on)
      else if kind < 6 then .attach on
      else if kind < 8 then .spot
      else .link
    let d : PieceDef := match placement with
      | .link => { name, cost := c, points := pts % 2, placement, yield := 0, limit := l }
      | .attach _ => { name, cost := c, points := max 1 pts, placement, yield := y % 2, limit := max 1 (l % 5) }
      | .upgrade _ => { name, cost := c, points := max 1 pts, placement, yield := y, limit := l }
      | .spot => { name, cost := c, points := pts % 4, placement, yield := max 1 y, limit := l }
    pieces := pieces ++ [d]
    match placement with
    | .upgrade k => if chain.back! == k && chain.size < 6 then chain := chain.push name
    | _ => pure ()
    match placement with
    | .link => pure ()
    | _ => stands := stands.push name
    next := next + 1
  let link := (pieces.find? fun d => match d.placement with | .link => true | _ => false).map (·.name)
  let base := kindNames[0]!
  let (sp, r1) := r.range 0 3; r := r1
  let setupPieces := match sp, link with
    | 0, _ => [base]
    | 1, _ => [base, base]
    | 2, some l => [base, l, base, l]
    | 2, none => [base, base, base]
    | _, some l => [base, l, base, l]
    | _, none => [base, base]
  -- Length, target, bank, stocks.
  let (len, r1) := r.range 0 3; r := r1
  let (rounds, r1) := match len with
    | 0 => r.range 5 8
    | 3 => r.range 21 60
    | _ => r.range 9 20; r := r1
  -- The target is well above what setup gives, so a seat must build or trade to reach it.
  let setupPoints := setupPieces.foldl (fun a k => a + ((pieces.find? (·.name == k)).map (·.points)).getD 0) 0
  let lo := 2 * setupPoints + 6 + rounds / 2
  let (target, r1) := r.range lo (lo + 6 + rounds + 3 * npoint); r := r1
  let (bpick, r1) := r.range 0 9; r := r1
  let (bank, r1) := if bpick < 8 then r.range 2 5 else r.range 6 8; r := r1
  let (starved, r1) := r.range 0 4; r := r1
  let mut resources : List ResourceDef := []
  for g in rs.toList do
    let (stock, r1) := if starved == 0 then r.range 15 60 else r.range 100 2000; r := r1
    resources := resources ++ [{ name := g, stock }]
  let style := if dense then "laws" else "economy"
  let G0 : GameDef :=
    { name := s!"Wild {style} world {seed}", resources, pieces
      map := { spotCount := spots.length, links := linksOf tiles, regions := regionsOf tiles }
      diceCount := dice, diceSides := sides, targetPoints := target, rounds, bankRate := bank, setupPieces }
  if !G0.checks then throw s!"wild world {seed} does not pass G.checks"
  -- Founding laws: each point good's worth and a source for it, then laws from the whole language.
  let ks := (pieces.map (·.name)).toArray
  let mut found : List String := []
  -- A point good is paid for pieces that setup does not place, so a seat that only sets up earns none of it.
  let built := (ks.filter (!setupPieces.contains ·))
  let built := if built.isEmpty then ks else built
  for p in points.toList do
    let (w, r1) := r.range 1 3; r := r1
    let (src, r1) := r.range 0 2; r := r1
    let (K, r1) := pickOf built r; r := r1
    let (amt, r1) := r.range 1 2; r := r1
    let source := match src with
      | 0 => s!" (on-round-end (for-each-player true (transfer bank each {p} (count each {K}))))"
      | 1 => s!" (on-build {K} (transfer bank actor {p} {amt}))"
      | _ => ""
    found := found ++ [s!"(law \"{p} is worth {w}\" (set-worth {p} {w}){source})"]
  let (nfound, r1) := if dense then r.range 4 14 else r.range 0 3; r := r1
  let stand := stands
  for j in [0:nfound] do
    let (t, r1) := wildLaw goods points ks stand j dice (dice * sides) j false r; r := r1
    found := found ++ [t]
  let G := addFounding G0 found
  let (library, _) := wildLibrary G points 14 r
  return (G, library, normalised (spots.map (·.toPixel 1.0)))

/-- Styles 2 and 3: a shipped training world (Island or Not Catan) with its numbers changed and laws added. -/
def mutate (spec : GameSpec) (seed : Nat) :
    Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
  let T := Tables.ofSpec spec
  let G0 := T.G
  let mut r : Rng := ⟨UInt64.ofNat seed * 0x94D049BB133111EB + 0x7F4A7C15⟩
  let names := (G0.resources.map (·.name)).toArray
  let mut pieces : List PieceDef := []
  for d in G0.pieces do
    let mut cost : Bundle := []
    for (g, k) in d.cost do
      let (dk, r1) := r.range 0 5; r := r1
      let k' := match dk with | 0 => k - 1 | 4 => k + 1 | 5 => k + 2 | _ => k
      let (swap, r1) := r.range 0 5; r := r1
      let (g2, r1) := pickOf names r; r := r1
      let g' := if swap == 0 && !(d.cost.any (·.1 == g2)) && !(cost.any (·.1 == g2)) then g2 else g
      if !(cost.any (·.1 == g')) then cost := cost ++ [(g', max 1 k')]
    let (dp, r1) := r.range 0 4; r := r1
    let points := match dp with | 0 => d.points - 1 | 3 => d.points + 1 | 4 => d.points + 2 | _ => d.points
    let (dy, r1) := r.range 0 5; r := r1
    let yield_ := match dy with | 0 => d.yield - 1 | 5 => d.yield + 1 | _ => d.yield
    let (dl, r1) := r.range 0 3; r := r1
    let limit := match dl with | 0 => max 1 (d.limit - d.limit / 3) | 3 => d.limit + d.limit / 2 + 1 | _ => d.limit
    pieces := pieces ++ [{ d with cost, points, yield := yield_, limit }]
  let (tp, r1) := r.range 100 170; r := r1
  let (rp, r1) := r.range 60 150; r := r1
  let (bank, r1) := r.range 2 5; r := r1
  let setupPoints := G0.setupPieces.foldl (fun a k => a + ((pieces.find? (·.name == k)).map (·.points)).getD 0) 0
  let G1 : GameDef :=
    { G0 with
      name := s!"Wild {spec.G.name} {seed}", pieces
      targetPoints := max (setupPoints + 4) (G0.targetPoints * tp / 100)
      rounds := min maxRoundsAllowed (max 3 (G0.rounds * rp / 100))
      bankRate := bank }
  if !G1.checks then throw s!"wild {spec.id} {seed} does not pass G.checks"
  -- A good worth points, in 1 world in 3.
  let (worth, r1) := r.range 0 2; r := r1
  let (P, r1) := pickOf names r; r := r1
  let points := if worth == 0 then #[P] else #[]
  let ks := (pieces.map (·.name)).toArray
  let stands := ((pieces.filter fun d => match d.placement with | .link => false | _ => true).map (·.name)).toArray
  let mut found : List String := []
  if worth == 0 then
    let built := ks.filter (!G0.setupPieces.contains ·)
    let (K, r1) := pickOf (if built.isEmpty then ks else built) r; r := r1
    found := found ++ [s!"(law \"{P} is worth 1\" (set-worth {P} 1) (on-build {K} (transfer bank actor {P} 1)))"]
  let (nfound, r1) := r.range 0 6; r := r1
  let goods := (names.filter (!points.contains ·))
  for j in [0:nfound] do
    let (t, r1) := wildLaw goods points ks stands j G1.diceCount (G1.diceCount * G1.diceSides) j false r; r := r1
    found := found ++ [t]
  let G := addFounding G1 found
  let (more, _) := wildLibrary G points 10 r
  let own := (T.library.zip T.libraryText)
  return (G, own ++ more, T.spotXY)

/-- World `n` of a set, in style `n % 4`, from this seed. -/
def make (seed n : Nat) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) :=
  match n % 4 with
  | 0 => makeTree seed false
  | 1 => makeTree seed true
  | 2 => mutate islandSpec seed
  | _ => mutate notCatanSpec seed

/-- The seat range of world `n`: the shipped world's for styles 2 and 3, else all. -/
def seatsOf (n : Nat) : Nat × Nat :=
  match n % 4 with
  | 2 => (islandSpec.minSeats, islandSpec.maxSeats)
  | 3 => (notCatanSpec.minSeats, notCatanSpec.maxSeats)
  | _ => (Charter.minSeats, Charter.maxSeats)

/-- The tables of world `n` of a set (`train` or `val`), and how many seeds were skipped to find it. -/
def worldTried (set : String) (n : Nat) : Tables × Nat := Id.run do
  let (lo, hi) := seatsOf n
  let name := if set == "val" then "pack-wild-val" else "pack-wild"
  for k in [0:64] do
    match make (seedOf set n + 7919 * k) n with
    | .ok (G, library, xy) => return (Tables.make s!"{name}-{n}" G lo hi library xy, k)
    | .error _ => pure ()
  return (default, 64)

def world (set : String) (n : Nat) : Tables := (worldTried set n).1

/-! ## Dealing and describing

Nothing below changes what a world is. `rl/worlds/wild_filter.py` hashes this file only up to this heading, so a
change below needs no new filter run. -/

/-- The tables of a wild id: `pack-wild-<n>`, `pack-wild-val-<n>`, or `pack-wild` / `pack-wild-val` (the first
accepted world of the set, until a game is dealt; see `dealt`). -/
def tables? (id : String) : Option Tables :=
  match id.splitOn "-" with
  | ["pack", "wild"] => some { world "train" (WildOk.nextOk "train" 0 wildSize) with id }
  | ["pack", "wild", "val"] => some { world "val" (WildOk.nextOk "val" 0 valSize) with id }
  | ["pack", "wild", "val", n] => n.toNat?.map (world "val")
  | ["pack", "wild", n] => n.toNat?.map (world "train")
  | _ => none

/-- The world a game of `pack-wild` or `pack-wild-val` is dealt, from the game's seed: one of the worlds the filter
accepted, each equally often (`WildOk.dealtOf`). Other tables stay as they are. -/
def dealt (T : Tables) (seed : Nat) : Tables :=
  match T.id with
  | "pack-wild" => { world "train" (WildOk.dealtOf "train" seed wildSize) with id := T.id }
  | "pack-wild-val" => { world "val" (WildOk.dealtOf "val" seed valSize) with id := T.id }
  | _ => T

/-- A world in words, for a person to read: its numbers, goods, pieces, founding laws and vote library. -/
def describe (T : Tables) : String := Id.run do
  let G := T.G
  let bundle (b : Bundle) : String := if b.isEmpty then "nothing" else ", ".intercalate (b.map fun (g, k) => s!"{k} {g}")
  let place : Placement → String
    | .spot => "on a spot"
    | .link => "on a link"
    | .upgrade k => s!"replaces a {k}"
    | .attach k => s!"attaches to a {k}"
  let byGood := G.resources.map fun rd => (rd.name, (G.map.regions.filter (·.res == rd.name)).length)
  let mut out : Array String := #[]
  out := out.push s!"{T.id}: {G.name}"
  out := out.push s!"  {T.minSeats} to {T.maxSeats} seats. {G.rounds} rounds, target {G.targetPoints} points. \
    {G.diceCount} dice of {G.diceSides} sides. Bank rate {G.bankRate}."
  out := out.push s!"  Board: {G.map.spotCount} spots, {G.map.links.length} links, {G.map.regions.length} tiles that pay \
    ({", ".intercalate (byGood.map fun (g, n) => s!"{n} {g}")})."
  out := out.push s!"  Bank stock: {", ".intercalate (G.resources.map fun rd => s!"{rd.stock} {rd.name}")}."
  out := out.push "  Pieces:"
  for d in G.pieces do
    out := out.push s!"    {d.name}: {place d.placement}, costs {bundle d.cost}, {d.points} points, yields {d.yield}, \
      at most {d.limit}"
  out := out.push s!"  Setup: {", ".intercalate G.setupPieces}."
  out := out.push s!"  Founding laws ({G.foundingLaws.length}):"
  for L in G.foundingLaws do
    out := out.push s!"    {(Rules.lawS L).render}"
  out := out.push s!"  Laws that can be put to a vote ({T.libraryText.size}):"
  for x in T.libraryText do
    out := out.push s!"    {x}"
  return "\n".intercalate out.toList

end CharterRL.Wild
