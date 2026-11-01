import CharterRL.Tables

/-!
# Made-up games, for "can it play"

A policy that ships has no fallback bot, so it must be able to play any game that passes `G.Valid`, at any seat
count the game allows. These games test that. Each one is made from a seed and a profile, and is kept only if it
passes `G.checks`, the same test `G.Valid` is:

* `limits`: the engine's limits. 16 resources, 16 kinds of piece, 100 spots with many links, many tiles, dice of
  4 x 20, 60 rounds, and as many founding laws as pass, up to 40, with more in the library for votes.
* `tiny`: one resource, one kind of piece, a few spots, few rounds.
* `odd`: sizes drawn at random between the two, with link pieces, upgrades and attachments mixed in.

The game id is `gen-<profile>-<seed>`, which `Env.ofJson` reads. No game here is used for training or for choosing
settings.
-/

namespace CharterRL.Gen
open Charter CharterServer

/-- A small random number source. -/
structure Rng where
  x : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.x + 0x9E3779B97F4A7C15
  (scramble x, ⟨x⟩)

/-- A number from `lo` to `hi`, both included. -/
def Rng.range (r : Rng) (lo hi : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (lo + x.toNat % (hi + 1 - lo), r)

/-- Names that are not words of the law language. -/
def resNames : Array String :=
  #["amber", "basalt", "coal", "dune", "ember", "flax", "gum", "hemp", "iron", "jade", "kelp", "lime", "moss", "nut",
    "opal", "peat"]

def kindNames : Array String :=
  #["hut", "path", "fort", "mill", "tower", "dock", "canal", "shrine", "barn", "wall", "bridge", "forge", "lodge",
    "mine", "port", "keep"]

/-- The sizes of a profile, each as a range. -/
structure Sizes where
  res : Nat × Nat
  kinds : Nat × Nat
  spots : Nat × Nat
  /-- Extra links per spot, past the ring that joins them. -/
  chords : Nat × Nat
  tiles : Nat × Nat
  dice : Nat × Nat
  sides : Nat × Nat
  rounds : Nat × Nat
  target : Nat × Nat
  founding : Nat × Nat
  /-- 1 for links between spots. 0 makes a map with no links, so no link pieces. -/
  links : Nat × Nat

def sizesOf : String → Option Sizes
  | "limits" => some { res := (16, 16), kinds := (16, 16), spots := (100, 100), chords := (3, 3), tiles := (60, 60)
                       dice := (4, 4), sides := (20, 20), rounds := (60, 60), target := (30, 30)
                       founding := (40, 40), links := (1, 1) }
  | "tiny" => some { res := (1, 1), kinds := (1, 1), spots := (1, 4), chords := (0, 0), tiles := (1, 2)
                     dice := (1, 1), sides := (2, 6), rounds := (1, 3), target := (1, 3), founding := (0, 0)
                     links := (0, 1) }
  | "odd" => some { res := (1, 16), kinds := (1, 16), spots := (2, 100), chords := (0, 4), tiles := (1, 40)
                    dice := (1, 4), sides := (2, 20), rounds := (1, 30), target := (1, 25), founding := (0, 12)
                    links := (0, 1) }
  | _ => none

/-- Laws over these names, as text. `i` keeps titles apart. -/
def lawTexts (rs ks spotKinds : Array String) (i : Nat) (r : Rng) : String × Rng := Id.run do
  let (t, r) := r.range 0 6
  let (a, r) := r.range 0 (rs.size - 1)
  let (b, r) := r.range 0 (ks.size - 1)
  let (c, r) := r.range 0 (max 1 spotKinds.size - 1)
  let R := rs[a]!
  let K := ks[b]!
  let text := match t with
    | 0 => s!"(law \"Half on {K} {i}\" (on-build {K} (transfer actor treasury {R} (/ (holding actor {R}) 2))))"
    | 1 => s!"(law \"Levy {i}\" (on-round-end (for-each-player true (transfer each treasury {R} (/ (holding each {R}) 2)))))"
    | 2 => s!"(law \"Tithe {i}\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    | 3 => s!"(law \"Cheap {K} {i}\" (set-cost {K} (bundle ({R} 1))))"
    | 4 => s!"(law \"Gift {i}\" (on-roll (transfer bank actor {R} 1)))"
    | 5 => s!"(law \"Bailout {i}\" (on-round-end (for-each-player (< (points each) 5) (transfer bank each {R} 1))))"
    | _ =>
      if spotKinds.isEmpty then s!"(law \"Gift {i}\" (on-roll (transfer bank actor {R} 1)))" else
      s!"(law \"Annex {i}\" (new-piece annex{i} (bundle ({R} 2)) (points 2) (attach {spotKinds[c]!}) (yield 1) (limit 2)))"
  return (text, r)

/-- The laws of these texts that read, with their text. -/
def parsed (names : List String) (texts : List String) : List (Law × String) :=
  texts.filterMap fun t => match Rules.parseProposal t names with
    | .ok (.law L) => some (L, t)
    | _ => none

/-- A made-up game, its library of laws and its spots' places, or why it could not be made. -/
def make (profile : String) (seed : Nat) : Except String (GameDef × Array (Law × String) × Array (Float × Float)) := do
  let some z := sizesOf profile | throw s!"there is no profile {profile}: there are limits, tiny and odd"
  let mut r : Rng := ⟨UInt64.ofNat seed * 0x2545F4914F6CDD1D + 17⟩
  let pick (r : Rng) (p : Nat × Nat) : Nat × Rng := r.range p.1 p.2
  let (nres, r1) := pick r z.res; r := r1
  let (nkinds, r1) := pick r z.kinds; r := r1
  let (nspots, r1) := pick r z.spots; r := r1
  let (hasLinks, r1) := pick r z.links; r := r1
  let (dice, r1) := pick r z.dice; r := r1
  let (sides, r1) := pick r z.sides; r := r1
  let (rounds, r1) := pick r z.rounds; r := r1
  let (target, r1) := pick r z.target; r := r1
  let (bank, r1) := r.range 2 5; r := r1
  -- Resources.
  let mut resources : List ResourceDef := []
  for i in [0:nres] do
    let (stock, r1) := r.range 20 2000; r := r1
    resources := resources ++ [{ name := resNames[i]!, stock }]
  let rs := resNames.extract 0 nres
  -- The map: a ring of spots, then chords.
  let mut links : List (Nat × Nat) := []
  if hasLinks == 1 && nspots ≥ 2 then
    for v in [0:nspots] do
      let w := (v + 1) % nspots
      if v != w && !(links.contains (linkEnds (v, w))) then links := links ++ [linkEnds (v, w)]
    for v in [0:nspots] do
      let (n, r1) := pick r z.chords; r := r1
      for _ in [0:n] do
        let (w, r1) := r.range 0 (nspots - 1); r := r1
        if v != w && !(links.contains (linkEnds (v, w))) then links := links ++ [linkEnds (v, w)]
  let (ntiles, r1) := pick r z.tiles; r := r1
  let mut regions : List Region := []
  for _ in [0:ntiles] do
    let (a, r1) := r.range 0 (nres - 1); r := r1
    let (number, r1) := r.range dice (dice * sides); r := r1
    let (size, r1) := r.range 1 (min 6 nspots); r := r1
    let mut spots : List Nat := []
    for _ in [0:size] do
      let (v, r1) := r.range 0 (nspots - 1); r := r1
      if !spots.contains v then spots := spots ++ [v]
    regions := regions ++ [{ res := rs[a]!, number, spots }]
  -- Pieces: the first goes on a spot, so setup can place it. Others are of any placement that can be built.
  let mut pieces : List PieceDef := []
  for i in [0:nkinds] do
    let (kindOf, r1) := r.range 0 3; r := r1
    let spotLike := pieces.filter fun d => match d.placement with | .link => false | _ => true
    let placement : Placement :=
      if i == 0 then .spot
      else match kindOf with
        | 0 => if links.isEmpty then .spot else .link
        | 1 => .spot
        | 2 => .upgrade ((spotLike.getLast?.map (·.name)).getD kindNames[0]!)
        | _ => .attach ((spotLike.head?.map (·.name)).getD kindNames[0]!)
    let (ncost, r1) := r.range 1 (min 3 nres); r := r1
    let mut cost : Bundle := []
    for _ in [0:ncost] do
      let (a, r1) := r.range 0 (nres - 1); r := r1
      let (n, r1) := r.range 1 3; r := r1
      if !(cost.any (·.1 == rs[a]!)) then cost := cost ++ [(rs[a]!, n)]
    let (points, r1) := r.range 0 3; r := r1
    let (yield_, r1) := r.range 0 2; r := r1
    let (limit, r1) := r.range 1 15; r := r1
    pieces := pieces ++ [{ name := kindNames[i]!, cost, points, placement, yield := yield_, limit }]
  let first := (pieces.head?.map (·.name)).getD kindNames[0]!
  let linkKind := (pieces.find? fun d => match d.placement with | .link => true | _ => false).map (·.name)
  let setupPieces := match linkKind with
    | some l => [first, l, first, l]
    | none => [first, first]
  let ks := (pieces.map (·.name)).toArray
  let spotKinds := (pieces.filter fun d => match d.placement with | .spot => true | _ => false).map (·.name) |>.toArray
  let G0 : GameDef :=
    { name := s!"Made-up {profile} {seed}", resources, pieces
      map := { spotCount := nspots, links, regions }
      diceCount := dice, diceSides := sides, targetPoints := target, rounds, bankRate := bank
      setupPieces }
  if !G0.checks then throw s!"the made-up game {profile} {seed} does not pass G.checks"
  -- Founding laws, each kept only if the game still passes.
  let names := rs.toList
  let (nfound, r1) := pick r z.founding; r := r1
  let mut G := G0
  let mut tries := 0
  let mut i := 0
  while G.foundingLaws.length < nfound && tries < 4 * nfound + 4 do
    tries := tries + 1
    let (t, r1) := lawTexts rs ks #[] i r; r := r1
    i := i + 1
    for (L, _) in parsed names [t] do
      let G' := { G with foundingLaws := G.foundingLaws ++ [L] }
      if G'.checks then G := G'
  -- The library for votes.
  let mut texts : List String := []
  for _ in [0:12] do
    let (t, r1) := lawTexts rs ks spotKinds i r; r := r1
    i := i + 1
    texts := texts ++ [t]
  let library := (parsed names texts).toArray
  let xy := (List.range nspots).toArray.map fun v =>
    let a := 2 * 3.14159265 * Float.ofNat v / Float.ofNat (max 1 nspots)
    (Float.cos a, Float.sin a)
  return (G, library, xy)

/-- The tables of a made-up game, from its id `gen-<profile>-<seed>`. -/
def tables? (id : String) : Option (Except String Tables) :=
  match id.splitOn "-" with
  | ["gen", profile, seed] =>
    some do
      let some n := seed.toNat? | throw s!"{id}: the seed must be a number"
      let (G, library, xy) ← make profile n
      return Tables.make id G Charter.minSeats Charter.maxSeats library xy
  | _ => none

end CharterRL.Gen
