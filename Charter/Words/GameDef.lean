import Charter.Words.RuleLanguage

/-!
# What a game is

A game is data. Claude can write one, and `GameDef.Valid` in `Words/Valid.lean` checks it.
-/

namespace Charter

/-- A whole game, as data. It can have founding laws. These are in force from the start, exactly as if
a majority had passed them, in order, and a majority can repeal them like any other law. -/
structure GameDef where
  name : String
  resources : List ResourceDef
  pieces : List PieceDef
  map : MapGraph
  diceCount : Nat
  diceSides : Nat
  targetPoints : Nat
  rounds : Nat
  /-- How many of one resource the bank takes for one of another. -/
  bankRate : Nat
  /-- What each seat places, free, in each setup turn. -/
  setupPieces : List PieceKind
  /-- The laws in force when a game starts, in the order they apply. -/
  foundingLaws : List Law := []
  deriving Repr

/-- How much of a resource the game has. A resource not in the game has 0. -/
def GameDef.stockOf (G : GameDef) (r : Res) : Nat :=
  ((G.resources.find? (·.name == r)).map (·.stock)).getD 0

/-- This resource is in the game. -/
def GameDef.isRes (G : GameDef) (r : Res) : Bool :=
  G.resources.any (·.name == r)

/-- A bundle names only real resources, and names each one once. -/
def GameDef.bundleOk (G : GameDef) (b : Bundle) : Bool :=
  (b.all fun x => G.isRes x.1) && (b.map (·.1)).eraseDups.length == b.length

/-- A link with its two ends in order, so `(0, 1)` and `(1, 0)` are the same link. -/
def linkEnds (l : Nat × Nat) : Nat × Nat := (Nat.min l.1 l.2, Nat.max l.1 l.2)

/-- A piece of this kind can be built and stands on a spot, directly or on other pieces that do. An
`upgrade` or `attach` needs its target on a spot, so a target on a link never works. `fuel` is the
number of kinds, so a chain that loops back on itself gives `false`. -/
def canStandOnSpot (pieces : List PieceDef) : Nat → PieceKind → Bool
  | 0, _ => false
  | fuel + 1, k =>
    match pieces.find? (·.name == k) with
    | some d =>
      decide (0 < d.limit) &&
        match d.placement with
        | .spot => true
        | .link => false
        | .upgrade j | .attach j => canStandOnSpot pieces fuel j
    | none => false

/-- Under these pieces and this map, a piece with this placement is not ruled out for ever. Its limit
is above 0, the map has a place of the right kind, and the piece it goes on can stand on a spot. -/
def GameDef.canBuild (G : GameDef) (pieces : List PieceDef) (p : PieceDef) : Bool :=
  decide (0 < p.limit) &&
    match p.placement with
    | .link => !G.map.links.isEmpty
    | .spot => decide (0 < G.map.spotCount)
    | .upgrade k | .attach k => canStandOnSpot pieces pieces.length k

/-- Every piece of the game's own can be built. -/
def GameDef.placementOk (G : GameDef) (p : PieceDef) : Bool := G.canBuild G.pieces p

end Charter
