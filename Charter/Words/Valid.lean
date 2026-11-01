import Charter.Words.LawChecks
import Charter.Words.Dice

/-!
# Which games can run

`GameDef.Valid` checks a whole game. A founding law must pass the same rules as any other law.
-/

namespace Charter

/-- The checks on a game's own parts. All of them can be computed. -/
def GameDef.shapeChecks (G : GameDef) : Bool :=
  !G.resources.isEmpty && decide (G.resources.length ≤ maxResources) &&
  (G.resources.map (·.name)).eraseDups.length == G.resources.length &&
  G.resources.all (fun r => decide (r.stock ≤ maxStock)) &&
  !G.pieces.isEmpty && decide (G.pieces.length ≤ maxPieceKinds) &&
  (G.pieces.map (·.name)).eraseDups.length == G.pieces.length &&
  G.pieces.all (fun p => G.bundleOk p.cost) &&
  G.pieces.all G.placementOk &&
  decide (G.map.spotCount ≤ maxSpots) &&
  G.map.links.all (fun l => decide (l.1 < G.map.spotCount ∧ l.2 < G.map.spotCount ∧ l.1 ≠ l.2)) &&
  (G.map.links.map linkEnds).eraseDups.length == G.map.links.length &&
  G.map.regions.all (fun x => G.isRes x.res && x.spots.all (fun v => decide (v < G.map.spotCount))) &&
  decide (1 ≤ G.diceCount ∧ 2 ≤ G.diceSides ∧ G.diceCount ≤ 4 ∧ G.diceSides ≤ 20) &&
  decide (1 ≤ G.targetPoints) && decide (1 ≤ G.rounds ∧ G.rounds ≤ maxRoundsAllowed) &&
  decide (2 ≤ G.bankRate) && G.bundleOk G.lawFee &&
  G.setupPieces.all (fun k => G.pieces.any (·.name == k))

/-- Each founding law passes `lawProblems`, in order, in a new game with this many seats and with the
earlier founding laws in force. -/
def GameDef.foundingOkFrom (G : GameDef) (seats : Nat) : List (Nat × Law) → Nat → List Law → Bool
  | _, _, [] => true
  | laws, id, L :: Ls =>
    (lawProblems G { initialState G seats 0 [] with laws := laws } L).isEmpty &&
      G.foundingOkFrom seats (enact laws id L) (id + 1) Ls

/-- The founding laws pass at every allowed number of seats, since what a law can ask for depends on
how many seats there are. -/
def GameDef.foundingOk (G : GameDef) : Bool :=
  (List.range (maxSeats + 1)).all fun seats =>
    decide (seats < minSeats) || G.foundingOkFrom seats [] 0 G.foundingLaws

/-- The checks every game must pass. All of them can be computed. -/
def GameDef.checks (G : GameDef) : Bool := G.shapeChecks && G.foundingOk

/-- `G` passes the checks. The engine never checks this itself, so a server must. -/
def GameDef.Valid (G : GameDef) : Prop := G.checks = true

instance (G : GameDef) : Decidable G.Valid := inferInstanceAs (Decidable (G.checks = true))

end Charter
