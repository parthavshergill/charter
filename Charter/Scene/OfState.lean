import Charter.Scene.Render
import Charter.Engine

/-!
# The scene of a game state

The markers come from `Engine.legalMoves`, so the board offers exactly what `step` accepts.
-/

namespace Charter.Scene
open Games

/-- How a game's board is drawn: its tiles, where its spots and sides are, and its look. The order of
`spots` and `links` gives the ids the game definition uses. -/
structure Layout where
  tiles : List TileDef
  spots : List HexGrid.Vertex
  edges : List HexGrid.Edge
  links : List (Nat × Nat)
  theme : Theme
  /-- What the game calls its world, in a sentence: "the island". -/
  word : String
  deriving Inhabited

variable {G : GameDef}

/-- A resource no piece costs. Nobody wants it for itself, so it is a counter that laws
read, such as a flag a law keeps in the treasury. It is not money, so it adds nothing to the treasury's pile. -/
def markRes (G : GameDef) (r : Res) : Bool :=
  !(G.pieces.any fun d => d.cost.any (·.1 == r))

/-- How many outcomes of the dice give each total, for totals from 0 up. -/
def diceWays (G : GameDef) : List Nat :=
  let oneDie (ways : List Nat) : List Nat :=
    (List.range (ways.length + G.diceSides)).map fun t =>
      ((List.range G.diceSides).map fun d =>
        if t ≥ d + 1 then ways.getD (t - (d + 1)) 0 else 0).sum
  (List.range G.diceCount).foldl (fun w _ => oneDie w) [1]

/-- How many outcomes of the dice give this total. It is how often the total comes up. -/
def chanceOf (G : GameDef) (n : Nat) : Nat := (diceWays G).getD n 0

/-- Every total the dice can show. -/
def rollsOf (G : GameDef) : List Nat :=
  (List.range (G.diceCount * G.diceSides + 1)).filter (G.diceCount ≤ ·)

/-- How a piece looks under the rules in force. -/
def shapeOf (L : Layout) (s : State G) (k : PieceKind) : Shape :=
  match L.theme.shape k with
  | some x => x
  | none =>
    match s.rules.piece? k with
    | some { placement := .attach _, .. } => .custom k true
    | _ => .custom k false

/-- The first clause decides which monument a law raises. -/
def monumentOf (L : Law) : MonumentKind :=
  match L.clauses.head? with
  | some (.setCost _ _) => .cost
  | some (.setPoints _ _) => .points
  | some (.setBankRate _) => .bank
  | some (.onHarvest _) => .harvest
  | some (.onBuild _ _) => .build
  | some (.onRoundEnd _) => .roundEnd
  | some (.onRoll _) => .roll
  | some (.newPiece p) => .newPiece p.name
  | _ => .repeal

/-- The side of the map with this link, by the link's id. -/
def linkId (L : Layout) (l : Nat × Nat) : Option Nat := (L.links.idxOf? l)

/-- The pick id of a move's place on the board, if it has one. -/
def pickOf (L : Layout) : Move → Option UInt32
  | .place _ (.spot v) => some (spotPick v)
  | .place _ (.link l) => (linkId L l).map linkPick
  | _ => none

/-- The marker of a move, if it places something on the board. -/
def markerOf (L : Layout) (s : State G) : Move → Option (Marker × UInt32)
  | .place k (.spot v) =>
    (L.spots[v]?).map fun w =>
      let raised := match s.rules.piece? k with
        | some { placement := .upgrade _, .. } | some { placement := .attach _, .. } => true
        | _ => false
      (.spot w raised, spotPick v)
  | .place _ (.link l) => do
    let i ← linkId L l
    let e ← L.edges[i]?
    pure (.link e, linkPick i)
  | _ => none

/-- Keep the first marker for each pick id. Two moves on one spot share one marker. -/
def distinctMarkers (ms : List (Marker × UInt32)) : List (Marker × UInt32) :=
  (ms.foldl (fun (acc : List (Marker × UInt32)) m =>
    if acc.any (·.2 == m.2) then acc else m :: acc) []).reverse

/-- Which markers to draw. The legal moves stay the same: this only says what to show now. -/
inductive MarkerFilter where
  | all | none | kind (k : PieceKind)

def MarkerFilter.keeps : MarkerFilter → Move → Bool
  | .all, _ => true
  | .none, _ => false
  | .kind k, .place k' _ => k == k'
  | .kind _, _ => false

/-- The scene for a viewing seat. A seat sees markers only for its own legal moves. -/
def ofState (L : Layout) (s : State G) (viewer : Option Nat) (show_ : MarkerFilter := .all) : Input :=
  let spotPieces := s.pieces.filterMap fun x =>
    match x.loc with
    | .spot v => (L.spots[v]?).map fun w => { v := w, owner := x.owner, shape := shapeOf L s x.kind, id := v }
    | _ => none
  let linkPieces := s.pieces.filterMap fun x =>
    match x.loc with
    | .link l => do
      let i ← linkId L l
      let e ← L.edges[i]?
      pure { e := e, owner := x.owner, kind := x.kind }
    | _ => none
  let markers := match viewer with
    | none => []
    | some p => distinctMarkers (((Engine.legalMoves G s p).filter show_.keeps).filterMap (markerOf L s))
  { theme := L.theme
    tiles := L.tiles
    chance := chanceOf G
    spotPieces := spotPieces
    linkPieces := linkPieces
    markers := markers
    roll := s.lastRoll
    round := if s.phase == .setup then 0 else s.round
    treasuryTotal := (G.resources.map fun r => if markRes G r.name then 0 else s.balance .treasury r.name).sum
    laws := s.laws.map fun x => (x.1, monumentOf x.2) }

/-- The scene as bytes for the browser's player. -/
def sceneBytes (L : Layout) (s : State G) (viewer : Option Nat) (show_ : MarkerFilter := .all) : ByteArray :=
  renderBytes (ofState L s viewer show_)

end Charter.Scene
