import Charter.Words.State

/-!
# Placing a piece

When a build is allowed, what it costs, and what the board looks like after it.
-/

namespace Charter

namespace State
variable {G : GameDef}

/-- The piece at spot `v`, if there is one. -/
def pieceAt (s : State G) (v : Nat) : Option Piece :=
  s.pieces.find? fun x => x.loc == .spot v

/-- A piece is already on this link. -/
def linkTaken (s : State G) (l : Nat × Nat) : Bool :=
  s.pieces.any fun x => x.loc == .link l

/-- The spots one link away from `v`. -/
def neighbours (_s : State G) (v : Nat) : List Nat :=
  G.map.links.filterMap fun l =>
    if l.1 == v then some l.2 else if l.2 == v then some l.1 else none

/-- `p` has a piece at spot `v`, or a link that reaches it. -/
def reaches (s : State G) (p : Seat) (v : Nat) : Bool :=
  s.pieces.any fun x =>
    x.owner == p &&
      match x.loc with
      | .spot w => w == v
      | .link l => l.1 == v || l.2 == v

/-- A running deal forbids this build. It binds only those who signed it. -/
def blockedByDeal (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : Bool :=
  s.deals.any fun d =>
    d.deal.signers.contains p &&
    d.deal.terms.any fun
      | .noBuild x k' spots =>
          x == p && k' == k &&
            match loc with
            | .spot v => spots.contains v
            | .link l => spots.contains l.1 || spots.contains l.2
      | _ => false

/-- `p` may put a piece with this placement rule at `loc`. Cost is checked separately. -/
def placementOk (s : State G) (p : Seat) (d : PieceDef) (loc : Loc) : Bool :=
  match d.placement, loc with
  | .link, .link l =>
      G.map.links.contains l && !s.linkTaken l && (s.reaches p l.1 || s.reaches p l.2)
  | .spot, .spot v =>
      decide (v < G.map.spotCount) && (s.pieceAt v).isNone &&
        (s.neighbours v).all (fun w => (s.pieceAt w).isNone) && s.reaches p v
  | .upgrade k, .spot v => s.pieces.contains ⟨p, k, .spot v⟩
  | .attach k, .spot v =>
      s.pieces.contains ⟨p, k, .spot v⟩ && !s.pieces.contains ⟨p, d.name, .spot v⟩
  | _, _ => false

/-- Everything required for `p` to build this piece in the actions phase. -/
def canPlace (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : Bool :=
  s.phase == .actions && s.isTurnOf p &&
  decide (s.actionsThisTurn p < maxActionsPerTurn) &&
  match s.rules.piece? k with
  | some d =>
      s.affords p d.cost && s.placementOk p d loc &&
      decide (s.countOf p k < d.limit) && !s.blockedByDeal p k loc
  | none => false

/-- Paying for a piece: each resource goes from the builder to the bank. -/
def costEntries (s : State G) (p : Seat) (k : PieceKind) : List Entry :=
  (s.costOf k).map fun x =>
    { src := .player p, dst := .bank, res := x.1, amount := x.2, reason := .cost }

/-- The pieces after `p` places `k` at `loc`. The new piece goes last. An upgrade also removes the
one piece of `p`'s it replaces. Nothing else changes. -/
def placedPieces (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : List Piece :=
  let kept :=
    match (s.rules.piece? k).map (·.placement), loc with
    | some (.upgrade old), .spot v => s.pieces.erase ⟨p, old, .spot v⟩
    | _, _ => s.pieces
  kept ++ [⟨p, k, loc⟩]

end State

end Charter
