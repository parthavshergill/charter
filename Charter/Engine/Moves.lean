import Charter.Engine.Basic

/-!
# Moves

One function per move. Each returns the new state, or a reason to reject the move. Counting the
action and looking for a winner happen in `step`, around these functions.
-/

namespace Charter.State
variable {G : GameDef}

/-- Where a setup piece can go. It is free, so a spot needs no link to the seat's own pieces. -/
def setupPlacementOk (s : State G) (p : Seat) (d : PieceDef) (loc : Loc) : Bool :=
  match d.placement, loc with
  | .spot, .spot v =>
      decide (v < G.map.spotCount) && (s.pieceAt v).isNone &&
        (s.neighbours v).all (fun w => (s.pieceAt w).isNone)
  | _, _ => s.placementOk p d loc

/-- Everything required for `p` to place this piece in setup: it is `p`'s turn, it is the next
piece on the game's setup list, and it fits. -/
def canSetupPlace (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : Bool :=
  s.phase == .setup && s.isTurnOf p &&
  decide (s.actionsThisTurn p < maxActionsPerTurn) &&
  G.setupPieces[s.actionsThisTurn p]? == some k &&
  match s.rules.piece? k with
  | some d => s.setupPlacementOk p d loc && decide (s.countOf p k < d.limit)
  | none => false

end Charter.State

namespace Charter.Engine

variable {G : GameDef}

/-! ## Placing a piece -/

/-- A build in the actions phase. It is accepted exactly when `canPlace` says so. -/
def buildBody (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : Except String (State G) :=
  if s.canPlace p k loc then
    let cost := s.costEntries p k
    match record s (cost ++ lawEntries (s.afterPosting cost) (.build p k)) with
    | .ok s1 => .ok { s1 with
        pieces := s.placedPieces p k loc
        builtThisRound := s.builtThisRound ++ [(p, k)] }
    | .error m => .error m
  else .error "this piece cannot be placed there now"

/-- A free setup placement. No resources move. -/
def setupBody (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : Except String (State G) :=
  if s.canSetupPlace p k loc then .ok { s with pieces := s.placedPieces p k loc }
  else .error "this setup piece cannot be placed there now"

/-- A place move, by phase. -/
def placeBody (s : State G) (p : Seat) (k : PieceKind) (loc : Loc) : Except String (State G) :=
  match s.phase with
  | .setup => setupBody s p k loc
  | .actions => buildBody s p k loc
  | .ended => .error "the game has ended"

/-! ## Trading -/

/-- Trade with the bank at the current rate. -/
def bankTradeBody (s : State G) (p : Seat) (give get : Res) : Except String (State G) :=
  if !(s.phase == .actions && s.isTurnOf p) then .error "you can trade with the bank on your turn"
  else if !(give != get && G.isRes give && G.isRes get) then .error "this is not a valid trade"
  else
    record s (s.bankTradeEntries p give get)

/-- An offer's bundle is not empty, names real resources once each, and moves something. -/
def offerBundleOk (G : GameDef) (b : Bundle) : Bool :=
  !b.isEmpty && G.bundleOk b && b.all fun x => decide (0 < x.2)

/-- Make an offer on your turn. An offer lasts until the turn ends. -/
def offerBody (s : State G) (p : Seat) (to : Option Seat) (give get : Bundle) :
    Except String (State G) :=
  if !(s.phase == .actions && s.isTurnOf p) then .error "you can make offers on your turn"
  else if !(offerBundleOk G give && offerBundleOk G get) then .error "this is not a valid offer"
  else if !s.affords p give then .error "you do not have what you offer"
  else
    let toOk :=
      match to with
      | some q => s.turnOrder.contains q && q != p && !s.tradeBlocked p q
      | none => true
    if !toOk then .error "you cannot make an offer to that seat"
    else .ok { s with
      offers := s.offers ++ [⟨s.nextOfferId, p, to, give, get⟩]
      nextOfferId := s.nextOfferId + 1 }

/-- Accept an offer. Both sides pay in full, or the whole event is rejected. -/
def acceptBody (s : State G) (p : Seat) (offerId : Nat) : Except String (State G) :=
  if s.phase != .actions then .error "offers can be accepted only in the actions phase"
  else
    match s.offers.find? (·.id == offerId) with
    | none => .error "there is no such offer"
    | some o =>
      if o.src == p then .error "you cannot accept your own offer"
      else if !(o.to.isNone || o.to == some p) then .error "this offer is for another seat"
      else if s.tradeBlocked p o.src then .error "a deal forbids this trade"
      else
        match record s (offerEntries o p) with
        | .ok s1 => .ok { s1 with offers := s.offers.filter (·.id != offerId) }
        | .error m => .error m

/-- Take back your own offer. -/
def cancelBody (s : State G) (p : Seat) (offerId : Nat) : Except String (State G) :=
  if s.phase != .actions then .error "offers can be cancelled only in the actions phase"
  else if s.offers.any (fun o => o.id == offerId && o.src == p) then
    .ok { s with offers := s.offers.filter (·.id != offerId) }
  else .error "you have no offer with that id"

/-- Every move except ending the turn. `step` handles that one first. -/
def moveBody (s : State G) (p : Seat) : Move → Except String (State G)
  | .place k loc => placeBody s p k loc
  | .bankTrade give get => bankTradeBody s p give get
  | .offer to give get => offerBody s p to give get
  | .accept offerId => acceptBody s p offerId
  | .cancel offerId => cancelBody s p offerId
  | .endTurn => .error "only the current seat can end its turn"

end Charter.Engine
