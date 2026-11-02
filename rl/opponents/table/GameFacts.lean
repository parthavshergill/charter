import Charter.Scene.OfState

/-!
# What any game's definition says about it

These read a `GameDef` and name no pack, so the bot's policy can use them without seeing the list of
packs in `Server/Spec.lean`.
-/

namespace CharterServer
open Charter

/-! ## Counters

A game can have a resource that no piece costs. Nobody wants it for itself, so it is a
counter that laws read, such as a flag a law keeps in the treasury. The screen and the Claude seats leave it out of hands,
trades and what a corner pays. It is still in the books and the laws' text, and the rules treat it like
any other resource. -/

/-- This resource is a counter and not a good. -/
abbrev markRes := Scene.markRes

/-- The resources a person trades and holds. -/
def goodsOf (G : GameDef) : List Res := (G.resources.map (·.name)).filter (!markRes G ·)

/-- The regions that pay goods. -/
def paidRegions (G : GameDef) : List Region := G.map.regions.filter (!markRes G ·.res)

/-! ## What a game's pieces are for

The policies and the chronicle ask these, so they need no piece names. -/

/-- The game's own piece that goes on a spot, such as a settlement. -/
def spotPiece (G : GameDef) : Option PieceDef :=
  G.pieces.find? fun d => match d.placement with
    | .spot => true
    | _ => false

/-- The game's own piece that goes on a link, such as a road. -/
def linkPiece (G : GameDef) : Option PieceDef :=
  G.pieces.find? fun d => match d.placement with
    | .link => true
    | _ => false

/-- The game's own piece that replaces another, such as a city, and the piece it replaces. -/
def upgradePiece (G : GameDef) : Option (PieceDef × PieceKind) :=
  G.pieces.findSome? fun d => match d.placement with
    | .upgrade k => some (d, k)
    | _ => none

end CharterServer
