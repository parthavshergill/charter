import Charter.Scene.OfState

/-!
# Does a pack have a look for everything?

This is a build check, and it is not a theorem. `Server/Spec.lean` runs it on every pack. It says in
words what is missing, so the person or agent adding a pack can act on the message.
-/

namespace Charter.Scene

/-- The marks drawn in `web/icons.js`. -/
def builtinMarks : List String :=
  [ "grain", "timber", "ore", "wool", "brick", "helium", "alloy", "ice", "crystal", "laurel", "alarm"
  , "road", "settlement", "city", "made", "knight", "relic", "wreath", "harbor" ]

/-- The colour tokens a pack can set, as in `web/look.js`. -/
def colorTokens : List String :=
  [ "walnut-0", "walnut-1", "walnut-2", "walnut-3", "brass", "vellum", "vellum-2", "vellum-3"
  , "ink", "ink-2", "ink-3", "gold", "gold-2", "gold-ink", "wax", "wax-2", "pale", "pale-2" ]

/-- The fonts a pack can choose, as in `web/look.js`. -/
def fontNames : List String := ["", "book", "slab", "humanist", "rounded", "typewriter"]

/-- The most triangles one model may have, and the most mesh file triangles one full scene may have.
`docs/process/reskins.md` says how these were measured. `web/vendor/meshfile.js` refuses a file over
the size for the ground. -/
def maxModelTriangles : Nat := 1500
def maxGroundTriangles : Nat := 12000
def maxSceneTriangles : Nat := 150000

def isHexColor (s : String) : Bool :=
  match s.toList with
  | '#' :: ds => ds.length == 6 && ds.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  | _ => false

def isPaint (s : String) : Bool := s == "none" || s == "currentColor" || isHexColor s

def isPathData (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 4000 && s.toList.all fun c => c.isDigit || "MmLlHhVvCcSsQqTtAaZzeE.,+- ".toList.contains c

/-- How much a text colour stands out from its background, from 1 up. Reading needs about 4.5. -/
def contrast (a b : String) : Float :=
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - 48 else if c.toNat ≥ 97 then c.toNat - 87 else c.toNat - 55
  let channel (s : String) (i : Nat) : Float :=
    let ds := s.toList
    let v := (16 * digit (ds.getD (1 + 2 * i) '0') + digit (ds.getD (2 + 2 * i) '0')).toFloat / 255.0
    if v ≤ 0.04045 then v / 12.92 else Float.pow ((v + 0.055) / 1.055) 2.4
  let lum (s : String) : Float := 0.2126 * channel s 0 + 0.7152 * channel s 1 + 0.0722 * channel s 2
  let (x, y) := (lum a, lum b)
  (max x y + 0.05) / (min x y + 0.05)

/-- Do these parts show this seat's colour? -/
def showsColor (parts : List Part) (c : UInt32) : Bool :=
  parts.any fun p => (p.rgb &&& 0xFFFFFF) == (c &&& 0xFFFFFF)

/-- The model a piece of the game itself has, if it has one. -/
def pieceModel (t : Theme) (d : PieceDef) (seat : Nat) : Option (List Part) :=
  match d.placement with
  | .link => some (t.linkModel d.name seat)
  | _ =>
    match t.shape d.name with
    | some .settlement => some (t.smallModel 7 seat 0)
    | some .city => some (t.largeModel 7 seat 0)
    | _ => t.ownModel d.name seat

/-- Everything a pack's look lacks or has wrong, in words. Empty means it is complete. -/
def lookProblems (G : GameDef) (L : Layout) : List String :=
  let t := L.theme
  let hasMark (n : String) : Bool :=
    t.look.icons.any (·.1 == n) || t.look.marks.any fun (k, m) => k == n && builtinMarks.contains m
  let onTiles := L.tiles.filterMap (·.res)
  let resources := G.resources.flatMap fun r =>
    (if hasMark r.name then [] else [s!"resource {r.name} has no icon"]) ++
    (if onTiles.contains r.name && t.ground (some r.name) == t.ground none && (t.tileTop (some r.name) 0).isEmpty
     then [s!"resource {r.name} has no tile of its own"] else [])
  let pieces := G.pieces.flatMap fun d =>
    (if hasMark d.name then [] else [s!"piece {d.name} has no icon"]) ++
    match pieceModel t d 0 with
    | none => [s!"piece {d.name} has no model"]
    | some _ =>
      let bad := (List.range t.seats.length).filter fun i =>
        !showsColor ((pieceModel t d i).getD []) (t.seats.getD i 0)
      if bad.isEmpty then [] else [s!"piece {d.name} does not show the owner's colour for seats {bad}"]
  let icons := t.look.icons.flatMap fun (n, ps) =>
    (if ps.isEmpty then [s!"the icon {n} is empty"] else []) ++
    ps.flatMap fun p =>
      (if isPathData p.d then [] else [s!"the icon {n} has a path that is not plain path data"]) ++
      (if isPaint p.fill && isPaint p.stroke then [] else [s!"the icon {n} has a colour that is not #rrggbb, none or currentColor"])
  let tokens := t.look.tokens.flatMap fun (k, v) =>
    (if colorTokens.contains k then [] else [s!"{k} is not a colour token"]) ++
    (if isHexColor v then [] else [s!"the token {k} is not #rrggbb"])
  let token (k fallback : String) : String := ((t.look.tokens.find? (·.1 == k)).map (·.2)).getD fallback
  let readable :=
    (if contrast (token "ink" "#2a1f14") (token "vellum" "#efe4c8") < 4.5 then ["ink on vellum is too hard to read"] else []) ++
    (if contrast (token "pale" "#e9dcc0") (token "walnut-1" "#1f140c") < 4.5 then ["pale on walnut is too hard to read"] else []) ++
    (if contrast (token "gold-ink" "#2b1d07") (token "gold" "#e8bb4d") < 4.5 then ["gold-ink on gold is too hard to read"] else [])
  let fonts :=
    [t.look.bodyFont, t.look.displayFont].filterMap fun f =>
      if fontNames.contains f then none else some s!"{f} is not a font from the fixed list"
  let monuments :=
    [("cost", MonumentKind.cost), ("points", .points), ("bank", .bank), ("harvest", .harvest), ("build", .build)
    , ("round end", .roundEnd), ("new piece", .newPiece "x"), ("repeal", .repeal)].filterMap fun (n, k) =>
      if (t.monumentModel k).isEmpty then some s!"the {n} monument is empty" else none
  let meshes := t.meshDefs.filterMap fun
    | .defineMeshFile id sha _ _ _ =>
      if id.toNat ≤ 8 then some s!"mesh id {id} is a primitive's id"
      else if sha.length == 64 && sha.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then none
      else some s!"mesh id {id} does not have a SHA-256"
    | _ => some "meshDefs holds a command that is not defineMeshFile"
  resources ++ pieces ++ icons ++ tokens ++ readable ++ fonts ++ monuments ++ meshes

end Charter.Scene
