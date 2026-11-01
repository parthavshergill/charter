import CharterRL.Env

/-!
# Tests of the environment against the engine

`charter-rl-check` runs these. Each test plays games with random legal actions and compares the environment with
`Engine.step`, or with itself. Each test that can pass by accident also runs once on a broken copy (a "seeded error"),
and must catch it.

* **mask**: for every action of every decision, the mask is 1 exactly when the engine accepts the action's event.
  Two kinds of event the engine accepts are not offered on purpose, and are counted apart: a declaration in a game
  where no law reads one, and a move by the voting seat while a vote is due.
* **determinism**: the same seed and the same actions give the same observations, masks and rewards.
* **seed**: changing `State.seed`, which decides the dice, changes no observation number.
* **renaming**: renaming every resource and piece, and reversing the order the game lists them in, gives the same
  observations, masks and rewards when each name keeps its row.
* **maps**: random maps pass the game's full `checks`.
-/

namespace CharterRL.Check
open Lean Charter CharterServer CharterServer.Bots CharterRL

/-- A small random number source for the tests. -/
structure Rng where
  x : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.x + 0x9E3779B97F4A7C15
  (scramble x, ⟨x⟩)

/-- A random legal action, from the mask. -/
def pick (r : Rng) (mask : ByteArray) : Option Nat × Rng :=
  let acts := (List.range mask.size).filter (mask.get! · == 1)
  if acts.isEmpty then (none, r) else
  let (x, r) := r.next
  (acts[(x.toNat % acts.length)]?, r)

/-- A lineup of callers only. -/
def callers (n : Nat) : Array SeatPlan := Array.replicate n { setup := none, play := none }

/-! ## The mask -/

/-- What the mask test found. -/
structure MaskCount where
  decisions : Nat := 0
  actions : Nat := 0
  offered : Nat := 0
  /-- Offered, and the engine refused. -/
  offeredRefused : Nat := 0
  /-- Not offered, and the engine accepted, with no reason. -/
  missing : Nat := 0
  /-- Not offered on purpose: a declaration no law reads. -/
  declareNotOffered : Nat := 0
  /-- Not offered on purpose: a move by the voting seat while a vote is due. -/
  moveWhileVoting : Nat := 0
  firstError : String := ""
  deriving Inhabited

def MaskCount.errors (c : MaskCount) : Nat := c.offeredRefused + c.missing

/-- The event an action would be with every restriction of `decode` lifted: declarations always, and moves for the
voting seat too. -/
def rawEvents (e : Env) (a : Nat) : List (Event × Bool) :=
  let T := { e.T with declares := true }
  match e.decision with
  | .none => []
  | .turn seat => ((decode T e.ep (.turn seat) a).map fun ev => (ev, false)).toList
  | .vote seat id L =>
    ((decode T e.ep (.vote seat id L) a).map fun ev => (ev, false)).toList ++
    ((decode T e.ep (.turn seat) a).map fun ev => (ev, true)).toList

def isDeclare : Event → Bool
  | .move _ (.declare ..) => true
  | _ => false

/-- Check one decision's mask against the engine. -/
def checkMask (c : MaskCount) (e : Env) (mask : ByteArray) : MaskCount := Id.run do
  let mut c := { c with decisions := c.decisions + 1 }
  let s := e.play.state
  for a in [0:actSize] do
    c := { c with actions := c.actions + 1 }
    let on := mask.get! a == 1
    let evs := rawEvents e a
    let accepted := evs.filter fun (ev, _) => (Engine.step e.G s ev).toOption.isSome
    let direct := evs.filter (!·.2)
    let directOk := direct.any fun (ev, _) => (Engine.step e.G s ev).toOption.isSome
    if on then
      c := { c with offered := c.offered + 1 }
      if !directOk then
        c := { c with offeredRefused := c.offeredRefused + 1
                      firstError := if c.firstError == "" then s!"action {a} is offered and the engine refuses it" else c.firstError }
    else if let some (ev, whileVoting) := accepted.head? then
      if whileVoting then c := { c with moveWhileVoting := c.moveWhileVoting + 1 }
      else if isDeclare ev && !e.T.declares then c := { c with declareNotOffered := c.declareNotOffered + 1 }
      else
        c := { c with missing := c.missing + 1
                      firstError := if c.firstError == "" then s!"action {a} is not offered and the engine accepts it" else c.firstError }
  return c

/-- Play `games` games of random legal actions and check every decision's mask, as `maskFn` makes it. -/
def maskTest (T : Tables) (settings : Settings) (seats games : Nat) (maskFn : Env → ByteArray)
    (maxDecisions : Nat := 400) : MaskCount := Id.run do
  let mut c : MaskCount := {}
  for g in [0:games] do
    let some e0 := (Env.start T settings (callers seats) (1000 + g)).toOption | continue
    let mut e := e0
    let mut r : Rng := ⟨UInt64.ofNat (77 + g)⟩
    for _ in [0:maxDecisions] do
      if e.decision.seat?.isNone then break
      let mask := maskFn e
      c := checkMask c e mask
      let (a, r') := pick r e.mask
      r := r'
      match a with
      | none => break
      | some a => e := e.step a
  return c

/-- Seeded error 1: end turn is always offered, so it is offered while a vote is due. -/
def maskEndAlways (e : Env) : ByteArray := e.mask.set! actEnd 1

/-- Seeded error 2: the last offered action is left out. -/
def maskDropLast (e : Env) : ByteArray :=
  let m := e.mask
  match (List.range m.size).reverse.find? (m.get! · == 1) with
  | some a => if a == actEnd then m else m.set! a 0
  | none => m

/-! ## Determinism, the seed, renaming -/

/-- What a test compares at each decision. -/
def snapshot (e : Env) : FloatArray × ByteArray × FloatArray := (e.observation, e.mask, e.rewards)

def sameFloats (a b : FloatArray) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => a.get! i == b.get! i

def sameSnap (a b : FloatArray × ByteArray × FloatArray) : Bool :=
  sameFloats a.1 b.1 && a.2.1.data == b.2.1.data && sameFloats a.2.2 b.2.2

/-- Play two games side by side with the same random actions. The number of decisions where they differ. `look`
changes the second game before each comparison, and `lookFirst` the first. Neither changes the games that play on. -/
def sideBySide (e1 e2 : Env) (seed : Nat) (maxDecisions : Nat := 400) (look : Env → Env := id) (lookFirst : Env → Env := id) : Nat × Nat := Id.run do
  let mut a := e1
  let mut b := e2
  let mut r : Rng := ⟨UInt64.ofNat seed⟩
  let mut diffs := 0
  let mut n := 0
  for _ in [0:maxDecisions] do
    n := n + 1
    if !sameSnap (snapshot (lookFirst a)) (snapshot (look b)) then diffs := diffs + 1
    if a.decision.seat?.isNone || b.decision.seat?.isNone then break
    let (x, r') := pick r a.mask
    r := r'
    match x with
    | none => break
    | some x =>
      a := a.step x
      b := b.step x
  return (diffs, n)

/-- The same game with another seed for the dice, and nothing else changed. -/
def reseeded (e : Env) : Env :=
  { e with play := { e.play with state := { e.play.state with seed := e.play.state.seed + 0x1234567 } } }

/-! ### A renamer over the game and its laws -/

section Rename
variable (res : Res → Res) (kind : PieceKind → PieceKind)

def rRef : ResRef → ResRef
  | .lit r => .lit (res r)
  | x => x

mutual
  def rExpr : Expr → Expr
    | .holding p r => .holding p (rRef res r)
    | .count p k => .count p (kind k)
    | .add a b => .add (rExpr a) (rExpr b)
    | .sub a b => .sub (rExpr a) (rExpr b)
    | .mul a b => .mul (rExpr a) (rExpr b)
    | .div a n => .div (rExpr a) n
    | .divBy a b => .divBy (rExpr a) (rExpr b)
    | .min a b => .min (rExpr a) (rExpr b)
    | .max a b => .max (rExpr a) (rExpr b)
    | .declared p r => .declared p (rRef res r)
    | .totalOver c a => .totalOver (rCond c) (rExpr a)
    | .mostOver c a => .mostOver (rCond c) (rExpr a)
    | .leastOver c a => .leastOver (rCond c) (rExpr a)
    | x => x

  def rCond : Cond → Cond
    | .lt a b => .lt (rExpr a) (rExpr b)
    | .le a b => .le (rExpr a) (rExpr b)
    | .eq a b => .eq (rExpr a) (rExpr b)
    | .and a b => .and (rCond a) (rCond b)
    | .or a b => .or (rCond a) (rCond b)
    | .not c => .not (rCond c)
    | .harvestedIs r => .harvestedIs (res r)
    | .yes => .yes
end

mutual
  def rEffect : Effect → Effect
    | .transfer s d r a => .transfer s d (rRef res r) (rExpr res kind a)
    | .movePiece s d k => .movePiece s d (kind k)
    | .forEach c body => .forEach (rCond res kind c) (rEffects body)
    | .when c body => .when (rCond res kind c) (rEffects body)

  def rEffects : List Effect → List Effect
    | [] => []
    | e :: es => rEffect e :: rEffects es
end

def rBundle (b : Bundle) : Bundle := b.map fun (r, n) => (res r, n)

def rPlacement : Placement → Placement
  | .upgrade k => .upgrade (kind k)
  | .attach k => .attach (kind k)
  | p => p

def rPiece (d : PieceDef) : PieceDef :=
  { d with name := kind d.name, cost := rBundle res d.cost, placement := rPlacement kind d.placement }

def rClause : Clause → Clause
  | .onHarvest b => .onHarvest (rEffects res kind b)
  | .onBuild k b => .onBuild (kind k) (rEffects res kind b)
  | .onRoundEnd b => .onRoundEnd (rEffects res kind b)
  | .onRoll b => .onRoll (rEffects res kind b)
  | .now b => .now (rEffects res kind b)
  | .setCost k b => .setCost (kind k) (rBundle res b)
  | .setPoints k n => .setPoints (kind k) n
  | .setBankRate n => .setBankRate n
  | .setWorth r n => .setWorth (res r) n
  | .newPiece p => .newPiece (rPiece res kind p)
  | .endGame => .endGame
  | .repeal i => .repeal i

def rLaw (L : Law) : Law := { L with clauses := L.clauses.map (rClause res kind) }

/-- The game with every resource and piece renamed, and both lists reversed. -/
def rGame (G : GameDef) : GameDef :=
  { G with
    resources := (G.resources.map fun d => { d with name := res d.name }).reverse
    pieces := (G.pieces.map (rPiece res kind)).reverse
    map := { G.map with regions := G.map.regions.map fun t => { t with res := res t.res } }
    setupPieces := G.setupPieces.map kind
    foundingLaws := G.foundingLaws.map (rLaw res kind) }
end Rename

def newRes (r : Res) : Res := "r" ++ toString (r.length * 7919 % 1000) ++ "_" ++ r.toUpper
def newKind (k : PieceKind) : PieceKind := "k_" ++ k.toUpper ++ "_x"

/-- The renamed game's environment, with each renamed resource and piece in the row its old name had. -/
def renamedEnv (T : Tables) (settings : Settings) (seats seed : Nat) (leak : Bool := false) : Except String Env := do
  let e ← Env.start T settings (callers seats) seed
  let G' := rGame newRes newKind T.G
  let T' := Tables.make T.id G' T.minSeats T.maxSeats ((T.library.zip T.libraryText).map fun (L, t) => (rLaw newRes newKind L, t)) T.spotXY
  let e' ← Env.start T' settings (callers seats) seed
  -- Put each renamed name in the row of its old name.
  let ep : Episode := { e.ep with
    rowRes := e.ep.rowRes.map newRes
    rowKind := e.ep.rowKind.map fun k => if k == "" then "" else newKind k }
  -- Seeded error: keep the renamed game's own rows, so a row's resource follows the list order.
  let ep := if leak then e'.ep else ep
  let G := e'.G
  let base := template T' ep G seats settings.moveRows
  let e'' : Env := { e' with ep, base, lawsSeen := [] }
  return e''

/-! ## Running them -/

def line (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Time a function over many games, in decisions per second, and observation cost. -/
def speed (T : Tables) (settings : Settings) (lineup : Array SeatPlan) (games : Nat) (obs : Bool) :
    IO (Float × Float × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut n := 0
  let mut sink : Float := 0
  for g in [0:games] do
    let some e0 := (Env.start T settings lineup (5000 + g)).toOption | continue
    let mut e := e0
    let mut r : Rng := ⟨UInt64.ofNat g⟩
    for _ in [0:2000] do
      if e.decision.seat?.isNone then break
      if obs then sink := sink + (e.observation.get! 0)
      let (a, r') := pick r e.mask
      r := r'
      match a with
      | none => break
      | some a =>
        e := e.step a
        n := n + 1
  let t1 ← IO.monoNanosNow
  let secs := Float.ofNat (t1 - t0) / 1e9
  if sink < 0 then IO.println ""
  return (Float.ofNat n / secs, Float.ofNat games / secs, n)

def fmt (x : Float) : String := toString (x.round)

end CharterRL.Check
