import Lean.Data.Json
import Charter.Engine
import Charter.Scene.OfState
import Server.Text
import Server.Rules
import Server.Secrecy

/-!
# What a law would do at this table, right now

The preview shown before a vote. Each case is the difference between the game with the law and the game
without it, so cases that change nothing do not appear. It does no sums of its own. Everything comes
from the functions the commandments state:

* **The next turn change** comes from `Engine.predictNextTurn`, which is the code `step` runs. Commandment
  X says it is exact if the law passes and the turn then ends. On a last turn its entries are the round's
  end and then the whole roll, so a roll's case is what comes after the round's end. That includes the
  laws that react to the roll.
* **A build** comes from the entries commandment VII states: the cost first, and then the laws reacting
  to it, from the books with the cost paid. So a law that reads holdings sees what the builder has left.

Figures are for the state it is given. Moves made later can change them, and the screen says so.

One case has no theorem behind it: the end of a round when this is not the round's last turn. It says
what the round's end would pay if nothing changed before it, using the same function. The figures can
move as the round goes on, and that is why the screen words it as it does.
-/

namespace CharterServer.Preview
open Lean Charter

variable {G : GameDef}

/-- One account's change in one resource. `who = none` is the treasury. -/
structure Row where
  who : Option Nat
  res : Res
  delta : Int
  deriving BEq

/-- One seat's change in how many of a kind of piece it owns. -/
structure PieceRow where
  who : Nat
  kind : PieceKind
  delta : Int
  deriving BEq

structure Section where
  whenText : String
  dice : Bool
  rows : List Row
  pieces : List PieceRow := []

def netOf (es : List Entry) (a : Account) (r : Res) : Int :=
  es.foldl (fun acc e =>
    if e.res != r then acc else
    let gain : Int := if e.dst == a then e.amount else 0
    let loss : Int := if e.src == a then e.amount else 0
    acc + gain - loss) 0

/-- The change from `before` to `after`, for players and the treasury, without zeros. -/
def rowsOf (s : State G) (before after : List Entry) : List Row :=
  let accts : List (Option Nat × Account) :=
    s.turnOrder.map (fun p => (some p, Account.player p)) ++ [(none, Account.treasury)]
  accts.flatMap fun (who, a) =>
    (G.resources.map (·.name)).filterMap fun r =>
      let d := netOf after a r - netOf before a r
      if d == 0 then none else some { who, res := r, delta := d }

/-- The change the law makes to what each seat owns: `lawBefore` to `lawAfter` with it, against `before` to
`after` without it. So a law already moving pieces does not count as this law's doing. -/
def pieceRowsOf (s : State G) (before after lawBefore lawAfter : List Piece) : List PieceRow :=
  let kinds := ((before ++ after ++ lawBefore ++ lawAfter).map (·.kind)).eraseDups
  let count (ps : List Piece) (p : Nat) (k : PieceKind) : Int :=
    ((ps.filter fun x => x.owner == p && x.kind == k).length : Int)
  s.turnOrder.flatMap fun p =>
    kinds.filterMap fun k =>
      let d := (count lawAfter p k - count lawBefore p k) - (count after p k - count before p k)
      if d == 0 then none else some { who := p, kind := k, delta := d }

/-- The pieces after the laws act at a round's end, whichever turn this is. On a round's last turn this is
`piecesBeforeRoll`. -/
def piecesAtRoundEnd (x : State G) : List Piece :=
  applyOrders x.rules (lawOrders (x.afterPosting x.duePayments) .roundEnd) x.pieces

def rollWords (all rs : List Nat) : String :=
  if rs.length == all.length then "On every roll" else
  s!"On a roll of {Charter.Text.andList (rs.map toString)}"

/-- What the next turn change pays for this roll, after whatever it pays before the roll. -/
def afterTheRoll (x : State G) (roll : Nat) : List Entry :=
  (Engine.predictNextTurn G x roll).drop x.entriesBeforeRoll.length

/-- The change the law makes to what the next turn change pays before the roll. Only a last turn has
any such payments. -/
def beforeRollRows (s s' : State G) : List Row :=
  rowsOf s s.entriesBeforeRoll s'.entriesBeforeRoll

/-- The change the law makes to what the next turn change pays for this roll. -/
def rollRows (s s' : State G) (roll : Nat) : List Row :=
  rowsOf s (afterTheRoll s roll) (afterTheRoll s' roll)

/-- What a build makes the books do, as commandment VII states it: the cost, then the laws reacting to
it with the cost paid. -/
def buildEntries (x : State G) (p : Nat) (k : PieceKind) : List Entry :=
  x.costEntries p k ++ lawEntries (x.afterPosting (x.costEntries p k)) (.build p k)

/-- The change the law makes to what this build does. -/
def buildRows (s s' : State G) (p : Nat) (k : PieceKind) : List Row :=
  rowsOf s (buildEntries s p k) (buildEntries s' p k)

/-- This seat can pay for this piece now, under these rules. If it cannot, `afterPosting` cannot show
what it would have left, so there are no exact figures to give. -/
def canPay (x : State G) (p : Nat) (k : PieceKind) : Bool :=
  (x.books.postAll (x.costEntries p k)).isSome

/-- A law that reacts only to the end of a round or to a build cannot change what a roll pays, unless the
turn that just ended closes the round. So its preview need not work out the dice. -/
def rollsCannotChange (s : State G) (L : Law) : Bool :=
  !s.isLastTurn && L.clauses.all fun
    | .onRoundEnd _ | .onBuild .. => true
    | _ => false

/-- Rolls that change something, likeliest first, with equal cases joined. -/
def rollSections (s s' : State G) (L : Law) : List Section :=
  let rolls := if rollsCannotChange s L then [] else Scene.rollsOf G
  let pieceRows (r : Nat) : List PieceRow :=
    pieceRowsOf s s.piecesBeforeRoll (s.turnPieces r) s'.piecesBeforeRoll (s'.turnPieces r)
  let cases := (rolls.map fun r => (r, (rollRows s s' r, pieceRows r))).filter fun c =>
    !c.2.1.isEmpty || !c.2.2.isEmpty
  let grouped : List (List Nat × (List Row × List PieceRow)) := cases.foldl (fun acc (r, what) =>
    if acc.any (·.2 == what) then
      acc.map fun x => if x.2 == what then (x.1 ++ [r], x.2) else x
    else acc ++ [([r], what)]) []
  let weight (g : List Nat × (List Row × List PieceRow)) : Nat := (g.1.map (Scene.chanceOf G)).sum
  let sorted := (grouped.toArray.qsort fun a b => weight a > weight b).toList
  -- These rows are the difference the law makes, and not payments. The words say so.
  sorted.map fun (rs, (rows, pieces)) =>
    { whenText := s!"{rollWords (Scene.rollsOf G) rs}, compared with today", dice := true, rows, pieces }

def buildSections (s s' : State G) (you : Option Nat) (names : Nat → String) : List Section :=
  match you, s.turnOrder.head? with
  | none, none => []
  | y?, first? =>
    let actor := (y?.orElse fun _ => first?).getD 0
    s'.rules.pieces.filterMap fun d =>
      if !canPay s' actor d.name then none else
      let rows := buildRows s s' actor d.name
      if rows.isEmpty then none else
      let who := if y?.isSome then "you build" else s!"{names actor} builds"
      some { whenText := s!"When {who} {Charter.Text.article d.name}", dice := false, rows }

def roundEndSections (s s' : State G) : List Section :=
  let pieces := pieceRowsOf s s.pieces (piecesAtRoundEnd s) s'.pieces (piecesAtRoundEnd s')
  let rows := if s.isLastTurn then beforeRollRows s s' else rowsOf s s.roundEndEntries s'.roundEndEntries
  if rows.isEmpty && pieces.isEmpty then [] else
  -- On any other turn this is not covered by commandment X: moves before the round's end can change it.
  [{ whenText := if s.isLastTurn then "When this turn ends" else "At the end of this round", dice := false, rows, pieces }]

/-- Kinds of piece whose build this law changes, but which this seat cannot pay for today. -/
def unpaidBuildNotes (s s' : State G) (actor : Nat) : List String :=
  s'.rules.pieces.filterMap fun d =>
    if canPay s' actor d.name then none else
    if (buildRows s s' actor d.name).isEmpty then none else
    some s!"It also acts on {Charter.Text.article d.name}, which this seat cannot pay for today, so there are no figures for that yet."

/-- A law that waits on the round or the dice can show nothing now and still act later. -/
def waitingNote (L : Law) : List String :=
  let reads := (if Rules.lawReadsWord L "round" then ["the round"] else []) ++
    (if Rules.lawReadsWord L "rolled" then ["the dice"] else [])
  if reads.isEmpty then [] else
  [s!"This law reads {Charter.Text.andList reads}, so it may act later than this shows. Read its source."]

def ruleNotes (s s' : State G) : List String :=
  let bank := if s'.rules.bankRate != s.rules.bankRate then
      [s!"Today the bank takes {s.rules.bankRate} for 1."] else []
  let worth := s'.rules.worth.filterMap fun x =>
    if s.rules.worth.contains x then none else
    some s!"Each {x.1} in a seat's own hand would be worth {x.2} {if x.2 == 1 then "point" else "points"}."
  let costs := s'.rules.pieces.filterMap fun d =>
    match s.rules.piece? d.name with
    | some old => if old.cost != d.cost then some s!"Today {Charter.Text.article d.name} costs {Charter.Text.bundleText old.cost}." else none
    | none => none
  let gone := s.rules.pieces.filterMap fun d =>
    if (s'.rules.piece? d.name).isNone then some s!"The {d.name} would no longer exist." else none
  bank ++ worth ++ costs ++ gone

def rowJson (r : Row) : Json :=
  Json.mkObj [("seat", toJson r.who), ("res", toJson r.res), ("delta", toJson r.delta)]

def pieceRowJson (r : PieceRow) : Json :=
  Json.mkObj [("seat", toJson r.who), ("kind", toJson r.kind), ("delta", toJson r.delta)]

def sectionJson (x : Section) : Json :=
  Json.mkObj [("when", toJson x.whenText), ("dice", toJson x.dice),
    ("rows", Json.arr (x.rows.map rowJson).toArray),
    ("pieces", Json.arr (x.pieces.map pieceRowJson).toArray)]

/-- What a law's `now` clauses do, the moment it passes. It is the first thing that happens. -/
def nowSection (s s' : State G) (L : Law) : List Section :=
  let rows := rowsOf s [] (s.decreeEntries L)
  let pieces := pieceRowsOf s [] [] s.pieces s'.pieces
  if rows.isEmpty && pieces.isEmpty then [] else
  [{ whenText := "The moment this passes", dice := false, rows, pieces }]

/-- This law's figures change when seats declare other numbers. A law in force that reads declarations
may have nothing to do with this law's figures, so this tries it: each seat declares a different large
number, and the figures are compared. -/
def figuresMoveWithDeclared (s : State G) (id : Nat) (L : Law) (you : Option Nat) (names : Nat → String) : Bool :=
  let figures (x : State G) : String :=
    let x' := x.withLaw id L
    (Json.arr ((nowSection x x' L ++ roundEndSections x x' ++ buildSections x x' you names ++ rollSections x x' L).map sectionJson).toArray).compress
  figures s != figures { s with declared := fun p _ => maxDeclared - p }

/-- The preview of a law for one viewer, as the screen shows it. -/
def lawPreview (s : State G) (id : Nat) (L : Law) (you : Option Nat) (names : Nat → String) : Json :=
  let s' := s.withLaw id L
  -- The game as the vote would leave it, if it ends there. It goes through `checkWin`, as the vote does.
  let final : Option (State G) := match Engine.checkWin s' with
    | .ok x => if x.phase == Phase.ended then some x else none
    | .error _ => none
  let winner := final.bind (·.winner)
  let points := s.turnOrder.filterMap fun p =>
    let a := s.pointsOf p
    let b := s'.pointsOf p
    if a == b then none else
    some (Json.mkObj [("seat", toJson p), ("from", toJson a), ("to", toJson b),
      ("wins", toJson (winner == some p))])
  let ends := L.clauses.any Clause.isEndGame
  let rolls := if ends then [] else rollSections s s' L
  -- A law that ends the game does nothing after it passes.
  let sections := if ends then nowSection s s' L else
    nowSection s s' L ++ roundEndSections s s' ++ buildSections s s' you names ++ rolls.take 3
  let actor := (you.orElse fun _ => s.turnOrder.head?).getD 0
  let refused := match lawProblems G s L with
    | [] => []
    | ps => [s!"As things stand, this law would not take effect: {", ".intercalate ps}."]
  -- Declarations can change until the round ends, so figures that depend on them hold only if they stay.
  let dependsOnDeclared := Rules.lawReadsDeclared L ||
    (s.laws.any (Rules.lawReadsDeclared ·.2) && figuresMoveWithDeclared s id L you names)
  let declared := if dependsOnDeclared then
      ["These figures hold if declarations stay as they are. A seat can change its own on its turn."]
    else []
  let ending := match ends, final, winner with
    | true, some x, some w =>
      let who := if you == some w then "You" else names w
      let tied := (x.turnOrder.filter (x.pointsOf · == x.pointsOf w)).length > 1
      let tie := if tied then " A tie goes to the seat earlier in turn order." else ""
      toJson s!"This ends the game the moment it passes. {who} would win with {x.pointsOf w} points.{tie}"
    | _, _, _ => Json.null
  let notes := refused ++ waitingNote L ++ declared ++ ruleNotes s s' ++ unpaidBuildNotes s s' actor
  Json.mkObj
    [ ("sections", Json.arr (sections.map sectionJson).toArray)
    , ("moreRolls", toJson (rolls.length - min rolls.length 3))
    , ("points", Json.arr points.toArray)
    , ("ending", ending)
    , ("notes", toJson notes)
    , ("dice", toJson (!rolls.isEmpty))
    , ("nothing", toJson (sections.isEmpty && points.isEmpty && notes.isEmpty && ending.isNull)) ]

/-! ## The preview a seat may see

In a game that hides something, the preview is worked out from what `observe` gives the viewer, where
every hidden number is 0. Its figures can then be wrong, if they depend on something hidden. So the
figures are worked out a second time, with every hidden number set high. If the two differ, the screen
shows no figures, and says why. This second try is a test, not a proof: figures that pass it can still
depend on a hidden number in a way it does not reach. -/

/-- The observed state with every number hidden from this viewer set high. -/
def probe (sec : Secrecy) (v : Option Nat) (s : State G) : State G :=
  { s with
    books := fun a r => if sec.seesHolding v a r then s.books a r else 50
    declared := fun p r => if sec.seesDeclared v p then s.declared p r else 7 }

/-- A preview with its figures withheld. -/
def withheld : Json :=
  Json.mkObj
    [ ("sections", Json.arr #[]), ("moreRolls", toJson 0), ("points", Json.arr #[]), ("ending", Json.null)
    , ("notes", toJson ["What this law would do depends on things hidden from you, so there are no figures. Read its source."])
    , ("dice", toJson false), ("nothing", toJson false), ("withheld", toJson true) ]

/-- **The preview of a law, as this viewer may see it.** It reads the state only through `observe`. -/
def seatPreview (sec : Secrecy) (s : State G) (id : Nat) (L : Law) (you : Option Nat) (names : Nat → String) : Json :=
  let o := observe sec you s
  let now := lawPreview o id L you names
  if sec.hidden.isEmpty && !sec.sealedDeclarations then now
  else if (lawPreview (probe sec you o) id L you names).compress == now.compress then now
  else withheld

/-- The preview for the person drafting a law. -/
def draftPreview (sec : Secrecy) (s : State G) (id : Nat) (L : Law) (you : Nat) (names : Nat → String) : Json :=
  seatPreview sec s id L (some you) names

end CharterServer.Preview
