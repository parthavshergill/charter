import Lean.Data.Json
import Charter.Engine
import Charter.Scene.OfState
import Server.Text
import Server.Rules

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

structure Section where
  whenText : String
  dice : Bool
  rows : List Row

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

def rollWords (rs : List Nat) : String :=
  let t := Charter.Text.andList (rs.map toString)
  if rs.length == 1 then s!"On a roll of {t}" else s!"On a roll of {t}"

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
  let cases := (rolls.map fun r => (r, rollRows s s' r)).filter (!·.2.isEmpty)
  let grouped : List (List Nat × List Row) := cases.foldl (fun acc (r, rows) =>
    if acc.any (·.2 == rows) then
      acc.map fun x => if x.2 == rows then (x.1 ++ [r], x.2) else x
    else acc ++ [([r], rows)]) []
  let weight (g : List Nat × List Row) : Nat := (g.1.map (Scene.chanceOf G)).sum
  let sorted := (grouped.toArray.qsort fun a b => weight a > weight b).toList
  sorted.map fun (rs, rows) => { whenText := rollWords rs, dice := true, rows }

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
  if s.isLastTurn then
    let rows := beforeRollRows s s'
    if rows.isEmpty then [] else [{ whenText := "When this turn ends", dice := false, rows }]
  else
    -- Not covered by commandment X: moves before the round's end can change this.
    let rows := rowsOf s s.roundEndEntries s'.roundEndEntries
    if rows.isEmpty then [] else [{ whenText := "At the end of this round", dice := false, rows }]

/-- Kinds of piece whose build this law changes, but which this seat cannot pay for today. -/
def unpaidBuildNotes (s s' : State G) (actor : Nat) : List String :=
  s'.rules.pieces.filterMap fun d =>
    if canPay s' actor d.name then none else
    if (buildRows s s' actor d.name).isEmpty then none else
    some s!"It also acts on {Charter.Text.article d.name}, which this seat cannot pay for today, so there are no figures for that yet."

def ruleNotes (s s' : State G) : List String :=
  let bank := if s'.rules.bankRate != s.rules.bankRate then
      [s!"Today the bank takes {s.rules.bankRate} for 1."] else []
  let worth := s'.rules.worth.filterMap fun x =>
    if s.rules.worth.contains x then none else
    some s!"Each {x.1} in a seat's own hand would be worth {x.2} points."
  let costs := s'.rules.pieces.filterMap fun d =>
    match s.rules.piece? d.name with
    | some old => if old.cost != d.cost then some s!"Today {Charter.Text.article d.name} costs {Charter.Text.bundleText old.cost}." else none
    | none => none
  let gone := s.rules.pieces.filterMap fun d =>
    if (s'.rules.piece? d.name).isNone then some s!"The {d.name} would no longer exist." else none
  bank ++ worth ++ costs ++ gone

def rowJson (r : Row) : Json :=
  Json.mkObj [("seat", toJson r.who), ("res", toJson r.res), ("delta", toJson r.delta)]

def sectionJson (x : Section) : Json :=
  Json.mkObj [("when", toJson x.whenText), ("dice", toJson x.dice),
    ("rows", Json.arr (x.rows.map rowJson).toArray)]

/-- The preview of a law for one viewer, as the screen shows it. -/
def lawPreview (s : State G) (id : Nat) (L : Law) (you : Option Nat) (names : Nat → String) : Json :=
  let s' := s.withLaw id L
  let points := s.turnOrder.filterMap fun p =>
    let a := s.pointsOf p
    let b := s'.pointsOf p
    if a == b then none else
    some (Json.mkObj [("seat", toJson p), ("from", toJson a), ("to", toJson b),
      ("wins", toJson (decide (G.targetPoints ≤ b)))])
  let rolls := rollSections s s' L
  let sections := roundEndSections s s' ++ buildSections s s' you names ++ rolls.take 3
  let actor := (you.orElse fun _ => s.turnOrder.head?).getD 0
  let refused := match lawProblems G s L with
    | [] => []
    | ps => [s!"As things stand, this law would not take effect: {", ".intercalate ps}."]
  -- Declarations can change until the round ends, so figures that read them hold only if they stay.
  let readsDeclared := Rules.lawReadsDeclared L || s.laws.any (Rules.lawReadsDeclared ·.2)
  let declared := if readsDeclared then
      ["These figures hold if declarations stay as they are. A seat can change its own on its turn."]
    else []
  let notes := refused ++ declared ++ ruleNotes s s' ++ unpaidBuildNotes s s' actor
  Json.mkObj
    [ ("sections", Json.arr (sections.map sectionJson).toArray)
    , ("moreRolls", toJson (rolls.length - min rolls.length 3))
    , ("points", Json.arr points.toArray)
    , ("notes", toJson notes)
    , ("dice", toJson (!rolls.isEmpty))
    , ("nothing", toJson (sections.isEmpty && points.isEmpty && notes.isEmpty)) ]

/-- The preview for the person drafting a law. -/
def draftPreview (s : State G) (id : Nat) (L : Law) (you : Nat) (names : Nat → String) : Json :=
  lawPreview s id L (some you) names

end CharterServer.Preview
