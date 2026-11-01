import Lean.Data.Json
import EventLog
import Server.Game
import Server.Rules
import Server.Text

/-!
# The clerk's memory

The API keeps nothing between calls, so the game keeps a log for the clerk. Each table has one, in
`<data>/<code>.clerk`, next to the table's event log `<data>/<code>.db`. It uses the same event log
package, so it survives a restart. It is not the game's log: nothing in it reaches `Engine.step`, and
no route serves it to a browser.

A draft's memory has two parts:

- **Tabled**: proposals, who made them, and how they ended. This comes from the game itself, so it
  needs no copy in the clerk's log, and it is public.
- **The seat's own drafts**: its earlier requests and what came of them. A draft stays private until
  it is proposed, so `memoryBlock` keeps only the asking seat's notes and looks at no others. A rule the
  clerk suggested to a seat is a note of that seat too.

Memory goes in the user message, so the cached system block never changes. Everything in it is data
from players, marked as such, and it cannot close its own markers.
-/

namespace CharterServer.Clerk
open Lean Charter CharterServer.Game

/-! ## The bounds -/

/-- The most of a seat's own drafts a prompt can hold. -/
def maxOwnDrafts : Nat := 8
/-- The most tabled proposals a prompt can hold. Laws in force are always in the table section. -/
def maxTabled : Nat := 10
/-- The size of the whole memory section, in characters. The oldest entries go first. -/
def maxMemoryChars : Nat := 6000
/-- The longest words of a request that are kept. -/
def maxWordsKept : Nat := 400
def maxFormalKept : Nat := 1200
def maxNoteKept : Nat := 300
/-- The longest request a draft can have. -/
def maxRequestChars : Nat := 2000

/-! ## One note: a seat's request and what came of it -/

structure Note where
  seat : Nat
  round : Nat
  words : String
  /-- The formal text it produced, printed from the parsed proposal. -/
  formal : Option String := none
  /-- What the clerk said it changed. -/
  difference : Option String := none
  /-- Why no rule came of it. -/
  refused : Option String := none
  /-- The clerk suggested this rule, and `words` are the clerk's words. -/
  suggested : Bool := false
  /-- The advice the clerk gave with a suggestion. -/
  why : Option String := none
  deriving Repr, BEq

/-- Cut to a length, and say that it was cut. -/
def cut (n : Nat) (s : String) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " [cut]"

def noteJson (n : Note) : Json :=
  Json.mkObj <|
    [("seat", toJson n.seat), ("round", toJson n.round), ("words", toJson (cut maxWordsKept n.words))] ++
    (n.formal.map (fun x => [("formal", toJson (cut maxFormalKept x))])).getD [] ++
    (n.difference.map (fun x => [("difference", toJson (cut maxNoteKept x))])).getD [] ++
    (n.refused.map (fun x => [("refused", toJson (cut maxNoteKept x))])).getD [] ++
    (if n.suggested then [("suggested", toJson true)] else []) ++
    (n.why.map (fun x => [("why", toJson (cut maxNoteKept x))])).getD []

def noteOfJson (j : Json) : Option Note := do
  let seat ← jNat j "seat"
  let round ← jNat j "round"
  let words ← jStr j "words"
  return { seat, round, words, formal := jStr j "formal", difference := jStr j "difference"
           refused := jStr j "refused", suggested := (jBool j "suggested").getD false, why := jStr j "why" }

/-- Read a stored line. A line that does not read is skipped: memory only helps, so a bad line must
not stop a draft. -/
def noteOfLine (line : String) : Option Note :=
  (Json.parse line).toOption.bind noteOfJson

/-! ## The log file -/

def logPath (dataDir : System.FilePath) (code : String) : System.FilePath :=
  dataDir / s!"{code}.clerk"

/-- Append one note. The caller holds the lock on this table's log. -/
def append (log : EventLog.Log String) (n : Note) : IO Unit := do
  discard <| log.append (noteJson n).compress

/-- Every note of this table. The caller holds the lock on this table's log. -/
def readNotes (log : EventLog.Log String) : IO (List Note) := do
  let lines ← log.readFrom 0
  return lines.toList.filterMap noteOfLine

/-! ## Marking data -/

/-- Make a string safe to put between markers: a `<` that could start a marker gets a space after
it. `(< 7 x)` and `(<= 7 x)` stay as they are. -/
def neutralize (s : String) : String :=
  let cs := s.toList
  String.ofList ((cs.zip (cs.drop 1 ++ [' '])).flatMap fun (c, next) =>
    if c == '<' && (next.isAlpha || next == '/' || next == '!' || next == '?') then ['<', ' '] else [c])

/-- One line of data: no line breaks, and no markers. -/
def oneLine (s : String) : String :=
  neutralize (s.replace "\r" " " |>.replace "\n" " ")

/-! ## The memory section -/

def outcomeWords (t : Tabled) : String :=
  match t.outcome with
  | "open" => "still open"
  | "passed" => s!"passed, as law {t.id}"
  | "failed" => "voted down"
  | "lapsed" => "lapsed"
  | "started" => "signed and started"
  | o => o

def tabledFormal (t : Tabled) : String := Rules.printProposal t.body

def tabledLine (g : Game) (t : Tabled) : String :=
  let who := oneLine (g.nameOf t.by_)
  oneLine s!"- Round {t.round}, seat {t.by_} ({who}): {cut maxFormalKept (tabledFormal t)} Outcome: {outcomeWords t}."

/-- What a seat's own note came to, with whether it went on to be tabled. -/
def noteLine (g : Game) (n : Note) : String :=
  let table := match n.formal with
    | some f =>
      match g.tabled.toList.reverse.find? (fun (t : Tabled) => t.by_ == n.seat && tabledFormal t == f) with
      | some t => s!" Then proposed: {outcomeWords t}."
      | none => " Not proposed."
    | none => ""
  let result := match n.formal, n.refused with
    | some f, _ => s!"Result: {f}"
    | none, some r => s!"Refused: {r}"
    | none, none => "No result."
  let diff := match n.difference with
    | some d => s!" Difference stated: {d}"
    | none => ""
  let asked := if n.suggested then "Suggested to this player" else "Asked"
  let advice := match n.why with
    | some w => s!" Why given: {w}"
    | none => ""
  oneLine s!"- Round {n.round}. {asked}: \"{n.words}\" {result}{diff}{advice}{table}"

/-- Keep the newest lines that fit in `budget`, in their order. -/
def fitNewest (budget : Nat) (lines : List String) : List String :=
  let rec go : List String → Nat → List String → List String
    | [], _, acc => acc
    | l :: rest, left, acc =>
      if l.length + 1 ≤ left then go rest (left - l.length - 1) (l :: acc) else acc
  go lines.reverse budget []

/-- The memory for one seat's draft. It reads only that seat's notes, and the public record. -/
def memoryBlock (g : Game) (seat : Nat) (notes : List Note) : String :=
  let mine := (notes.filter (·.seat == seat)).reverse.take maxOwnDrafts |>.reverse
  let ownLines := fitNewest (maxMemoryChars / 2) (mine.map (noteLine g))
  let tabledLines := (g.tabled.toList.reverse.take maxTabled).reverse.map (tabledLine g)
  let public_ := fitNewest (maxMemoryChars - maxMemoryChars / 2) tabledLines
  if ownLines.isEmpty && public_.isEmpty then "" else
  let pub := if public_.isEmpty then "none yet" else "\n".intercalate public_
  let own := if ownLines.isEmpty then "none yet" else "\n".intercalate ownLines
  s!"<memory>\n<tabled>\n{pub}\n</tabled>\n<your_earlier_drafts>\n{own}\n</your_earlier_drafts>\n</memory>"

end CharterServer.Clerk
