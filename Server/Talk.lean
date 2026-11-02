import Lean.Data.Json
import EventLog
import Server.Util

/-!
# Table talk

Public chat, private messages between seats, and a private confessional for each AI seat. Talk is not
a game event. It goes nowhere near `Engine.step`, and the engine's `Event` type does not know about
it. Each table has its own log, `<data>/<code>.talk`, next to its event log, and it survives a restart.
Each line records the event number it happened at, so a replay can show it at the right moment.

Who can read a line:

* A public line: everyone.
* A private line: the two seats. A spectator can read it once the table is open to spectators.
* A confessional or an exit interview: only a spectator, once the table is open to spectators.

A table is open to spectators when no person holds a seat, or when the game is over. So a person at a
live table cannot read the AI seats' secrets by opening the page with no token.
-/

namespace CharterServer.Talk
open Lean

/-- The longest line that is kept. -/
def maxChars : Nat := 800

structure Line where
  /-- The number of game events when this was said. -/
  event : Nat
  /-- `public`, `private`, `confession` or `interview`. -/
  kind : String
  /-- The seat that said it. -/
  by_ : Nat
  /-- The seat it was said to, for a private line. -/
  to : Option Nat := none
  text : String
  deriving Repr, BEq, Inhabited

def lineJson (l : Line) : Json :=
  Json.mkObj [("event", toJson l.event), ("kind", l.kind), ("by", toJson l.by_), ("to", toJson l.to), ("text", l.text)]

def lineOfJson (j : Json) : Option Line := do
  return { event := ← jNat j "event", kind := ← jStr j "kind", by_ := ← jNat j "by"
           to := jNat j "to", text := ← jStr j "text" }

/-- Can this viewer read this line? `viewer` is the seat, or `none` for a spectator. -/
def canSee (openToSpectators : Bool) (viewer : Option Nat) (l : Line) : Bool :=
  match l.kind with
  | "public" => true
  | "private" =>
    match viewer with
    | some v => v == l.by_ || some v == l.to
    | none => openToSpectators
  | _ => viewer.isNone && openToSpectators

/-- The words of a line: no line breaks, and not too long. -/
def clean (s : String) : String :=
  let one := (s.replace "\r" " " |>.replace "\n" " ").trimAscii.toString
  if one.length ≤ maxChars then one else String.ofList (one.toList.take maxChars)

def logPath (dataDir : System.FilePath) (code : String) : System.FilePath :=
  dataDir / s!"{code}.talk"

/-! ## Replies and the seen sign

These are pure, so `ServerTests.lean` can check them. `Server/TalkReply.lean` uses them. -/

/-- The words of a text, in lower case, without punctuation. -/
def words (s : String) : List String :=
  let (out, cur) := s.toLower.toList.foldl (init := ((#[] : Array String), "")) fun (out, cur) c =>
    if c.isAlphanum then (out, cur.push c)
    else if cur.isEmpty then (out, cur) else (out.push cur, "")
  (if cur.isEmpty then out else out.push cur).toList

/-- Does this text name this player? It looks for the first word of the name, as a whole word, in any case. -/
def names (text name : String) : Bool :=
  match words name with
  | first :: _ => (words text).contains first
  | [] => false

/-- The seats in `readers` that have seen line `i` of the talk. `seen s` is how many lines of the talk seat
`s` has seen, counted from the start. The writer is not in the list, and nor is a seat that cannot read the
line: a private line can be seen only by the seat it was sent to. -/
def seenBy (talk : Array Line) (i : Nat) (readers : List Nat) (seen : Nat → Nat) : List Nat :=
  match talk[i]? with
  | none => []
  | some l => readers.filter fun s => s != l.by_ && canSee false (some s) l && i < seen s

/-- Every line of a table. A line that does not read is skipped: talk must not stop a game loading. -/
def readAll (log : EventLog.Log String) : IO (Array Line) := do
  let lines ← log.readFrom 0
  return lines.filterMap fun s => (Json.parse s).toOption.bind lineOfJson

end CharterServer.Talk
