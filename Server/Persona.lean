import Lean.Data.Json
import Charter.Words
import Server.Util

/-!
# Personas for Claude seats

A persona is a play style and a character voice. The styles match who the game is for. A seed picks
the personas, and the seed goes in the log, so a table can be seated the same way again.
-/

namespace CharterServer.Persona
open Lean

/-- How a seat likes to play. -/
structure Style where
  id : String
  label : String
  play : String
  /-- This seat has read no rules. It knows only what the screen shows. -/
  onScreenOnly : Bool := false
  deriving Inhabited

def styles : List Style :=
  [ { id := "trader", label := "Catan trader"
      play := "You play like a keen Catan trader. You win at the table, not on the board. You talk to everyone, you make many offers, and you look for trades where both sides gain. You watch who holds what and who needs what. You hate paying the bank's rate when a neighbour would take less." }
  , { id := "builder", label := "Civ builder"
      play := "You play like a Civilization builder. You think in long plans. You choose spots for what they will pay over many rounds, you upgrade early, and you let growth compound. You like laws that reward investment, and you distrust anything that pays out today and costs you later." }
  , { id := "beautifier", label := "SimCity beautifier"
      play := "You play like a SimCity mayor. You want this place to grow well, and you are proud of it. You like new kinds of buildings, public works paid from the treasury, and a map where nobody is left behind. You want to win, but you would rather win something worth having. You try to write laws that make the game itself better." }
  , { id := "schemer", label := "Paradox schemer"
      play := "You play like a Paradox grand strategist. You build coalitions and you break them. You read every law for who it really helps. You write laws that look neutral and favour you. You use private messages, side deals and embargoes, and you lie when it pays. You keep count of the votes before you act." }
  , { id := "newcomer", label := "newcomer"
      play := "You have never played this game, and you have read no rules. You know only what you can see on the screen in front of you. You try things to find out what they do. When something confuses you, you say so, in plain words, in your confessional. You do not pretend to understand."
      onScreenOnly := true } ]

/-- A character voice: a name and how they talk. -/
def voices : List (String × String) :=
  [ ("Vesna", "a dry harbour-master who speaks in short sentences and counts everything")
  , ("Odalric", "a grand old orator who loves a flourish and an unasked-for history lesson")
  , ("Pim", "a cheerful market gossip who cannot keep a straight face or a secret for long")
  , ("Sabela", "a patient gardener who talks about seasons and is quietly menacing")
  , ("Tomasz", "a retired engineer who is literal, fussy and suspicious of round numbers")
  , ("Ines", "a courtly diplomat who is always polite and rarely sincere")
  , ("Bruno", "a loud ship's cook who talks in food metaphors and takes offence easily")
  , ("Yuki", "a young surveyor who is curious about everything and asks too many questions")
  , ("Marguerite", "a sharp old aunt who has seen every trick and says so")
  , ("Lucan", "a nervous junior clerk who apologises and then does it anyway") ]

/-- One seat's persona. -/
structure Persona where
  style : String
  name : String
  voice : String
  deriving Repr, BEq, Inhabited

def Persona.styleOf (p : Persona) : Style :=
  (styles.find? (·.id == p.style)).getD (styles.headD default)

def toJson' (p : Persona) : Json :=
  Json.mkObj [("style", p.style), ("name", p.name), ("voice", p.voice)]

def ofJson? (j : Json) : Option Persona := do
  return { style := ← jStr j "style", name := ← jStr j "name", voice := ← jStr j "voice" }

/-- A list in an order fixed by the seed. -/
def shuffled {α : Type} (seed : UInt64) (xs : List α) : List α :=
  let keyed := xs.zipIdx.map fun (x, i) =>
    (Charter.scramble (seed + UInt64.ofNat (i + 1) * 0x9E3779B97F4A7C15), x)
  ((keyed.toArray.qsort fun a b => a.1 < b.1).toList).map (·.2)

/-- Personas for a table. Styles do not repeat until every style has been used, and names never do
at a table of up to ten. `only` keeps those styles, in that order, when it is not empty. -/
def pick (seed : UInt64) (seats : Nat) (only : List String := []) : List Persona :=
  let order : List Style :=
    if only.isEmpty then shuffled seed styles
    else only.filterMap fun id => styles.find? (·.id == id)
  let order := if order.isEmpty then styles else order
  let names := shuffled (Charter.scramble seed) voices
  (List.range seats).map fun i =>
    let st := order.getD (i % order.length) (styles.headD default)
    let (name, voice) := names.getD (i % names.length) ("Seat", "a plain speaker")
    { style := st.id, name, voice }

end CharterServer.Persona
