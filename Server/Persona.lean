import Lean.Data.Json
import Charter.Words
import Server.Util

/-!
# Personas for Claude seats

A persona is a play style and a character voice. The styles match who the game is for. A seed picks
the personas, and the seed goes in the log, so a table can be seated the same way again.

A pack can name its own cast, in `casts`. `charter-sim --briefs` can also give each seat a name, a voice
and a private goal. The goal goes in that seat's system prompt and in the log's private fields, and no
other seat and no spectator sees it.
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

/-- Styles that a person running `charter-sim` must ask for by name. `pick` never chooses these by
itself, and a server table cannot ask for them. -/
def specialStyles : List Style :=
  [ { id := "griefer", label := "griefer"
      play := "You are testing this game for its designers, and they asked for this. Your goal is to make this game unplayable, miserable or broken, using only legal play. This replaces the instruction to play to win: winning does not matter to you. Pass laws that drain, freeze, confuse and trap. Use laws that sleep until a late round, decrees, seizing pieces, ending the game, deals that lock people in, proposal spam, and exploits of rounding and caps. Collude with the other seats, and betray them when that does more damage. In `say` and `confess`, narrate what you are trying and what you expect to go wrong. In `confess`, also say what worked, what surprised you, and anything that looks like a bug, a broken promise or a confusing screen." } ]

def allStyles : List Style := styles ++ specialStyles

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

/-- The seats of a pack that has its own cast, by the pack's id. A pack not listed here uses `voices`. -/
def casts : List (String × List (String × String)) :=
  [ ("slime-parliament",
      [ ("Lady Physarum", "an ancient yellow slime mould of old family who has never once been wrong, by her own count")
      , ("Fuligo", "a dog-vomit slime who is loud, proud of the name, and sure that everyone is laughing at them")
      , ("Stemonitis", "a thin chocolate-tube mould who speaks only in points of order and remembers every slight")
      , ("Little Arcyria", "a young pink mould who is very new to politics and much too keen on it")
      , ("Old Lycogala", "a wolf's-milk slime who whispers, chuckles, and hints at long-buried scandal")
      , ("Trichia", "a glittering mould who is vain about her spores and will trade anything for a compliment") ])
  , ("ai-bubble",
      [ ("Odile Marchetti", "the head of Larkspur Foundry, a former concert pianist who speaks in measured, serene sentences about inevitability")
      , ("Tunde Bell", "the head of Ninefold, an ex-commodities trader who counts everything out loud and trusts no number he did not write down")
      , ("Greta Nyland", "the head of Tessera Works, a safety-minded engineer who warns about the crash while building as fast as anyone")
      , ("Cassius Oyelaran", "the head of Brightwater Cognition, a relentless showman who has never met a slide he could not improve") ])
  , ("strike-the-earth",
      [ ("Durgna Cold-Anvil", "a clan matriarch who counts every ingot and has buried three husbands in the walls")
      , ("Ottar Slagbeard", "a huge smith who shouts, weeps at songs and cannot pass a bad idea without shaking its hand")
      , ("Hilde Nine-Lamps", "a soft-spoken lamp-keeper who has read the old accounts of every fort that fell")
      , ("Bram Undermine", "a cheerful sapper who judges all things by how well they would collapse")
      , ("Sigrun Ashdelve", "a young shaft captain who talks like the saga is already being written about her")
      , ("Old Korbo", "a mushroom farmer who has seen it all flood twice and says so") ])
  , ("pirate-republic",
      [ ("Bess Harrow", "a quartermaster with a silver tongue who has an answer for everything and a speech for every occasion")
      , ("Silas Crake", "a one-time castaway who talks low and slow and has not forgiven a single captain he ever sailed under")
      , ("Nan Tolliver", "a purser who talks in sums and quotes back what you said three rounds ago")
      , ("Ezekiel Thorn", "a master gunner and lay preacher who thunders about the Articles and the Republic")
      , ("Marisol Vane", "a smuggler from Havana who is courteous, amused and never quite answers the question")
      , ("Jory Quick", "a young powder monkey who has never been to sea this long and says so, loudly") ]) ]

/-- One seat's persona. -/
structure Persona where
  style : String
  name : String
  voice : String
  /-- A motive only this seat knows. Empty for an ordinary seat. -/
  goal : String := ""
  deriving Repr, BEq, Inhabited

def Persona.styleOf (p : Persona) : Style :=
  (allStyles.find? (·.id == p.style)).getD (styles.headD default)

def toJson' (p : Persona) : Json :=
  let base : List (String × Json) := [("style", p.style), ("name", p.name), ("voice", p.voice)]
  Json.mkObj (if p.goal.isEmpty then base else base ++ [("goal", Json.str p.goal)])

def ofJson? (j : Json) : Option Persona := do
  return { style := ← jStr j "style", name := ← jStr j "name", voice := ← jStr j "voice"
           goal := (jStr j "goal").getD "" }

/-- A list in an order fixed by the seed. -/
def shuffled {α : Type} (seed : UInt64) (xs : List α) : List α :=
  let keyed := xs.zipIdx.map fun (x, i) =>
    (Charter.scramble (seed + UInt64.ofNat (i + 1) * 0x9E3779B97F4A7C15), x)
  ((keyed.toArray.qsort fun a b => a.1 < b.1).toList).map (·.2)

/-- Personas for a table. Styles do not repeat until every style has been used, and names never do
at a table of up to ten. `only` keeps those styles, in that order, when it is not empty. It can name a
style in `pool`, so a special style needs a caller that passes `allStyles`. `game` chooses a pack's cast,
if it has one. -/
def pick (seed : UInt64) (seats : Nat) (only : List String := []) (game : String := "")
    (pool : List Style := styles) : List Persona :=
  let order : List Style :=
    if only.isEmpty then shuffled seed styles
    else only.filterMap fun id => pool.find? (·.id == id)
  let order := if order.isEmpty then styles else order
  let cast := ((casts.find? (·.1 == game)).map (·.2)).getD voices
  let names := shuffled (Charter.scramble seed) cast
  (List.range seats).map fun i =>
    let st := order.getD (i % order.length) (styles.headD default)
    let (name, voice) := names.getD (i % names.length) ("Seat", "a plain speaker")
    { style := st.id, name, voice }

/-! ## Briefs -/

/-- What a brief file says about one seat. A field left out keeps what the seed chose. -/
structure Brief where
  name : Option String := none
  voice : Option String := none
  goal : Option String := none
  style : Option String := none
  deriving Repr, BEq

/-- Read a brief file: a JSON list with one object per seat, in seat order. -/
def parseBriefs (text : String) : Except String (List Brief) := do
  let j ← Json.parse text
  let items ← j.getArr?
  let briefs := items.toList.map fun b =>
    ({ name := jStr b "name", voice := jStr b "voice", goal := jStr b "goal", style := jStr b "style" } : Brief)
  for b in briefs do
    if let some st := b.style then
      if !(allStyles.any (·.id == st)) then throw s!"a brief names a style that does not exist: {st}"
  return briefs

def Brief.applyTo (b : Brief) (p : Persona) : Persona :=
  { p with
    name := b.name.getD p.name, voice := b.voice.getD p.voice
    goal := b.goal.getD p.goal, style := b.style.getD p.style }

/-- The seed's personas, with the briefs put over them. A seat with no brief stays as it was. -/
def withBriefs (personas : List Persona) (briefs : List Brief) : List Persona :=
  personas.zipIdx.map fun (p, i) =>
    match briefs[i]? with
    | some b => b.applyTo p
    | none => p

end CharterServer.Persona
