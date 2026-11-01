import Lean.Data.Json
import Server.Formalize
import Server.Talk

/-!
# The clerk suggests a rule

A player with no rule in mind asks the clerk for one. The clerk reads what that seat can see and
replies with words for the input box, a short "why", and a formal rule. The formal rule goes through
the same parser and checks as any draft, and the player then has an ordinary draft. Nothing here
reaches `Engine.step`.

The limit on what the clerk reads is in `message`. It looks at talk only through `visibleTalk`, which
uses the rule the talk route uses, and at clerk notes only through this seat's own. The rest is what
every seat already sees in its view. `ServerTests` holds this.

The "why" is advice from Claude. No check reads it, and the screen shows it apart from the rule, whose
source Lean prints from the clauses. The rule's description comes from `Server/Describe.lean`, which sees
none of what this file reads.
-/

namespace CharterServer.Suggest
open Lean Charter CharterServer.Game CharterServer.Formalize

/-! ## The bounds -/

/-- The most public chat lines a prompt can hold. -/
def maxPublicTalk : Nat := 30
/-- The most private lines a prompt can hold. -/
def maxPrivateTalk : Nat := 15
/-- How many of the newest chronicle lines are always kept. -/
def maxRecentLines : Nat := 15
/-- How many older chronicle lines are kept. Only the ones worth telling are. -/
def maxOlderLines : Nat := 20
/-- How many earlier suggestions a prompt can hold. -/
def maxSuggestions : Nat := 8
/-- The size of each of these sections, in characters. The oldest lines go first. -/
def maxSectionChars : Nat := 3000
/-- The longest words the clerk can put in the input box. -/
def maxWordsChars : Nat := 300
def maxWhySentences : Nat := 2
/-- A "why" should be under about 45 words. Past this, the clerk is asked to write it again. -/
def maxWhyWords : Nat := 60
/-- For how many rounds a failed rule cannot come back word for word. -/
def failedRounds : Nat := 3

/-! ## What the clerk may read -/

/-- The talk this seat can read: public lines, and private lines it sent or received. It is the rule
that decides what the talk route serves to this seat. No confessional or interview passes it, and no
private line between other seats. -/
def visibleTalk (seat : Nat) (talk : List Talk.Line) : List Talk.Line :=
  talk.filter (Talk.canSee false (some seat))

/-- What this seat harvests, from the pieces on the board. -/
def collectsOf {G : GameDef} (s : State G) (p : Nat) : String :=
  let parts := (paidRegions G).filterMap fun r =>
    let total := (s.pieces.filter fun x =>
        x.owner == p && match x.loc with
          | .spot v => r.spots.contains v
          | .link _ => false).foldl
      (fun acc x => acc + ((s.rules.piece? x.kind).map (·.yield)).getD 0) 0
    if total == 0 then none else some s!"{total} {r.res} on a roll of {r.number}"
  if parts.isEmpty then "nothing" else ", ".intercalate parts

/-- Where this seat's pieces stand. -/
def piecesOf {G : GameDef} (s : State G) (p : Nat) : String :=
  let parts := (s.pieces.filter (·.owner == p)).map fun x =>
    match x.loc with
    | .spot v => s!"{x.kind} on corner {v}"
    | .link l => s!"{x.kind} from corner {l.1} to {l.2}"
  if parts.isEmpty then "nothing" else ", ".intercalate parts

def bundleWords (b : Bundle) : String :=
  if b.isEmpty then "nothing" else Text.bundleText b

/-- The public facts the table section does not hold. -/
def publicFacts (g : Game) (s : State g.spec.G) : String :=
  let G := g.spec.G
  let bank := (G.resources.map (·.name)).map fun r => s!"{s.balance .bank r} {r}"
  let collects := s.turnOrder.map fun p => s!"- seat {p}: {collectsOf s p}"
  let standing := s.turnOrder.map fun p => s!"- seat {p}: {piecesOf s p}"
  let deals := if s.deals.isEmpty then "none" else
    "\n".intercalate (s.deals.map fun d => s!"- until round {d.lastRound}: {Text.dealLine g.nameOf d.deal}")
  let unpaid := (Scene.rollsOf G).filter fun r => !G.map.regions.any (·.number == r)
  let unpaidWords := if unpaid.isEmpty then "" else s!"No hex pays on {Text.orList (unpaid.map toString)}. "
  let offers := if s.offers.isEmpty then "none" else
    "\n".intercalate (s.offers.map fun o =>
      let to := match o.to with
        | some t => g.nameOf t
        | none => "anyone"
      s!"- {g.nameOf o.src} offers {bundleWords o.give} to {to}, for {bundleWords o.get}")
  Clerk.neutralize s!"The bank holds: {", ".intercalate bank}.
Proposing a law or a deal costs nothing.
{unpaidWords}Each turn starts with a roll, and `on-roll` laws run on every one.

What each seat harvests today:
{"\n".intercalate collects}

Where each seat's pieces stand:
{"\n".intercalate standing}

Deals running:
{deals}

Open offers:
{offers}"

/-- The chronicle: the newest lines, and the older ones worth telling. -/
def chronicleLines (g : Game) : List String :=
  let all := g.chronicle.toList
  let older := all.take (all.length - maxRecentLines)
  let told := (older.filter (·.major)).reverse.take maxOlderLines |>.reverse
  let recent := all.drop (all.length - maxRecentLines)
  Clerk.fitNewest maxSectionChars ((told ++ recent).map fun l => Clerk.oneLine s!"- Round {l.round}: {l.text}")

def publicLines (g : Game) (talk : List Talk.Line) : List String :=
  let lines := ((talk.filter (·.kind == "public")).reverse.take maxPublicTalk).reverse
  Clerk.fitNewest maxSectionChars (lines.map fun l => Clerk.oneLine s!"- {g.nameOf l.by_}: {l.text}")

def privateLines (g : Game) (seat : Nat) (talk : List Talk.Line) : List String :=
  let lines := ((talk.filter (·.kind == "private")).reverse.take maxPrivateTalk).reverse
  Clerk.fitNewest maxSectionChars (lines.map fun l =>
    if l.by_ == seat then Clerk.oneLine s!"- you to {g.nameOf (l.to.getD 0)}: {l.text}"
    else Clerk.oneLine s!"- {g.nameOf l.by_} to you: {l.text}")

def suggestionLines (g : Game) (notes : List Clerk.Note) : List String :=
  let mine := (notes.filter (·.suggested)).reverse.take maxSuggestions |>.reverse
  Clerk.fitNewest maxSectionChars (mine.map (Clerk.noteLine g))

/-- Print a message from what `message` has already limited. -/
def build (g : Game) (s : State g.spec.G) (seat : Nat) (talk : List Talk.Line) (notes : List Clerk.Note)
    (retry : Option (String × String)) : String :=
  let block (tag : String) (lines : List String) : String :=
    let body := if lines.isEmpty then "none yet" else "\n".intercalate lines
    s!"<{tag}>\n{body}\n</{tag}>"
  let mem := Clerk.memoryBlock g seat notes
  let mem := if mem.isEmpty then "" else s!"\n\n{mem}"
  let base := "\n\n".intercalate
    [ s!"<table>\n{tableContext g s seat}\n\n{publicFacts g s}\n</table>{mem}"
    , block "chronicle" (chronicleLines g)
    , block "table_talk" (publicLines g talk)
    , block "your_private_messages" (privateLines g seat talk)
    , block "your_earlier_suggestions" (suggestionLines g notes)
    , s!"<suggest>\nSuggest one rule for seat {seat} ({Clerk.oneLine (g.nameOf seat)}).\n</suggest>" ]
  match retry with
  | none => base
  | some (prior, err) =>
    s!"{base}\n\n<rejected_reply>\n{Clerk.neutralize prior}\n</rejected_reply>\n\nThe program rejected that reply. It said: {Clerk.neutralize err}\nReply again in the same form, with this fixed."

/-- The user message of a suggestion for one seat. Only this seat's talk and notes get past here. -/
def message (g : Game) (s : State g.spec.G) (seat : Nat) (talk : List Talk.Line) (notes : List Clerk.Note)
    (retry : Option (String × String) := none) : String :=
  build g s seat (visibleTalk seat talk) (notes.filter (·.seat == seat)) retry

/-! ## Reading the reply -/

/-- How many sentences a text has: stops with a space or the end after them. -/
def sentenceEnds (s : String) : Nat :=
  let cs := s.toList
  ((cs.zip (cs.drop 1 ++ [' '])).filter fun (c, next) =>
    (c == '.' || c == '!' || c == '?') && next.isWhitespace).length

/-- Why the words alone must be written again, if they must. -/
def wordsProblem (w : String) : Option String :=
  if w.isEmpty then some "The WORDS line is empty."
  else if w.startsWith "(" then some "The WORDS line must be plain words, and not formal text."
  else if w.length > maxWordsChars then some s!"The WORDS line has {w.length} characters. Keep it under 200."
  else none

/-- Why a reply's words or advice must be written again, if they must. -/
def shapeProblem (r : Reply) : Option String :=
  match r.words, r.why with
  | none, _ => some "The WORDS line is missing."
  | _, none => some "The WHY line is missing."
  | some w, some y =>
    let wordCount := ((y.splitOn " ").filter (!·.isEmpty)).length
    match wordsProblem w with
    | some why => some why
    | none =>
      if y.isEmpty then some "The WHY line is empty."
      else if sentenceEnds y > maxWhySentences || wordCount > maxWhyWords then
        some s!"The WHY line has {sentenceEnds y} sentences and {wordCount} words. Write at most two sentences, under 45 words."
      else none

/-- The same rule, whatever its title. -/
def ruleKey : Proposal → String
  | .law L => Rules.printProposal (.law { L with title := "" })
  | .deal d => Rules.printProposal (.deal { d with title := "" })

/-- Why this rule must not be suggested now, if it must not. This is only for a rule that is the same
word for word. The prompt asks for a different idea, and that part is up to the model. -/
def repeatProblem (g : Game) (s : State g.spec.G) (notes : List Clerk.Note) (p : Proposal) : Option String :=
  let key := ruleKey p
  let same (q : Proposal) : Bool := ruleKey q == key
  let inForce := s.laws.any fun x => same (.law x.2)
  let earlier := notes.any fun n =>
    n.suggested && match n.formal.map g.parse with
      | some (.ok q) => same q
      | _ => false
  let tabled (t : Tabled) (outcome : String) : Bool := t.outcome == outcome && same t.body
  let isOpen := g.tabled.any (tabled · "open")
  let recent (t : Tabled) : Bool := s.round ≤ t.round + failedRounds
  let failed := g.tabled.any fun t => recent t && (tabled t "failed" || tabled t "lapsed")
  if inForce then some "That law is already in force. Suggest a different idea."
  else if earlier then some "You already suggested that rule to this player. Suggest a different idea."
  else if isOpen then some "That rule is already before the table. Suggest a different idea."
  else if failed then some "The table turned that rule down recently. Suggest a different idea."
  else none

/-- The first sentences of a text, for the last attempt. -/
def firstSentences (n : Nat) (s : String) : String := Id.run do
  let cs := s.toList
  let mut seen := 0
  let mut out : List Char := []
  for (c, next) in cs.zip (cs.drop 1 ++ [' ']) do
    out := c :: out
    if (c == '.' || c == '!' || c == '?') && next.isWhitespace then
      seen := seen + 1
      if seen == n then break
  return String.ofList out.reverse

/-! ## A suggestion from start to finish -/

/-- Run a suggestion on this thread. `talk` and `notes` hold the whole table: `message` limits them. -/
def run (job : Job) (cfg : Settings) (current : IO (Option Game)) (talk : List Talk.Line)
    (notes : List Clerk.Note) : IO Unit := do
  let finish (f : Final) : IO Unit :=
    touch job fun st => { st with stage := "done", final := some f }
  let some key := cfg.key
    | finish (.failed "This server has no API key, so the clerk cannot suggest a rule. Set ANTHROPIC_API_KEY in .env, or write your own rule.")
  let system ← try IO.FS.readFile cfg.promptPath catch _ => pure ""
  if system.isEmpty then
    finish (.failed "The clerk's instructions are missing from this server.")
    return
  let some g ← current | finish (.failed "The game is gone.")
  let some s := g.state | finish (.failed "The game has not started.")
  job.state.modify fun st => { st with atEvent := g.events }
  let mine := notes.filter (·.seat == job.seat)
  let giveUp (why : String) : IO Unit :=
    finish (.refused s!"The clerk could not find a rule to suggest this time. {why} Try again, or write your own rule.")
  let ready (words why : String) (formal : String) : IO Unit := do
    job.onReady formal
    touch job fun st => { st with suggestedWords := some words, why := some why, stage := "done"
                                  final := some (.ready formal none true) }
  let mut retry : Option (String × String) := none
  for n in (List.range maxAttempts).map (· + 1) do
    touch job fun st => { st with stage := "sent", attempt := n, text := "", thinking := "",
                                  retryReason := retry.map (·.2) }
    let body := requestBody cfg system (message g s job.seat talk notes retry)
    let outcome ← runRequest job (curlConfig cfg key body) cfg.model
    addSpent job
    if ← job.cancelled.get then
      finish .cancelled
      return
    if let some msg := failureOf outcome true then
      finish (.failed msg)
      return
    let text := (← job.state.get).text
    let reply := parseReply text
    if let some why := reply.refuse then
      finish (.refused why)
      return
    let last := n == maxAttempts
    match ← checkFormal job current reply.formal with
    | .error err =>
      if last then return ← giveUp err
      retry := some (text, err)
    | .ok () =>
      let repeated := match g.parse reply.formal with
        | .ok p => repeatProblem g s mine p
        | .error _ => none
      match repeated, shapeProblem reply, reply.words, reply.why with
      | some why, _, _, _ =>
        if last then return ← giveUp why
        retry := some (text, why)
      | none, none, some w, some y =>
        ready w y reply.formal
        return
      | none, some why, w?, y? =>
        -- On the last attempt, a rule whose only fault is long advice still goes out, with the advice cut.
        match last, w?, y? with
        | true, some w, some y =>
          if (wordsProblem w).isNone && !y.isEmpty then
            ready w (firstSentences maxWhySentences y) reply.formal
            return
          return ← giveUp why
        | true, _, _ => return ← giveUp why
        | false, _, _ => retry := some (text, why)
      | none, none, _, _ => return ← giveUp "The reply was not complete."

end CharterServer.Suggest
