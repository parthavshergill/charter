import Lean.Data.Json
import Charter.Sha256
import Server.Formalize

/-!
# A short description of a law, by Claude

A law's source is hard to read, so Claude writes a few plain words to show above it. These words are
Claude's. No proof and no test stands behind them, and the source is what counts.

The call sees only the law, written out with a blank title. It never sees the player's words, the title,
the chat or anything else about the table. A law's piece names are free text from its proposer, so
`describer.md` treats everything in the law as data, and `Clerk.neutralize` stops a name from closing
the marker it sits between.

Each description is tied to the law it was written for by a hash of that printed law. A law with a new
clause or a new number has a new hash, so it can never show an old description. Two laws that differ
only in their titles share one, which is safe because the title is not in the call.

A description is kept in the table's clerk log. It survives a restart and goes to storage with the rest
of that log. A clerk note and a description are different lines of that log, and neither reads as the
other. No route takes a description from a client.

No description is a normal case: a hand-written law, a refusal, an empty reply, or the clerk on strike
because of a problem on our side, such as a failed call or a used-up budget. The screen then shows the
source with a short note. A problem on our side says so.

The call goes through `Formalize.runRequest`, so the budgets cover it and it is priced as the model it
went to. It sends `fallbacks` only for a Sonnet model, because Haiku has no server-side fallback for a
refusal. It sends no temperature, no top_p, no top_k and no prefill.
-/

namespace CharterServer.Describe
open Lean Charter CharterServer.Game

/-- The most words a description can have. `describer.md` asks for 40, and this leaves a little room. -/
def maxWords : Nat := 45
/-- How many replies a description can get. A later one is told that the last was too long. -/
def maxAttempts : Nat := 2
/-- This allows for thinking as well as the few words of the reply. At a higher effort a hard law can
think for a thousand tokens or more. -/
def maxOutputTokens : Nat := 4000
/-- A person is waiting with the source already on screen, so this does not wait long. -/
def maxSeconds : Nat := 40

/-! ## Which law a description belongs to -/

/-- The printed law, with no title. This is what a description is tied to. -/
def printedLaw (L : Law) : String := Rules.printProposal (.law { L with title := "" })

/-- The key that ties a description to one law. -/
def lawKey (L : Law) : String := Sha256.hashText (printedLaw L)

#guard printedLaw { title := "Anything", clauses := [.setBankRate 3] } == "(law \"\" (set-bank-rate 3))"
#guard lawKey { title := "A", clauses := [.setBankRate 3] } == lawKey { title := "B", clauses := [.setBankRate 3] }
#guard lawKey { title := "A", clauses := [.setBankRate 3] } != lawKey { title := "A", clauses := [.setBankRate 4] }

/-! ## How the model reads a law

The model gets the same clauses in a form that it reads better. In tests with the bare form, it often
turned a payment around, and it read a second transfer under `if` as an "else". Each thing here goes on
its own line, each payment says `from` and `to`, and `if` reads `when`. Only the words and the spaces
differ from the printed law. -/

/-- These forms start a new line. A form the list does not know stays on the line it is on, and it
still reads. -/
def startsLine (head : String) : Bool :=
  head.startsWith "on-" || head.startsWith "set-" ||
  ["new-piece", "repeal", "now", "end-game", "for-each-player", "if", "transfer", "move-piece"].contains head

/-- A form, with its parts relabelled for the model. -/
def relabel : List SExp → List SExp
  | [.atom "transfer", f, t, r, n] => [.atom "transfer", .atom "from", f, .atom "to", t, r, n]
  | [.atom "move-piece", f, t, k] => [.atom "move-piece", .atom "from", f, .atom "to", t, k]
  | .atom "if" :: rest => .atom "when" :: rest
  | xs => xs

partial def layout (depth : Nat) : SExp → String
  | .list xs =>
    let parts := (relabel xs).map fun x =>
      let line := match x with
        | .list (.atom h :: _) => startsLine h
        | _ => false
      (line, layout (depth + 1) x)
    let body := parts.foldl (init := "") fun acc (line, text) =>
      if line then acc ++ "\n" ++ String.ofList (List.replicate (2 * (depth + 1)) ' ') ++ text
      else if acc.isEmpty then text
      else acc ++ " " ++ text
    "(" ++ body ++ ")"
  | x => x.render

/-- The law as the model reads it, with no title. -/
def forModel (L : Law) : String :=
  layout 0 (Rules.lawS { L with title := "" })

#guard forModel { title := "Toll", clauses := [.onBuild "road" [.when (.le (.lit 5) (.points .actor)) [.transfer .actor .treasury (.lit "ore") (.lit 2)]]] } ==
  "(law \"\"\n  (on-build road\n    (when (<= 5 (points actor))\n      (transfer from actor to treasury ore 2))))"

/-! ## What the server knows about a law's description -/

inductive Status where
  /-- The call is running. -/
  | writing
  | ready (text : String)
  /-- A pack's own words about one of its founding laws, and the pack's name. -/
  | pack (name text : String)
  /-- The call was refused or came back with nothing to show. -/
  | failed
  /-- A problem on our side stopped the call. -/
  | strike
  deriving BEq

/-- One table's descriptions, by the key of the law. A law that is not here has none. -/
abbrev Book := Std.HashMap String Status

/-- A description for the screen. -/
def json (book : Book) (L : Law) : Json :=
  match book.get? (lawKey L) with
  | some .writing => Json.mkObj [("status", "writing")]
  | some (.ready text) => Json.mkObj [("status", "ready"), ("text", text)]
  | some (.pack name text) => Json.mkObj [("status", "pack"), ("text", text), ("pack", name)]
  | some .failed => Json.mkObj [("status", "failed")]
  | some .strike => Json.mkObj [("status", "strike")]
  | none => Json.mkObj [("status", "none")]

/-- Who wrote the description of a law and what it says, if the law has one. -/
def textOf (book : Book) (L : Law) : Option (String × String) :=
  match book.get? (lawKey L) with
  | some (.ready text) => some ("Claude's description", text)
  | some (.pack name text) => some (s!"The description from the pack {name}", text)
  | _ => none

/-- How many descriptions have finished, whichever way, so that a page knows when to ask again. -/
def finished (book : Book) : Nat :=
  book.fold (fun n _ st => if st == .writing then n else n + 1) 0

/-! ## A pack's own words -/

/-- A pack's words, by the key of the law they belong to. An entry counts only if its fingerprint is the
start of its law's key, so words written for an older version of a law never show. -/
def packWords (spec : GameSpec) : List (String × String) :=
  spec.foundingWords.filterMap fun (L, fingerprint, text) =>
    let key := lawKey L
    if !fingerprint.isEmpty && key.startsWith fingerprint then some (key, text) else none

/-- The book of a table, with its pack's words on top. -/
def withPack (spec : GameSpec) (book : Book) : Book :=
  (packWords spec).foldl (fun b (key, text) => b.insert key (.pack spec.name text)) book

/-- What is wrong with a pack's words: a founding law with none, or words for an older law. Each line
says what to put in the entry. -/
def packProblems (spec : GameSpec) : List String :=
  let fresh := packWords spec
  (spec.G.foundingLaws.filterMap fun L =>
    if fresh.any (·.1 == lawKey L) then none
    else some s!"Read the words for \"{L.title}\" again. Its fingerprint is {(lawKey L).take 8}.")

/-! ## The clerk log -/

/-- A log line for a description. It has no `seat`, so `Clerk.noteOfLine` does not read it as a note. -/
def recordJson (key text model effort : String) : Json :=
  Json.mkObj [("k", "description"), ("law", key), ("text", text), ("model", model), ("effort", effort)]

/-- Read a log line, if it is a description. -/
def recordOfLine (line : String) : Option (String × String) := do
  let j ← (Json.parse line).toOption
  if jStr j "k" != some "description" then none
  return (← jStr j "law", ← jStr j "text")

#guard recordOfLine (recordJson "k1" "Words." "m" "low").compress == some ("k1", "Words.")
#guard (Clerk.noteOfLine (recordJson "k1" "Words." "m" "low").compress).isNone
#guard (recordOfLine (Clerk.noteJson { seat := 0, round := 1, words := "w" }).compress).isNone

/-! ## The request -/

/-- The settings of this call. The key and the address are the clerk's. -/
structure Settings where
  api : Formalize.Settings
  effort : String

def settings (root : System.FilePath) : IO Settings := do
  let api ← Formalize.settings root
  return { api := { api with model := (← IO.getEnv "CHARTER_DESCRIBE_MODEL").getD "claude-sonnet-5-5"
                             promptPath := root / "Server" / "describer.md" }
           effort := (← IO.getEnv "CHARTER_DESCRIBE_EFFORT").getD "low" }

/-- The user message holds the law and nothing else. On a second try it also holds the last reply. -/
def userMessage (L : Law) (retry : Option (String × Nat)) : String :=
  let base := s!"<law>\n{Clerk.neutralize (forModel L)}\n</law>"
  match retry with
  | none => base
  | some (prior, words) =>
    s!"{base}\n\n<last_reply>\n{Clerk.neutralize prior}\n</last_reply>\n\nThat reply has {words} words. Write it again in at most 40 words, with nothing else."

def requestBody (cfg : Settings) (system user : String) : Json :=
  let fields : List (String × Json) :=
    [ ("model", cfg.api.model)
    , ("max_tokens", toJson maxOutputTokens)
    , ("stream", toJson true)
    , ("output_config", Json.mkObj [("effort", cfg.effort)])
    , ("system", Json.arr #[Json.mkObj [("type", "text"), ("text", system)]])
    , ("messages", Json.arr #[Json.mkObj [("role", "user"), ("content", user)]]) ]
  let fallback : List (String × Json) :=
    if cfg.api.model.startsWith "claude-sonnet" then [("fallbacks", "default")] else []
  Json.mkObj (fields ++ fallback)

/-! ## The reply -/

/-- The reply as one paragraph. -/
def clean (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

def wordCount (s : String) : Nat := ((clean s).splitOn " ").length

#guard clean "  One  two\n\nthree. " == "One two three."
#guard wordCount "One two\nthree." == 3

/-- The call has a usable reply only if the model stopped by itself. A refusal or a cut-off reply is
not usable, and neither is a request that got no reply at all. -/
def usable (o : Formalize.Outcome) : Bool :=
  (Formalize.failureOf o).isNone && o.stopReason == some "end_turn"

private def newJob (code : String) : IO Formalize.Job := do
  let now ← IO.monoMsNow
  return { id := 0, seat := 0, words := "", startedMs := now, table := code
           state := ← IO.mkRef { lastEventMs := now }
           stop := ← IO.mkRef (pure ())
           cancelled := ← IO.mkRef false }

/-- Ask for a description of this law, on this thread. An error is the status of a law that gets no
description, and the reason goes to the server's log. A reply that stays too long is not cut, since a
cut could change what it says. -/
def run (cfg : Settings) (code : String) (L : Law) : IO (Except Status String) := do
  let some key := cfg.api.key
    | IO.eprintln s!"[{code}] no description: this server has no API key"
      return .error .strike
  let system ← try IO.FS.readFile cfg.api.promptPath catch _ => pure ""
  if system.isEmpty then
    IO.eprintln s!"[{code}] the description prompt is missing"
    return .error .strike
  let mut retry : Option (String × Nat) := none
  for _ in [0:maxAttempts] do
    let job ← newJob code
    let body := requestBody cfg system (userMessage L retry)
    let outcome ← Formalize.requestRetrying job (Formalize.curlConfig cfg.api key body maxSeconds) cfg.api.model maxSeconds
    if !usable outcome then
      IO.eprintln s!"[{code}] no description from {cfg.api.model}: {(Formalize.failureOf outcome).getD "the reply did not finish"}"
      return .error (if (Formalize.failureOf outcome).isSome && (Formalize.declined outcome).isNone then .strike else .failed)
    let text := clean (← job.state.get).text
    if text.isEmpty then
      IO.eprintln s!"[{code}] no description: the reply was empty"
      return .error .failed
    let words := wordCount text
    if words ≤ maxWords then return .ok text
    retry := some (text, words)
  IO.eprintln s!"[{code}] no description: the reply stayed too long"
  return .error .failed

end CharterServer.Describe
