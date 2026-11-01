import Lean.Data.Json
import Server.Game
import Server.Rules
import Server.Clerk
import Server.Spend

/-!
# The clerk: English to formal text

A read-only step. It never changes a game and goes through no engine event. Claude's reply is
untrusted: it goes through the same parser and the same checks as text a player types, and nothing
reaches `Engine.step` until the player proposes it.

Player words are untrusted too. The table, the clerk's memory and the request each go between
markers in the user message, and `formalizer.md` says that what is between them is data. The markers
cannot be closed from inside, because `Clerk.neutralize` breaks anything that would read as one.

The server calls the Anthropic API through `curl`, because the Lean toolchain here has no TLS client.
The key and the request go to `curl` through its standard input, never its arguments, so `ps` cannot
show them. The key is not stored, printed or sent to a browser.

Each draft runs on its own thread and writes what really happens to a shared state, and the browser
polls that state. Every stage on screen is tied to an event below.

`Server/Suggest.lean` uses the same request, reply and checks when a player asks the clerk to suggest a rule.
-/

namespace CharterServer.Formalize
open Lean Charter CharterServer.Game

variable {G : GameDef}

/-- How a draft ended. -/
inductive Final where
  | ready (formal : String) (difference : Option String) (viaClaude : Bool)
  | refused (reason : String)
  | failed (message : String)
  /-- The clerk cannot work because of a problem on our side. -/
  | strike (message : String)
  | cancelled

structure JobState where
  /-- `sent`, `retrying`, `connected`, `thinking`, `drafting`, `parsing`, `checking`, `previewing`, or `done`. -/
  stage : String := "sent"
  attempt : Nat := 1
  retryReason : Option String := none
  lastEventMs : Nat := 0
  thinking : String := ""
  text : String := ""
  final : Option Final := none
  inputTokens : Nat := 0
  cacheReadTokens : Nat := 0
  cacheWriteTokens : Nat := 0
  outputTokens : Nat := 0
  /-- Added up over every request of this draft. The fields above are for the latest request. -/
  spentInput : Nat := 0
  spentCacheRead : Nat := 0
  spentCacheWrite : Nat := 0
  spentOutput : Nat := 0
  /-- For a suggestion: the words the clerk proposes, for the player's input box. -/
  suggestedWords : Option String := none
  /-- For a suggestion: the clerk's advice. It is Claude's prose, and no rule is built from it. -/
  why : Option String := none
  /-- For a suggestion: how many game events the table had when the clerk read it. -/
  atEvent : Nat := 0

structure Job where
  id : Nat
  seat : Nat
  words : String
  startedMs : Nat
  state : IO.Ref JobState
  stop : IO.Ref (IO Unit)
  cancelled : IO.Ref Bool
  /-- The table this work is for, which decides whose budget pays for it. -/
  table : String := ""
  /-- The player asked the clerk to suggest a rule, so `words` is empty. -/
  suggest : Bool := false
  /-- Runs on a rule Claude wrote, just before the screen can see that it is ready. -/
  onReady : String → IO Unit := fun _ => pure ()

/-- The model and limits. Effort and output are bounded, because this runs on a player's click. -/
structure Settings where
  key : Option String
  model : String
  baseUrl : String
  promptPath : System.FilePath

def maxOutputTokens : Nat := 8000
def maxSeconds : Nat := 150
/-- How many replies a draft can get before it stops. Each later one is told what was wrong. -/
def maxAttempts : Nat := 3
/-- How many times one reply is asked for, when the API has a problem that can pass. -/
def maxTries : Nat := 3
/-- A person is waiting, so a longer wait than this ends the tries. -/
def maxRetryWaitMs : Nat := 10000
/-- A difference line should be under about 30 words. Past this, the clerk is asked to write it again. -/
def maxDifferenceWords : Nat := 40

/-- Read a key from a `.env` file. This only finds it. It must not be printed. -/
def keyFromEnvFile (path : System.FilePath) : IO (Option String) := do
  if !(← path.pathExists) then return none
  let lines ← IO.FS.lines path
  for l in lines do
    let l := l.trimAscii.toString
    if l.startsWith "ANTHROPIC_API_KEY=" then
      let v := (l.drop "ANTHROPIC_API_KEY=".length).toString.trimAscii.toString
      let v := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then ((v.drop 1).dropEnd 1).toString else v
      if !v.isEmpty then return some v
  return none

/-- Find the settings. Called for each draft, so a key added to `.env` works without a restart. -/
def settings (root : System.FilePath) : IO Settings := do
  let fromEnv := (← IO.getEnv "ANTHROPIC_API_KEY").filter (!·.isEmpty)
  let envPath : System.FilePath := (← IO.getEnv "CHARTER_ENV_FILE").getD (root / ".env").toString
  let key ← match fromEnv with
    | some k => pure (some k)
    | none => keyFromEnvFile envPath
  return { key
           model := (← IO.getEnv "CHARTER_MODEL").getD "claude-opus-5-5"
           baseUrl := (← IO.getEnv "ANTHROPIC_BASE_URL").getD "https://api.anthropic.com"
           promptPath := root / "Server" / "formalizer.md" }

/-! ## The table, as the model sees it -/

def placementS (p : Placement) : String := (Rules.placementS p).render

def pieceLine (s : State G) (d : PieceDef) : String :=
  let _ := s
  s!"- {d.name}: costs {Text.bundleText d.cost}; {d.points} points; placement {placementS d.placement}; yield {d.yield}; limit {d.limit} per player"

/-- A seat's hand and pieces, which every player can see on the board. -/
def seatFacts (s : State G) (p : Nat) : String :=
  let hand := (G.resources.map (·.name)).filterMap fun r =>
    let n := s.balance (.player p) r
    if n == 0 then none else some s!"{n} {r}"
  let owned := (s.rules.pieces.map (·.name)).filterMap fun k =>
    let n := s.countOf p k
    if n == 0 then none else some s!"{n} {k}"
  let handText := if hand.isEmpty then "nothing" else ", ".intercalate hand
  let ownedText := if owned.isEmpty then "nothing" else ", ".intercalate owned
  s!"{s.pointsOf p} points; holds {handText}; owns {ownedText}"

/-- What the model needs to know about this table right now. All of it is public. Names and titles
are player words, so the whole section is data. -/
def tableContext (g : Game) (s : State g.spec.G) (seat : Nat) : String :=
  let G := g.spec.G
  let seats := "\n".intercalate (s.turnOrder.map fun p =>
    let you := if p == seat then " (the proposer: \"I\", \"me\", \"my\" mean this seat)" else ""
    s!"- seat {p}: {g.nameOf p}{you}: {seatFacts s p}")
  let pieces := "\n".intercalate (s.rules.pieces.map (pieceLine s))
  let laws := if s.laws.isEmpty then "none" else
    "\n".intercalate (s.laws.map fun x => s!"- Law {x.1}: {Rules.printProposal (.law x.2)}")
  let hexes := "\n".intercalate (G.map.regions.map fun r =>
    s!"- {r.res} on {r.number}: corners {r.spots}")
  let treasury := (G.resources.map (·.name)).filterMap fun r =>
    let n := s.balance .treasury r
    if n == 0 then none else some s!"{n} {r}"
  let treasuryText := if treasury.isEmpty then "nothing" else ", ".intercalate treasury
  let guide := if g.spec.guide.isEmpty then "" else s!"\n\n{g.spec.guide}"
  Clerk.neutralize s!"Round {s.round} of {G.rounds}. First to {G.targetPoints} points wins. The bank trades {s.rules.bankRate} for 1. The treasury holds {treasuryText}. The dice show {G.diceCount} to {G.diceCount * G.diceSides}.

The resources of this game: {", ".intercalate g.resources}.{guide}

Seats:
{seats}

Pieces:
{pieces}

Laws in force:
{laws}

Hexes:
{hexes}"

/-! ## The request -/

/-- The user message: the table, the memory, the request, and on a retry, what was wrong. The system
block holds only the fixed rules, so the prompt cache stays valid whatever is in here. -/
def userMessage (g : Game) (s : State g.spec.G) (seat : Nat) (memory : String) (words : String)
    (retry : Option (String × String)) : String :=
  let table := s!"<table>\n{tableContext g s seat}\n</table>"
  let mem := if memory.isEmpty then "" else s!"\n\n{memory}"
  let base := s!"{table}{mem}\n\n<request>\n{Clerk.neutralize words}\n</request>"
  match retry with
  | none => base
  | some (prior, err) =>
    s!"{base}\n\n<rejected_reply>\n{Clerk.neutralize prior}\n</rejected_reply>\n\nThe program rejected that reply. It said: {Clerk.neutralize err}\nReply again in the same form, with this fixed."

/-- The request body. The rule language is a fixed system block, so it can be cached across drafts.
The table and the memory go in the user message, so they do not disturb that cache. -/
def requestBody (cfg : Settings) (system user : String) : Json :=
  Json.mkObj
    [ ("model", cfg.model)
    , ("max_tokens", toJson maxOutputTokens)
    , ("stream", toJson true)
    , ("thinking", Json.mkObj [("type", "adaptive"), ("display", "summarized")])
    , ("output_config", Json.mkObj [("effort", "medium")])
    , ("fallbacks", "default")
    , ("system", Json.arr #[Json.mkObj [("type", "text"), ("text", system),
        ("cache_control", Json.mkObj [("type", "ephemeral")])]])
    , ("messages", Json.arr #[Json.mkObj [("role", "user"), ("content", user)]]) ]

def curlQuote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- The whole curl configuration, for its standard input. This holds the key, so it goes nowhere else. -/
def curlConfig (cfg : Settings) (key : String) (body : Json) (seconds : Nat := maxSeconds) : String :=
  "\n".intercalate
    [ s!"url = {curlQuote s!"{cfg.baseUrl}/v1/messages"}"
    , "request = \"POST\""
    , "header = \"content-type: application/json\""
    , s!"header = {curlQuote s!"x-api-key: {key}"}"
    , "header = \"anthropic-version: 2026-10-21\""
    , "header = \"anthropic-beta: server-side-fallback-2026-07-01\""
    , "silent", "show-error", "no-buffer"
    , s!"max-time = {seconds}", "connect-timeout = 15"
    , "write-out = \"\\n__HTTP__ %{http_code} %header{retry-after}\\n\""
    , s!"data-binary = {curlQuote body.compress}"
    , "" ]

/-! ## Reading the stream -/

def touch (job : Job) (f : JobState → JobState := id) : IO Unit := do
  let now ← IO.monoMsNow
  job.state.modify fun st => { f st with lastEventMs := now }

/-- Handle one server-sent event. Each change here is what the screen reports. -/
def onEvent (job : Job) (j : Json) : IO Unit := do
  match jStr j "type" with
  | some "message_start" =>
    let usage := (jField j "message").bind (jField · "usage")
    let inTok := (usage.bind (jNat · "input_tokens")).getD 0
    let cached := (usage.bind (jNat · "cache_read_input_tokens")).getD 0
    let written := (usage.bind (jNat · "cache_creation_input_tokens")).getD 0
    touch job fun st => { st with stage := "connected", inputTokens := inTok, cacheReadTokens := cached
                                  cacheWriteTokens := written }
  | some "content_block_start" =>
    match (jField j "content_block").bind (jStr · "type") with
    | some "thinking" => touch job fun st => { st with stage := "thinking" }
    | some "text" => touch job fun st => { st with stage := "drafting" }
    | some "fallback" => touch job fun st => { st with stage := "connected", thinking := "", text := "" }
    | _ => touch job
  | some "content_block_delta" =>
    let d := jField j "delta"
    match d.bind (jStr · "type") with
    | some "thinking_delta" =>
      let t := (d.bind (jStr · "thinking")).getD ""
      touch job fun st => { st with thinking := st.thinking ++ t }
    | some "text_delta" =>
      let t := (d.bind (jStr · "text")).getD ""
      touch job fun st => { st with stage := "drafting", text := st.text ++ t }
    | _ => touch job
  | some "message_delta" =>
    let out := ((jField j "usage").bind (jNat · "output_tokens")).getD 0
    touch job fun st => { st with outputTokens := out }
  | _ => touch job

/-- What one request came to. -/
structure Outcome where
  http : Option Nat := none
  retryAfter : Option String := none
  /-- An `error` event, or the body of a failed request. -/
  apiErrorType : Option String := none
  apiErrorMessage : Option String := none
  stopReason : Option String := none
  exitCode : UInt32 := 0
  /-- No request was made, because a budget is used up. This says which one, for the server's log. -/
  resting : Option String := none

def apiError (j : Json) : Option (String × String) :=
  match jField j "error" with
  | some e => some ((jStr e "type").getD "error", (jStr e "message").getD "")
  | none => none

/-- An error message from the API, made safe for the log: one short line that holds no key. -/
def scrubbed (config message : String) : String :=
  let m := match config.splitOn "x-api-key: " with
    | _ :: rest :: _ =>
      let key := (rest.splitOn "\"").headD ""
      if key.isEmpty then message else message.replace key "[key]"
    | _ => message
  Clerk.cut 300 (Clerk.oneLine (" ".intercalate ((m.splitOn " ").map fun w => if w.startsWith "sk-" then "[key]" else w)))

#guard scrubbed "header = \"x-api-key: abc123\"\n" "bad key abc123 here" == "bad key [key] here"
#guard scrubbed "" "your key sk-ant-xyz is bad" == "your key [key] is bad"

/-- What a player reads when the clerk cannot work because of a problem on our side. No key, status code
or file name goes here. The reason goes to the server's log. -/
def onStrike : String :=
  "The clerk is on strike! Sorry, that's on us. The rest of the game still works, and you can write a rule in formal text."

/-- Why a request did not produce a reply, in words for the server's log and for a person running
`make sim`. `none` means it worked. Players never read this: see `finalOf`. -/
def failureOf (o : Outcome) : Option String :=
  let detail := " ".intercalate <|
    (o.http.map (s!"HTTP {·}")).toList ++ o.apiErrorType.toList ++ o.apiErrorMessage.toList
  if o.resting.isSome then o.resting
  else if o.exitCode == 28 then some "no reply within the time limit (curl exit 28)"
  else if o.exitCode == 6 || o.exitCode == 7 then some s!"no connection to the API (curl exit {o.exitCode})"
  else if o.exitCode == 127 then some "this server cannot run curl (curl exit 127)"
  else if o.exitCode != 0 then some s!"the connection to the API failed (curl exit {o.exitCode})"
  else
    match o.http, o.apiErrorType with
    | some 401, _ | _, some "authentication_error" => some s!"the API key was refused: {detail}"
    | some 402, _ | _, some "billing_error" => some s!"the API account has a billing problem: {detail}"
    | some 403, _ | _, some "permission_error" => some s!"this API key may not use this model: {detail}"
    | some 404, _ | _, some "not_found_error" => some s!"the API found no such model or path: {detail}"
    | some 429, _ | _, some "rate_limit_error" => some s!"the API's rate limit was reached: {detail}"
    | some 529, _ | _, some "overloaded_error" => some s!"the API is overloaded: {detail}"
    | some c, _ =>
      if c ≥ 400 || o.apiErrorType.isSome then some s!"the API returned an error: {detail}"
      else
        match o.stopReason with
        | some "refusal" => some "the model refused"
        | some "max_tokens" => some "the reply ran past its length limit"
        | some _ => none
        | none => some s!"the reply ended before it finished: {detail}"
    | none, _ => some "the connection closed without a reply"

/-- The request itself is the problem, so the player can do something about it. This is not our fault,
and these words stay as they are when everything else goes on strike. -/
def declined (o : Outcome) (suggesting : Bool := false) : Option String :=
  if o.exitCode != 0 || o.apiErrorType.isSome || o.http.any (· ≥ 400) then none
  else
    match o.stopReason with
    | some "refusal" =>
      some (if suggesting then "Claude declined to suggest a rule. Try again, or write your own rule."
        else "Claude declined to draft this. Rephrase it, or write the formal text yourself.")
    | some "max_tokens" =>
      some (if suggesting then "The suggestion ran past its length limit. Try again, or write your own rule."
        else "The draft ran past its length limit. Try a simpler rule.")
    | _ => none

/-- How a request that did not produce a reply ends a draft. `none` means it worked. -/
def finalOf (o : Outcome) (suggesting : Bool := false) : Option Final :=
  match declined o suggesting with
  | some m => some (.failed m)
  | none =>
    if o.resting.isSome then some (.strike Spend.restingWords)
    else (failureOf o).map fun _ => .strike onStrike

/-- Can asking again help? The API's list is at `platform.claude.com/docs/en/api/errors`. -/
def retryable (o : Outcome) : Bool :=
  o.resting.isNone && (
  [28, 6, 7, 16, 18, 35, 52, 55, 56, 92].contains o.exitCode.toNat ||
  (o.exitCode == 0 && match o.http with
   | some c => c == 408 || c == 409 || c == 429 || c ≥ 500 || (c < 400 && o.apiErrorType.isNone && o.stopReason.isNone)
   | none => true) ||
  (match o.apiErrorType with
   | some t => t == "rate_limit_error" || t == "overloaded_error" || t == "api_error" || t == "timeout_error"
   | none => false))

#guard onStrike.length < 130
#guard retryable { http := some 529, apiErrorType := some "overloaded_error" }
#guard retryable { http := some 500, apiErrorType := some "api_error" }
#guard retryable { http := some 504, apiErrorType := some "timeout_error" }
#guard retryable { http := some 429, apiErrorType := some "rate_limit_error" }
#guard retryable { http := some 200, apiErrorType := some "overloaded_error" }
#guard retryable { http := some 200 }
#guard retryable { exitCode := 7, http := some 0 }
#guard !retryable { http := some 401, apiErrorType := some "authentication_error" }
#guard !retryable { http := some 402, apiErrorType := some "billing_error" }
#guard !retryable { http := some 400, apiErrorType := some "invalid_request_error" }
#guard !retryable { http := some 413, apiErrorType := some "request_too_large" }
#guard !retryable { http := some 200, stopReason := some "refusal" }
#guard !retryable { resting := some "the budget" }
#guard (declined { http := some 200, stopReason := some "refusal" }).isSome
#guard (declined { http := some 529, stopReason := some "refusal" }).isNone

/-- Count what the request that just ended cost. A request stopped part way has no final output count,
so that part is estimated from what arrived, at about four characters a token. -/
private def chargeJob (job : Job) (model : String) : IO Unit := do
  let st ← job.state.get
  let output := if st.outputTokens != 0 then st.outputTokens else (st.text.length + st.thinking.length) / 4
  Spend.charge job.table model st.inputTokens st.cacheReadTokens st.cacheWriteTokens output

/-- Run one request and read it to the end. Blocks this thread only. Every call to the API comes through
here, so this is where the budgets are checked and charged. `model` is the model named in the request,
which sets the price. -/
def runRequest (job : Job) (config model : String) : IO Outcome := do
  if let some why ← Spend.whyResting job.table then
    IO.eprintln s!"[{job.table}] no request to {model}: {why}"
    return { resting := some why }
  -- These fields describe one request, so a request that gets no reply must not repeat the last one's.
  job.state.modify fun st =>
    { st with inputTokens := 0, cacheReadTokens := 0, cacheWriteTokens := 0, outputTokens := 0 }
  let child ← IO.Process.spawn
    { cmd := "curl", args := #["--config", "-"], stdin := .piped, stdout := .piped, stderr := .piped }
  -- curl reads its configuration until end of file, so nothing may keep this handle open: take it
  -- out of `child` before anything captures `child`.
  let (stdin, child) ← child.takeStdin
  job.stop.set (do try child.kill catch _ => pure ())
  stdin.putStr config
  stdin.flush
  let _ := stdin
  let mut out : Outcome := {}
  let mut raw := ""
  repeat
    let line ← child.stdout.getLine
    if line.isEmpty then break
    let l := line.trimAscii.toString
    if l.startsWith "data: " then
      match Json.parse (l.drop 6).toString with
      | .ok j =>
        onEvent job j
        if let some (t, m) := apiError j then
          out := { out with apiErrorType := some t, apiErrorMessage := some m }
        if let some r := (jField j "delta").bind (jStr · "stop_reason") then
          out := { out with stopReason := some r }
      | .error _ => pure ()
    else if l.startsWith "__HTTP__ " then
      match (l.drop 9).toString.splitOn " " with
      | code :: rest =>
        out := { out with http := code.toNat?, retryAfter := rest.head?.filter (!·.isEmpty) }
      | [] => pure ()
    else if !l.isEmpty && !l.startsWith "event:" then
      raw := raw ++ l
  let code ← child.wait
  out := { out with exitCode := code }
  chargeJob job model
  if out.apiErrorType.isNone then
    if let .ok j := Json.parse raw then
      if let some (t, m) := apiError j then
        out := { out with apiErrorType := some t, apiErrorMessage := some m }
  out := { out with apiErrorMessage := out.apiErrorMessage.map (scrubbed config) }
  if !(← job.cancelled.get) then
    if let some why := failureOf out then
      IO.eprintln s!"[{job.table}] request to {model} failed: {why}"
  return out

/-! ## Reading the reply -/

/-- A reply is a DIFFERENCE line and an expression, an expression, or a REFUSE line. A suggestion has
WORDS and WHY lines and an expression, or a REFUSE line. -/
structure Reply where
  difference : Option String := none
  refuse : Option String := none
  words : Option String := none
  why : Option String := none
  formal : String := ""

def parseReply (text : String) : Reply := Id.run do
  let mut r : Reply := {}
  let mut rest : List String := []
  for line in text.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.startsWith "DIFFERENCE:" then
      r := { r with difference := some ((l.drop 11).toString.trimAscii.toString) }
    else if l.startsWith "REFUSE:" then
      r := { r with refuse := some ((l.drop 7).toString.trimAscii.toString) }
    else if l.startsWith "WORDS:" then
      r := { r with words := some ((l.drop 6).toString.trimAscii.toString) }
    else if l.startsWith "WHY:" then
      r := { r with why := some ((l.drop 4).toString.trimAscii.toString) }
    else if !l.startsWith "```" then rest := rest ++ [line]
  -- Any words before the expression are not part of it. The parser judges the rest.
  let formal := rest.dropWhile fun line => !line.trimAscii.toString.startsWith "("
  return { r with formal := ("\n".intercalate formal).trimAscii.toString }

/-- Why a reply's difference line must be written again, if it must. -/
def differenceProblem (r : Reply) : Option String :=
  match r.difference with
  | some d =>
    let words := (d.splitOn " ").filter (!·.isEmpty)
    if words.length > maxDifferenceWords then
      some s!"The DIFFERENCE line has {words.length} words. Keep it under 30."
    else none
  | none => none

/-- Why a formal text cannot go to the table now. An empty list means it can. -/
def problemsOf (g : Game) (seat : Nat) (text : String) : Except String (List String) := do
  let p ← g.parse text
  match g.state with
  | none => pure ["the game has not started"]
  | some s =>
    match p with
    | .law L => pure (lawProblems g.spec.G s L)
    | .deal d =>
      pure (dealProblems s d ++ (if d.signers.contains seat then [] else ["you must be one of the signers of your own deal"]))

/-- Say a constitution problem as a plain sentence. -/
def sentence (s : String) : String :=
  let t := Text.capFirst s
  if t.endsWith "." then t else t ++ "."

def problemsText (ps : List String) : String := " ".intercalate (ps.map sentence)

/-! ## A draft from start to finish -/

/-- Parse and check a formal text against the game as it is now. Each stage is reported as it happens. -/
def checkFormal (job : Job) (current : IO (Option Game)) (text : String) : IO (Except String Unit) := do
  touch job fun st => { st with stage := "parsing" }
  let some g ← current | return .error "the game is gone"
  match g.parse text with
  | .error e => return .error e
  | .ok _ =>
    touch job fun st => { st with stage := "checking" }
    match problemsOf g job.seat text with
    | .error e => return .error e
    | .ok [] =>
      touch job fun st => { st with stage := "previewing" }
      return .ok ()
    | .ok ps => return .error (problemsText ps)

/-- Add the latest request's tokens to what this draft has spent. -/
def addSpent (job : Job) : IO Unit :=
  job.state.modify fun st =>
    { st with spentInput := st.spentInput + st.inputTokens, spentCacheRead := st.spentCacheRead + st.cacheReadTokens
              spentCacheWrite := st.spentCacheWrite + st.cacheWriteTokens, spentOutput := st.spentOutput + st.outputTokens }

/-- How long to wait before asking again, after `tries` tries. -/
def retryWaitMs (o : Outcome) (tries : Nat) : Nat :=
  match o.retryAfter.bind String.toNat? with
  | some n => n * 1000
  | none => 1000 * 2 ^ (tries - 1)

#guard retryWaitMs {} 1 == 1000 && retryWaitMs {} 2 == 2000
#guard retryWaitMs { retryAfter := some "7" } 1 == 7000

/-- One request, asked again up to `maxTries` times while the problem can pass. It stops early if the wait
is too long for a person, or if the time for one request has already gone by. Asks that are not the last
are added to what the draft has spent here. The caller adds the last one. -/
def requestRetrying (job : Job) (config model : String) (seconds : Nat := maxSeconds) : IO Outcome := do
  let start ← IO.monoMsNow
  let mut tries := 1
  repeat
    let out ← runRequest job config model
    if tries ≥ maxTries || !retryable out || (← job.cancelled.get) then return out
    let wait := retryWaitMs out tries
    if wait > maxRetryWaitMs || (← IO.monoMsNow) + wait > start + seconds * 1000 then return out
    addSpent job
    touch job fun st => { st with stage := "retrying", text := "", thinking := "" }
    let mut left := wait + (← IO.rand 0 250)
    while left > 0 do
      if ← job.cancelled.get then return out
      IO.sleep 100
      left := left - min 100 left
    touch job fun st => { st with stage := "sent" }
    tries := tries + 1
  return {}

/-- End a job because of a problem on our side: the reason goes to the log, and the player gets `onStrike`. -/
def strike (job : Job) (why : String) : IO Unit := do
  IO.eprintln s!"[{job.table}] the clerk cannot work: {why}"
  touch job fun st => { st with stage := "done", final := some (.strike onStrike) }

/-- Run a draft on this thread. `current` reads the game as it is now, for each check. `notes` is
the table's clerk log, and `Clerk.memoryBlock` takes only this seat's part of it. -/
def run (job : Job) (cfg : Settings) (current : IO (Option Game)) (notes : List Clerk.Note) : IO Unit := do
  let isCancelled : IO Bool := job.cancelled.get
  let finish (f : Final) : IO Unit := do
    if let .ready formal _ true := f then job.onReady formal
    touch job fun st => { st with stage := "done", final := some f }
  let check := checkFormal job current
  -- Formal text is checked directly. It does not need the model.
  if job.words.trimAscii.toString.startsWith "(" then
    match ← check job.words.trimAscii.toString with
    | .ok () => finish (.ready job.words.trimAscii.toString none false)
    | .error e => finish (.refused e)
    return
  let some key := cfg.key | strike job "this server has no API key"
  let system ← try IO.FS.readFile cfg.promptPath catch _ => pure ""
  if system.isEmpty then
    strike job s!"the instructions are missing: {cfg.promptPath}"
    return
  let some g ← current | finish (.failed "The game is gone.")
  let some s := g.state | finish (.failed "The game has not started.")
  let memory := Clerk.memoryBlock g job.seat notes
  let mut retry : Option (String × String) := none
  for n in (List.range maxAttempts).map (· + 1) do
    touch job fun st => { st with stage := "sent", attempt := n, text := "", thinking := "",
                                  retryReason := retry.map (·.2) }
    let body := requestBody cfg system (userMessage g s job.seat memory job.words retry)
    let outcome ← requestRetrying job (curlConfig cfg key body) cfg.model
    addSpent job
    if ← isCancelled then
      finish .cancelled
      return
    if let some f := finalOf outcome then
      finish f
      return
    let text := (← job.state.get).text
    let reply := parseReply text
    if let some why := reply.refuse then
      finish (.refused why)
      return
    match ← check reply.formal with
    | .ok () =>
      match differenceProblem reply with
      | some why =>
        if n == maxAttempts then
          finish (.ready reply.formal reply.difference true)
          return
        retry := some (text, why)
      | none =>
        finish (.ready reply.formal reply.difference true)
        return
    | .error err =>
      if n == maxAttempts then
        finish (.refused s!"The clerk could not write this as a legal rule. {err}")
        return
      retry := some (text, err)

end CharterServer.Formalize
