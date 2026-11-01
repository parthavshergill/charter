import Lean.Data.Json
import Server.Table
import Server.Player
import Server.View

/-!
# Claude seats

A Claude seat decides through the Anthropic API, called through `curl` as the clerk does. The key goes
to `curl` through its standard input. It is not stored, printed or logged.

Each decision is one request with no history: the rules, the seat's persona, its private memory, the
public state, the legal moves and the open decisions. That keeps every prompt bounded. The fixed part
goes in cached system blocks. The answer is JSON in a fixed form (`replySchema`), read by `parseReply`.
The engine has the final word on every action. An answer that does not read is asked for again, and
then the seat falls back to a safe legal action, so a slow or broken seat cannot stall the game.

Other players' words are data. They go in the user message between markers, and `Clerk.neutralize`
stops them from closing a marker. The system message says that only it gives instructions. Players can
still lie to each other. That is the game.
-/

namespace CharterServer.Seat
open Lean Charter CharterServer.Game CharterServer.Player

variable {G : GameDef}

/-! ## The form of an answer -/

private def schemaObj (props : List (String × Json)) : Json :=
  Json.mkObj
    [ ("type", "object"), ("additionalProperties", toJson false)
    , ("required", toJson (props.map (·.1)))
    , ("properties", Json.mkObj props) ]

private def tStr : Json := Json.mkObj [("type", "string")]
private def tInt : Json := Json.mkObj [("type", "integer")]
private def tBool : Json := Json.mkObj [("type", "boolean")]
private def nullable (t : String) : Json :=
  Json.mkObj [("anyOf", Json.arr #[Json.mkObj [("type", t)], Json.mkObj [("type", "null")]])]

private def tBundle : Json :=
  Json.mkObj [("type", "array"), ("items", schemaObj [("res", tStr), ("n", tInt)])]

/-- One kind of action. The API makes an answer give an object's fields in the schema's order, and a
Lean `Json` object sorts its keys. So the field that names the action must sort first of all fields:
if it does not, a model that starts with it can only write the actions whose other fields sort after
it. That is why it is called `action`, and why the fields of `place_link` are not `a` and `b`. -/
private def action (t : String) (props : List (String × Json) := []) : Json :=
  schemaObj (("action", Json.mkObj [("const", t)]) :: props)

/-- The answer a seat must give. -/
def replySchema : Json :=
  schemaObj
    [ ("say", nullable "string")
    , ("whispers", Json.mkObj [("type", "array"), ("items", schemaObj [("to", tInt), ("text", tStr)])])
    , ("confess", nullable "string")
    , ("remember", nullable "string")
    , ("actions", Json.mkObj [("type", "array"), ("items", Json.mkObj [("anyOf", Json.arr #[
        action "place" [("kind", tStr), ("spot", tInt)],
        action "place_link" [("kind", tStr), ("from_spot", tInt), ("to_spot", tInt)],
        action "bank_trade" [("give", tStr), ("get", tStr)],
        action "offer" [("to", nullable "integer"), ("give", tBundle), ("get", tBundle)],
        action "accept" [("id", tInt)],
        action "cancel" [("id", tInt)],
        action "declare" [("res", tStr), ("n", tInt)],
        action "vote" [("id", tInt), ("yes", tBool)],
        action "sign" [("id", tInt)],
        action "exit" [("deal_id", tInt)],
        action "draft" [("words", tStr)],
        action "propose_draft",
        action "end_turn" ])])]) ]

/-- The answer to the questions after a game. -/
def interviewSchema : Json :=
  schemaObj
    [ ("confusing", tStr), ("boring", tStr), ("great", tStr), ("could_not_say", tStr)
    , ("best_moment", tStr), ("farewell", tStr) ]

/-! ## Reading an answer -/

structure Whisper where
  to : Nat
  text : String
  deriving Repr

structure Reply where
  say : Option String := none
  whispers : List Whisper := []
  confess : Option String := none
  remember : Option String := none
  actions : List Json := []

private def nonEmpty (s : Option String) : Option String :=
  s.filter fun x => !x.trimAscii.isEmpty

/-- Read an answer. An answer must be one JSON object with an `actions` list. -/
def parseReply (text : String) : Except String Reply := do
  let j ← Json.parse text.trimAscii.toString
  let actions ← match (j.getObjVal? "actions").toOption with
    | some a => a.getArr?
    | none => throw "the answer has no actions list"
  let whispers := match (j.getObjVal? "whispers").toOption.bind (·.getArr?.toOption) with
    | some ws => ws.toList.filterMap fun w => do
        return { to := ← jNat w "to", text := ← jStr w "text" }
    | none => []
  return { say := nonEmpty (jStr j "say"), whispers, confess := nonEmpty (jStr j "confess")
           remember := nonEmpty (jStr j "remember"), actions := actions.toList }

/-- What one action of an answer asks for. -/
inductive Act where
  | event (ev : Json)
  | draft (words : String)
  | proposeDraft
  deriving Inhabited

private def need {α : Type} (what : String) : Option α → Except String α
  | some x => .ok x
  | none => .error s!"an action is missing {what}"

/-- Put a link's two spots in the order the map uses. -/
def linkInOrder (g : Game) (a b : Nat) : Nat × Nat :=
  if g.spec.G.map.links.contains (b, a) && !g.spec.G.map.links.contains (a, b) then (b, a) else (a, b)

/-- Turn one action into an event for this seat. The engine still decides if the event is legal. -/
def actOfJson (g : Game) (seat : Nat) (a : Json) : Except String Act := do
  let move (m : Json) : Json := Json.mkObj [("t", "move"), ("seat", toJson seat), ("move", m)]
  let num (k : String) : Except String Nat := need k (jNat a k)
  let txt (k : String) : Except String String := need k (jStr a k)
  let some t := jStr a "action" | throw "an action has no type"
  let ev ← match t with
    | "place" =>
      pure (move (Json.mkObj [("t", "place"), ("kind", ← txt "kind"), ("spot", toJson (← num "spot"))]))
    | "place_link" =>
      let (x, y) := linkInOrder g (← num "from_spot") (← num "to_spot")
      pure (move (Json.mkObj [("t", "place"), ("kind", ← txt "kind"), ("link", toJson [x, y])]))
    | "bank_trade" =>
      pure (move (Json.mkObj [("t", "bankTrade"), ("give", ← txt "give"), ("get", ← txt "get")]))
    | "offer" =>
      let give ← need "give" (jField a "give")
      let get ← need "get" (jField a "get")
      pure (move (Json.mkObj [("t", "offer"), ("to", toJson (jNat a "to")), ("give", give), ("get", get)]))
    | "accept" => pure (move (Json.mkObj [("t", "accept"), ("id", toJson (← num "id"))]))
    | "cancel" => pure (move (Json.mkObj [("t", "cancel"), ("id", toJson (← num "id"))]))
    | "declare" => pure (move (Json.mkObj [("t", "declare"), ("res", ← txt "res"), ("n", toJson (← num "n"))]))
    | "end_turn" => pure (move (Json.mkObj [("t", "endTurn")]))
    | "vote" =>
      let yes ← need "yes" (jBool a "yes")
      pure (Json.mkObj [("t", "vote"), ("seat", toJson seat), ("id", toJson (← num "id")), ("yes", toJson yes)])
    | "sign" => pure (Json.mkObj [("t", "sign"), ("seat", toJson seat), ("id", toJson (← num "id"))])
    | "exit" => pure (Json.mkObj [("t", "exit"), ("seat", toJson seat), ("dealId", toJson (← num "deal_id"))])
    | "draft" =>
      let words ← txt "words"
      if words.trimAscii.toString.length < 12 then
        throw "a draft needs words: say the whole rule you want, or leave the draft out"
      return .draft words
    | "propose_draft" => return .proposeDraft
    | other => throw s!"there is no action called {other}"
  -- The form of the event must read. Whether it is legal now is for the engine.
  discard <| eventOfJson g ev
  return .event ev

/-! ## The prompt -/

/-- What a game's spots pay, in words. -/
def spotPays (G : GameDef) (v : Nat) : String :=
  let rs := (paidRegions G).filter (·.spots.contains v)
  if rs.isEmpty then "pays nothing" else ", ".intercalate (rs.map fun r => s!"{r.res} on {r.number}")

/-- The fixed facts of a game: the same for every seat at every moment, so they stay in the cache. -/
def gameFacts (spec : GameSpec) : String :=
  let G := spec.G
  let res := ", ".intercalate (G.resources.map (·.name))
  let pieces := "\n".intercalate (G.pieces.map fun d =>
    s!"- {d.name}: costs {Text.bundleText d.cost}; {d.points} points; goes on {Formalize.placementS d.placement}; collects {d.yield} when a hex it touches pays; limit {d.limit} per seat")
  let chance := ", ".intercalate ((Scene.rollsOf G).map fun r => s!"{r}: {Scene.chanceOf G r}")
  let spots := "\n".intercalate ((List.range G.map.spotCount).map fun v =>
    let near := (G.map.links.filterMap fun l =>
      if l.1 == v then some l.2 else if l.2 == v then some l.1 else none)
    s!"{v}: {spotPays G v}; next to {", ".intercalate (near.map toString)}")
  let guide := if spec.guide.isEmpty then "" else s!"\n\n{spec.guide}"
  s!"## This game: {spec.name}
The first seat to {G.targetPoints} points wins, within {G.rounds} rounds. Dice: {G.diceCount} dice with {G.diceSides} sides. The resources are {res}. The bank trades {G.bankRate} of a resource for 1 of another. Proposing a law costs nothing. In setup each seat places, free: {", ".intercalate G.setupPieces}.{guide}

Pieces:
{pieces}

How many ways the dice can show each total: {chance}.

The corners of the map, by number: what each pays, and which corners are next to it.
{spots}"

/-- The text of the first system block. A seat that has read no rules gets no rules section. -/
def rulesFor (rulesFile : String) (onScreenOnly : Bool) : String :=
  if onScreenOnly then
    match rulesFile.splitOn "## The rules" with
    | before :: _ => before.trimAscii.toString
    | [] => rulesFile
  else rulesFile

def personaText (p : Persona.Persona) (seat : Nat) : String :=
  let goal := if p.goal.isEmpty then "" else
    s!"\n\nYour private goal. No other seat can see this. It is for you alone, and it matters more to you than anything above: {p.goal}"
  s!"You are {p.name}, {p.voice}. You sit in seat {seat}. Talk like this person at all times.\n\n{p.styleOf.play}{goal}"

/-- The request body. The fixed parts come first and are cached: the rules and the game's facts for
every seat, then the persona for this seat. Nothing that changes goes in the system message. -/
def requestBody (st : SeatSettings) (model : String) (rules persona user : String) (schema : Json) : Json :=
  let cached (t : String) : Json :=
    Json.mkObj [("type", "text"), ("text", t), ("cache_control", Json.mkObj [("type", "ephemeral")])]
  Json.mkObj
    [ ("model", model)
    , ("max_tokens", toJson st.maxTokens)
    , ("stream", toJson true)
    , ("thinking", Json.mkObj [("type", "adaptive")])
    , ("output_config", Json.mkObj
        [("effort", st.effort), ("format", Json.mkObj [("type", "json_schema"), ("schema", schema)])])
    , ("fallbacks", "default")
    , ("system", Json.arr #[cached rules, cached persona])
    , ("messages", Json.arr #[Json.mkObj [("role", "user"), ("content", user)]]) ]

/-- A law for the prompt: its source, which is what binds, and then its description, if it has one. -/
def lawForSeat (book : Describe.Book) (L : Law) : String :=
  let source := s!"Rule source, the binding text: {Rules.printProposal (.law L)}"
  match Describe.textOf book L with
  | some (who, text) => s!"{source} {who}, which does not bind: {text}"
  | none => source

/-- A proposal, for the prompt. -/
def proposalLine (sit : Situation) (book : Describe.Book) (p : OpenProposal) : String :=
  let g := sit.game
  let s := sit.state
  let yes := p.yesCount
  let seats := s.turnOrder.length
  let need := seats / 2 + 1
  let votes := ", ".intercalate (p.votes.map fun v => s!"seat {v.1} {if v.2 then "yes" else "no"}")
  match p.body with
  | .law L =>
    let preview := (Preview.lawPreview s p.id L (some sit.seat) g.nameOf).compress
    s!"- Law proposal {p.id}, by seat {p.by_}, titled \"{L.title}\". {lawForSeat book L} Votes so far: {if votes.isEmpty then "none" else votes}. It has {yes} yes of the {need} it needs. What it would do at this table now: {preview}"
  | .deal d =>
    s!"- Deal proposal {p.id}, by seat {p.by_}: {Text.dealLine g.nameOf d} Signed so far: {p.signed}. Signers: {d.signers}."

/-- The list of what a seat can do now, grouped so that it stays short. -/
def legalBlock (sit : Situation) : String :=
  let G := sit.game.spec.G
  let s := sit.state
  let legal := sit.legal.get
  let kinds := (legal.filterMap fun | .place k _ => some k | _ => none).eraseDups
  let places := kinds.map fun k =>
    let spots := legal.filterMap fun | .place k' (.spot v) => if k' == k then some v else none | _ => none
    let links := legal.filterMap fun | .place k' (.link l) => if k' == k then some l else none | _ => none
    let cost := if s.phase == .setup then "free" else Text.bundleText (s.costOf k)
    let spotText := if spots.isEmpty then "" else
      " at spot: " ++ "; ".intercalate (spots.map fun v => s!"{v} ({spotPays G v})")
    let linkText := if links.isEmpty then "" else
      " on link: " ++ ", ".intercalate (links.map fun l => s!"{l.1}-{l.2}")
    s!"- {k} ({cost}){spotText}{linkText}"
  let trades := legal.filterMap fun
    | .bankTrade a b => if markRes G a || markRes G b then none else some (a, b)
    | _ => none
  let gives := (trades.map (·.1)).eraseDups
  let bank := gives.map fun a =>
    s!"- bank: give {s.rules.bankRate} {a} for 1 of {", ".intercalate ((trades.filter (·.1 == a)).map (·.2))}"
  let accepts := sit.offers.get.map fun o => s!"- accept offer {o.id}"
  let cancels := legal.filterMap fun | .cancel i => some s!"- cancel your offer {i}" | _ => none
  let ending := if legal.contains .endTurn then ["- end_turn"] else []
  let readsDeclared := s.laws.any (Rules.lawReadsDeclared ·.2) || s.openProposals.any fun p =>
    match p.body with
    | .law L => Rules.lawReadsDeclared L
    | .deal _ => false
  let declares := if readsDeclared && s.phase == .actions && s.isTurnOf sit.seat then
      [s!"- declare: set your public number for a resource, from 0 to {maxDeclared}"] else []
  let lines := places ++ bank ++ accepts ++ cancels ++ declares ++ ending
  if lines.isEmpty then "nothing on the board" else "\n".intercalate lines

/-- The game as it is now. All of it is public. -/
def gameBlock (sit : Situation) (book : Describe.Book) : String :=
  let g := sit.game
  let G := g.spec.G
  let s := sit.state
  let seats := "\n".intercalate (s.turnOrder.map fun p =>
    let you := if p == sit.seat then " (you)" else ""
    s!"- seat {p}: {Clerk.oneLine (g.nameOf p)}{you}: {Formalize.seatFacts s p}")
  let held (a : Account) : String :=
    let xs := (G.resources.map (·.name)).filterMap fun r =>
      let n := s.balance a r
      if n == 0 then none else some s!"{n} {r}"
    if xs.isEmpty then "nothing" else ", ".intercalate xs
  let turn := match s.currentSeat with
    | some p => s!"It is seat {p}'s turn."
    | none => ""
  let phase := if s.phase == .setup then "Setup." else s!"Round {s.round} of {G.rounds}."
  let pieces := "\n".intercalate (s.rules.pieces.map fun d =>
    s!"- {d.name}: costs {Text.bundleText d.cost}; {d.points} points; goes on {Formalize.placementS d.placement}; collects {d.yield}; limit {d.limit}; you own {s.countOf sit.seat d.name}")
  let board := "\n".intercalate (s.turnOrder.map fun p =>
    let mine := s.pieces.filter (·.owner == p)
    let at_ (x : Piece) : String := match x.loc with
      | .spot v => s!"{x.kind} at {v}"
      | .link l => s!"{x.kind} on {l.1}-{l.2}"
    s!"- seat {p}: {if mine.isEmpty then "nothing" else ", ".intercalate (mine.map at_)}")
  let laws := if s.laws.isEmpty then "none" else "\n".intercalate (s.laws.map fun x =>
    s!"- Law {x.1}, titled \"{x.2.title}\". {lawForSeat book x.2}")
  let declaredRows := s.turnOrder.flatMap fun p =>
    (G.resources.map (·.name)).filterMap fun r =>
      let n := s.declared p r
      if n == 0 then none else some s!"seat {p} declared {n} {r}"
  let deals := if s.deals.isEmpty then "none" else "\n".intercalate (s.deals.map fun d =>
    s!"- Deal {d.id}, until round {d.lastRound}: {Text.dealLine g.nameOf d.deal}")
  let open_ := if s.openProposals.isEmpty then "none" else
    "\n".intercalate (s.openProposals.map (proposalLine sit book))
  let offers := if s.offers.isEmpty then "none" else "\n".intercalate (s.offers.map fun o =>
    let to := match o.to with
      | some q => s!"to seat {q}"
      | none => "to anyone"
    s!"- Offer {o.id}, from seat {o.src} {to}: gives {Text.bundleText o.give}, asks {Text.bundleText o.get}")
  let roll := match s.lastRoll with
    | some r => s!" The last roll was {r}."
    | none => ""
  s!"{phase} {turn}{roll} You are seat {sit.seat}, and you have exactly {s.pointsOf sit.seat} points. Trust this number and not your notes. First to {G.targetPoints} points wins. The bank trades {s.rules.bankRate} for 1. The treasury holds {held .treasury}.

Seats:
{seats}

Pieces under the rules in force:
{pieces}

The board:
{board}

Laws in force:
{laws}
{if declaredRows.isEmpty then "" else s!"\nDeclared this round: {", ".intercalate declaredRows}.\n"}
Deals running:
{deals}

Proposals before the table:
{open_}

Open offers:
{offers}"

/-- Everything the seat reads, in one message. Player words are between markers and cannot close them. -/
def userMessage (sit : Situation) (book : Describe.Book) (talk : Array Talk.Line) (mind : Mind) (callsLeft : Nat)
    (retry : Option (String × String)) : String :=
  let g := sit.game
  let s := sit.state
  let who (seat : Nat) : String := s!"seat {seat} ({Clerk.oneLine (g.nameOf seat)})"
  let events := ((g.chronicle.toList.drop mind.chronicleSeen).reverse.take 60).reverse.map fun l =>
    Clerk.oneLine l.text
  let publicLines := ((talk.toList.filter (·.kind == "public")).reverse.take 40).reverse.map fun l =>
    Clerk.oneLine s!"{who l.by_}: {l.text}"
  let privateLines := ((talk.toList.filter fun l =>
      l.kind == "private" && (l.by_ == sit.seat || l.to == some sit.seat)).reverse.take 20).reverse.map fun l =>
    if l.by_ == sit.seat then Clerk.oneLine s!"you to {who (l.to.getD 0)}: {l.text}"
    else Clerk.oneLine s!"{who l.by_} to you: {l.text}"
  let notes := Clerk.fitNewest Clerk.maxMemoryChars (mind.notes.toList.map Clerk.oneLine)
  let block (tag : String) (lines : List String) : String :=
    if lines.isEmpty then "" else s!"<{tag}>\n{"\n".intercalate lines}\n</{tag}>\n\n"
  let draft :=
    if mind.draftWords.isEmpty then "" else
    s!"<your_draft>\nYou asked the clerk: {Clerk.oneLine mind.draftWords}\n{Clerk.neutralize mind.draftResult}\n</your_draft>\n\n"
  let asks :=
    (sit.votes.map fun p => s!"vote on law proposal {p.id}") ++
    (sit.signs.map fun p => s!"sign deal proposal {p.id}, if you want it") ++
    (sit.offers.get.map fun o => s!"accept offer {o.id}, if you want it")
  let task :=
    if sit.myTurn then
      if s.phase == .setup then "It is your turn in setup. Place your free pieces, then end your turn."
      else
        let hurry := if callsLeft ≤ 2 then s!" You have {callsLeft} more answers this turn, so finish up." else ""
        s!"It is your turn. Do what you want, then end your turn.{hurry} You have {maxActionsPerTurn - s.actionsThisTurn sit.seat} actions left this turn."
    else if asks.isEmpty then "It is not your turn. You may talk or propose a draft."
    else s!"It is not your turn. You can {"; ".intercalate asks}."
  let open_ := if asks.isEmpty || !sit.myTurn then "" else s!" You can also {"; ".intercalate asks}."
  let again := match retry with
    | some (prior, err) =>
      s!"\n\n<rejected_answer>\n{Clerk.neutralize (Clerk.cut 1500 prior)}\n</rejected_answer>\nThe program could not read that answer. It said: {Clerk.neutralize err} Answer again in the required form."
    | none => ""
  s!"<game>
{Clerk.neutralize (gameBlock sit book)}
</game>

{block "recent_events" events}{block "table_talk" publicLines}{block "private_messages" privateLines}{block "your_memory" notes}{block "what_happened_to_your_last_actions" (mind.results.map Clerk.oneLine)}{draft}<what_you_can_do_on_the_board>
{legalBlock sit}
</what_you_can_do_on_the_board>

{task}{open_}{again}"

/-! ## Calling the API -/

/-- Can asking again help? -/
def retryable (o : Formalize.Outcome) : Bool :=
  o.resting.isNone && (
  [28, 6, 7, 35, 52, 55, 56].contains o.exitCode.toNat ||
  (match o.http with
   | some c => c == 408 || c == 409 || c == 429 || c ≥ 500
   | none => o.exitCode == 0) ||
  (match o.apiErrorType with
   | some t => t == "rate_limit_error" || t == "overloaded_error" || t == "api_error"
   | none => false))

/-- The API refused the key, the model or the request. Asking again cannot help. -/
def hopeless (o : Formalize.Outcome) : Bool :=
  o.http == some 401 || o.http == some 403 || o.http == some 404 ||
  o.apiErrorType == some "authentication_error" || o.apiErrorType == some "permission_error" ||
  o.apiErrorType == some "not_found_error"

/-- Wait for a free slot, and for any rate-limit pause to end, then run this. -/
partial def withSlot {α : Type} (ctx : Ctx) (act : IO α) : IO α := do
  let now ← IO.monoMsNow
  let cool ← ctx.coolUntil.get
  if now < cool then
    IO.sleep (min 2000 (cool - now)).toUInt32
    return ← withSlot ctx act
  let got ← ctx.inFlight.modifyGet fun n =>
    if n < ctx.seat.concurrency then (true, n + 1) else (false, n)
  if !got then
    IO.sleep 100
    return ← withSlot ctx act
  try act
  finally ctx.inFlight.modify (· - 1)

/-- What one request came to. -/
structure Answer where
  text : String := ""
  input : Nat := 0
  cacheRead : Nat := 0
  cacheWrite : Nat := 0
  output : Nat := 0

private def freshJob (code : String) (seat : Nat) : IO Formalize.Job := do
  let now ← IO.monoMsNow
  return { id := 0, seat, words := "", startedMs := now, table := code
           state := ← IO.mkRef { lastEventMs := now }
           stop := ← IO.mkRef (pure ())
           cancelled := ← IO.mkRef false }

private def addUsage (ctx : Ctx) (code : String) (f : Usage → Usage) : IO Unit :=
  ctx.usage.modify fun m => m.insert code (f (m.getD code {}))

/-- One request with its retries. It returns the model's text, or why there is none. Each request is
written to the table's seat log with what it cost. -/
def request (ctx : Ctx) (code : String) (seat : Nat) (what : String) (body : Json) : IO (Except String Answer) := do
  let cfg ← Formalize.settings ctx.root
  let some key := cfg.key | return .error "this server has no API key"
  let start ← IO.monoMsNow
  let deadline := start + ctx.seat.budgetS * 1000
  let mut tries : Nat := 0
  let event := ((← findEntry ctx code).map (·.game.events)).getD 0
  repeat
    tries := tries + 1
    let job ← freshJob code seat
    let sentAt ← IO.monoMsNow
    let outcome ← withSlot ctx do
      ctx.running.modify (·.insert (code, seat) job)
      try Formalize.runRequest job (Formalize.curlConfig cfg key body ctx.seat.timeoutS) ((jStr body "model").getD "")
      finally ctx.running.modify (·.erase (code, seat))
    let st ← job.state.get
    let ms := (← IO.monoMsNow) - sentAt
    let failure := Formalize.failureOf outcome
    seatNote ctx code <| Json.mkObj
      [ ("k", "call"), ("seat", toJson seat), ("what", what), ("event", toJson event), ("ms", toJson ms)
      , ("input", toJson st.inputTokens), ("cacheRead", toJson st.cacheReadTokens)
      , ("cacheWrite", toJson st.cacheWriteTokens), ("output", toJson st.outputTokens)
      , ("http", toJson outcome.http), ("stop", toJson outcome.stopReason), ("failure", toJson failure)
      , ("answer", Clerk.cut 6000 st.text) ]
    if let some dir ← IO.getEnv "CHARTER_SEAT_DUMP" then
      IO.FS.writeFile (System.FilePath.mk dir / s!"{code}-{seat}-{event}-{sentAt}.json") body.pretty
    addUsage ctx code fun u =>
      { u with calls := u.calls + 1, input := u.input + st.inputTokens, cacheRead := u.cacheRead + st.cacheReadTokens
               cacheWrite := u.cacheWrite + st.cacheWriteTokens, output := u.output + st.outputTokens }
    match failure with
    | none =>
      return .ok { text := st.text, input := st.inputTokens, cacheRead := st.cacheReadTokens
                   cacheWrite := st.cacheWriteTokens, output := st.outputTokens }
    | some msg =>
      if hopeless outcome then
        ctx.fatal.set (some msg)
        return .error msg
      -- If the timer stopped this request, the seat's turn is over. Asking again cannot help it.
      if ← job.cancelled.get then return .error "the timer ended this turn"
      if !retryable outcome then return .error msg
      addUsage ctx code fun u => { u with retries := u.retries + 1 }
      let backoff := min 60000 (1000 * 2 ^ tries)
      let wait := match outcome.retryAfter.bind String.toNat? with
        | some n => n * 1000
        | none => backoff
      let jitter ← IO.rand 0 500
      let now ← IO.monoMsNow
      if outcome.http == some 429 || outcome.apiErrorType == some "rate_limit_error" then
        ctx.coolUntil.modify (max (now + wait))
      if now + wait + jitter > deadline || tries ≥ 8 then return .error msg
      IO.sleep (wait + jitter).toUInt32
  return .error "no reply"

/-! ## A seat's memory -/

def getMind (ctx : Ctx) (code : String) (seat : Nat) : IO Mind := do
  return (← ctx.minds.get).getD (code, seat) {}

def modifyMind (ctx : Ctx) (code : String) (seat : Nat) (f : Mind → Mind) : IO Unit :=
  ctx.minds.modify fun m => m.insert (code, seat) (f (m.getD (code, seat) {}))

/-- Read back what a table's seats noted, after a restart. -/
def restoreMinds (ctx : Ctx) (code : String) : IO Unit := do
  for r in ← seatRecords ctx code do
    match jStr r "k", jNat r "seat" with
    | some "note", some seat =>
      modifyMind ctx code seat fun m => { m with notes := m.notes.push ((jStr r "text").getD "") }
    | some "interview", some seat =>
      modifyMind ctx code seat fun m => { m with interviewed := true }
    | _, _ => pure ()

/-! ## Deciding -/

/-- The keys for what this seat is being asked about now. -/
def askedKeys (sit : Situation) : List String :=
  (sit.votes.map fun p => s!"vote:{p.id}") ++ (sit.signs.map fun p => s!"sign:{p.id}") ++
  (sit.offers.get.map fun o => s!"offer:{o.id}")

/-- Is there something new for this seat to answer out of turn? -/
def hasNews (sit : Situation) (mind : Mind) : Bool :=
  mind.draftFresh || (askedKeys sit).any (!mind.asked.contains ·)

/-- A safe legal action, for a seat with no answer. In setup it places where the dice pay most, because
a seat should not lose its start to a network error. Otherwise it ends the turn. Out of turn it does
nothing, so a law lapses or fails by the rules. -/
def fallbackEvents (sit : Situation) : List Json :=
  if !sit.myTurn then [] else
  let endIt := Bots.moveEvent sit.seat .endTurn
  if sit.state.phase == .setup then
    let m := Bots.setupMove sit.state sit.legal.get
    if m == .endTurn then [endIt] else [Bots.moveEvent sit.seat m, endIt]
  else [endIt]

/-- Talk and notes from an answer. These are not game events. -/
def applyTalk (ctx : Ctx) (code : String) (sit : Situation) (r : Reply) : IO Unit := do
  let seat := sit.seat
  if let some t := r.say then addTalk ctx code "public" seat none t
  for w in r.whispers.take 3 do
    if w.to != seat && sit.state.turnOrder.contains w.to then
      addTalk ctx code "private" seat (some w.to) w.text
  if let some t := r.confess then addTalk ctx code "confession" seat none t
  if let some t := r.remember then
    let t := Clerk.cut 600 t
    modifyMind ctx code seat fun m => { m with notes := m.notes.push t }
    let event := ((← findEntry ctx code).map (·.game.events)).getD 0
    seatNote ctx code (Json.mkObj [("k", "note"), ("seat", toJson seat), ("event", toJson event), ("text", t)])

/-- Ask the clerk, wait for its result, and tell the seat. This is the same clerk a person uses. The
result is shown to the seat, and it decides whether to propose it. -/
def runDraft (ctx : Ctx) (code : String) (seat : Nat) (words : String) : IO Unit := do
  let words := Clerk.cut Clerk.maxRequestChars words
  let job ← startDraft ctx code seat words
  for _ in [0:4000] do
    if (← job.state.get).final.isSome then break
    IO.sleep 100
  let st ← job.state.get
  let some e ← findEntry ctx code | return
  let g := e.game
  let (result, formal, outcome) : String × Option String × String := match st.final with
    | some (.ready text diff _) =>
      let review := match g.parse text with
        | .ok (.law L) => Rules.printProposal (.law L)
        | .ok (.deal d) => Text.dealLine g.nameOf d
        | .error _ => text
      let preview := match g.parse text, g.state with
        | .ok (.law L), some s =>
          s!"\nWhat it would do at this table now: {(Preview.draftPreview s s.nextProposalId L seat g.nameOf).compress}"
        | _, _ => ""
      let dtext := match diff with
        | some d => s!"\nThe clerk says this differs from what you asked: {d}"
        | none => ""
      (s!"The clerk wrote this rule. What binds is the rule itself: {review}{dtext}{preview}\nTo put it before the table, use propose_draft.", some text, "ready")
    | some (.refused why) => (s!"The clerk could not write this as a rule. It said: {why}", none, "refused")
    | some (.failed why) => (s!"The clerk could not be reached: {why}", none, "failed")
    | some .cancelled => ("The draft was cancelled.", none, "cancelled")
    | none => ("The clerk took too long.", none, "failed")
  modifyMind ctx code seat fun m =>
    { m with draftWords := words, draftResult := result, draftFormal := formal, draftFresh := true }
  addUsage ctx code fun u =>
    { u with calls := u.calls + st.attempt, input := u.input + st.spentInput, cacheRead := u.cacheRead + st.spentCacheRead
             cacheWrite := u.cacheWrite + st.spentCacheWrite, output := u.output + st.spentOutput }
  let difference := match st.final with
    | some (.ready _ d _) => toJson d
    | _ => Json.null
  let why := match st.final with
    | some (.refused w) | some (.failed w) => toJson w
    | _ => Json.null
  seatNote ctx code <| Json.mkObj
    [ ("k", "draft"), ("seat", toJson seat), ("event", toJson g.events), ("words", words), ("outcome", outcome)
    , ("formal", toJson formal), ("difference", difference), ("why", why), ("attempts", toJson st.attempt)
    , ("ms", toJson ((← IO.monoMsNow) - job.startedMs))
    , ("input", toJson st.spentInput), ("cacheRead", toJson st.spentCacheRead)
    , ("cacheWrite", toJson st.spentCacheWrite), ("output", toJson st.spentOutput) ]

/-- A Claude seat, as a player. -/
def claudePlayer (ctx : Ctx) (code : String) (seat : Nat) : Player :=
  { kind := "claude"
    choose := fun sit => do
      let g := sit.game
      let mind0 ← getMind ctx code seat
      let keys := askedKeys sit
      modifyMind ctx code seat fun m => { m with asked := (m.asked ++ keys).eraseDups, draftFresh := false }
      let fall (why : String) : IO Choice := do
        addUsage ctx code fun u => { u with fallbacks := u.fallbacks + 1 }
        seatNote ctx code (Json.mkObj [("k", "fallback"), ("seat", toJson seat), ("event", toJson g.events), ("why", why)])
        return .act (fallbackEvents sit)
      let some persona := (g.personas[seat]?).join | fall "this seat has no persona"
      let rulesFile ← try IO.FS.readFile (ctx.root / "Server" / "player_rules.md") catch _ => pure ""
      if rulesFile.isEmpty then return ← fall "the rules are missing"
      let rules := rulesFor rulesFile persona.styleOf.onScreenOnly ++ "\n\n" ++ gameFacts g.spec
      let talk := ((← findEntry ctx code).map (·.talk)).getD #[]
      let callsLeft := ctx.seat.callsPerTurn - mind0.callsThisTurn
      let book ← bookOf ctx code
      let mut retry : Option (String × String) := none
      for _ in [0:3] do
        let user := userMessage sit book talk mind0 callsLeft retry
        let body := requestBody ctx.seat ctx.seat.model rules (personaText persona seat) user replySchema
        match ← request ctx code seat "decide" body with
        | .error why => return ← fall why
        | .ok answer =>
          match parseReply answer.text >>= fun r => do
              let acts ← r.actions.mapM (actOfJson g seat)
              pure (r, acts) with
          | .error err => retry := some (answer.text, err)
          | .ok (r, acts) =>
            applyTalk ctx code sit r
            modifyMind ctx code seat fun m =>
              { m with chronicleSeen := g.chronicle.size, results := [] }
            -- What comes after a draft is not carried out: the seat is asked again with the result.
            let before := acts.takeWhile fun | .draft _ => false | _ => true
            let words := acts.findSome? fun | .draft w => some w | _ => none
            modifyMind ctx code seat fun m => { m with pendingDraft := words }
            let formal := mind0.draftFormal
            let events := before.filterMap fun
              | .event ev => some ev
              | .proposeDraft => formal.map fun t =>
                Json.mkObj [("t", "propose"), ("seat", toJson seat), ("text", t)]
              | .draft _ => none
            if formal.isNone && before.any (fun | .proposeDraft => true | _ => false) then
              modifyMind ctx code seat fun m =>
                { m with results := m.results ++ ["You have no draft to propose. Use draft first."] }
            return .act events
      fall "its answers could not be read"
    told := fun ev refused => do
      match refused with
      | some why =>
        let what := Clerk.cut 200 ev.compress
        modifyMind ctx code seat fun m =>
          { m with results := m.results ++ [s!"Refused: {what}. Why: {why}"] }
        let event := ((← findEntry ctx code).map (·.game.events)).getD 0
        seatNote ctx code <| Json.mkObj
          [("k", "refused"), ("seat", toJson seat), ("event", toJson event), ("action", ev), ("why", why)]
      | none =>
        if jStr ev "t" == some "propose" then
          modifyMind ctx code seat fun m =>
            { m with draftWords := "", draftResult := "", draftFormal := none }
    after := do
      let m ← getMind ctx code seat
      if let some words := m.pendingDraft then
        modifyMind ctx code seat fun x => { x with pendingDraft := none }
        runDraft ctx code seat words }

/-! ## After the game -/

/-- The questions after a game, in character. -/
def interviewMessage (g : Game) (s : State g.spec.G) (seat : Nat) (mind : Mind) : String :=
  let who := match s.winner with
    | some w => s!"{g.nameOf w} (seat {w}) won with {s.pointsOf w} points"
    | none => "nobody won"
  let majors := ((g.chronicle.toList.filter (·.major)).reverse.take 120).reverse.map (Clerk.oneLine ·.text)
  let notes := Clerk.fitNewest Clerk.maxMemoryChars (mind.notes.toList.map Clerk.oneLine)
  Clerk.neutralize s!"The game is over. {who}. You ended with {s.pointsOf seat} points, in round {s.round}.

<recent_events>
{"\n".intercalate majors}
</recent_events>

<your_memory>
{"\n".intercalate notes}
</your_memory>

Now step out of the game for a moment and tell the designers the truth, in your own voice. Be specific, and do not be polite about the game. Answer each field in one to three sentences:
- confusing: what confused you, and when.
- boring: what was boring or felt like a chore.
- great: what was actually good, if anything.
- could_not_say: a rule or a deal you wanted that the rule language could not express.
- best_moment: the best or most surprising moment of the game.
- farewell: one line to the table."

/-- Ask one seat what it thought of the game. This goes to the talk log, for spectators only. -/
def interview (ctx : Ctx) (code : String) (seat : Nat) : IO Unit := do
  modifyMind ctx code seat fun m => { m with interviewed := true }
  let some e ← findEntry ctx code | return
  let g := e.game
  let some s := g.state | return
  let some persona := (g.personas[seat]?).join | return
  let rulesFile ← try IO.FS.readFile (ctx.root / "Server" / "player_rules.md") catch _ => pure ""
  let rules := rulesFor rulesFile persona.styleOf.onScreenOnly ++ "\n\n" ++ gameFacts g.spec
  let mind ← getMind ctx code seat
  let body := requestBody ctx.seat ctx.seat.model rules (personaText persona seat)
    (interviewMessage g s seat mind) interviewSchema
  match ← request ctx code seat "interview" body with
  | .error why => seatNote ctx code (Json.mkObj [("k", "fallback"), ("seat", toJson seat), ("why", why)])
  | .ok answer =>
    match Json.parse answer.text with
    | .error _ => seatNote ctx code (Json.mkObj [("k", "fallback"), ("seat", toJson seat), ("why", "the interview did not read")])
    | .ok j =>
      let part (k label : String) : String := s!"{label}: {(jStr j k).getD "-"}"
      let text := " ".intercalate
        [part "confusing" "Confusing", part "boring" "Boring", part "great" "Great",
         part "could_not_say" "Could not say", part "best_moment" "Best moment", part "farewell" "Farewell"]
      seatNote ctx code (Json.mkObj [("k", "interview"), ("seat", toJson seat), ("answers", j)])
      let line : Talk.Line := { event := g.events, kind := "interview", by_ := seat, text }
      ctx.table.atomically do
        let tbl ← get
        let some e' := tbl.get? code | return
        discard <| e'.talkLog.append (Talk.lineJson line).compress
        set (tbl.insert code { e' with talk := e'.talk.push line })

end CharterServer.Seat
